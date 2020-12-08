open Hes
open Ast
open Ast.Logic
open Algorithm
open Z3
open Convert
open Smt
open Fptprover

let get_pvar_called_counts pvar_to_id funcs =
  let n = List.length funcs in
  let res = Array.make n 0 in
  funcs
  |> List.map HesLogic.let_function
  |> List.iter
    (fun (_, _, _, body) ->
       Hesutil.iter_app
         (fun pvar _ ->
            let pvar_id = pvar_to_id pvar in
            res.(pvar_id) <- res.(pvar_id) + 1
         ) body
    );
  res

(* 0: entry, n: n-th pvar from toplevel *)
let pvargraph_of_hes hes =
  let funcs, entry = HesLogic.let_hes hes in
  let pvar_to_id = Hashtbl.create 1234 in
  (* initialize pvar_to_id *)
  List.iteri (fun i func -> Hashtbl.add pvar_to_id (HesLogic.get_pvar_of_function func) (i+1)) funcs;
  entry :: (List.map (fun func -> HesLogic.get_body_of_function func) funcs)
  |> List.map
    (fun body ->
       Hesutil.get_next_funcs body
       |> List.map (fun nxt_pvar -> Hashtbl.find pvar_to_id nxt_pvar)
    )
  |> Array.of_list

let reachable_from starting_node_id graph =
  let n = Array.length graph in
  let res = Array.make n false in
  let queue = Queue.create () in
  res.(starting_node_id) <- true;
  Queue.push starting_node_id queue;
  while not (Queue.is_empty queue) do
    let node_id = Queue.pop queue in
    List.iter
      (fun nxt_node_id ->
         if not res.(nxt_node_id) then (
           res.(nxt_node_id) <- true;
           Queue.push nxt_node_id queue
         )
      ) graph.(node_id)
  done;
  res

module EraseUnreachedPredicates : sig
  val optimize: HesLogic.hes -> HesLogic.hes
end = struct
  let optimize hes =
    let graph = pvargraph_of_hes hes in
    let reachable = reachable_from 0 graph |> Array.to_list in
    let funcs, entry = HesLogic.let_hes hes in
    let funcs =
      Core.List.zip_exn funcs (List.tl reachable)
      |> List.filter Util.snd
      |> List.map Util.fst
    in
    HesLogic.mk_hes funcs entry
end


(*
  inline extension

  if a predicate P1 is called from only one predicate P2
  and depth(P1) > depth(P2)
  then P1 is eliminated by inline extension
*)

module InlineExtension : sig
  val optimize: HesLogic.hes -> HesLogic.hes
end = struct
  (* let update_called_counts_in_fml called_counts fml =
     if Formula.is_atom fml then
      let atom, _ = Formula.let_atom fml in
      update_called_counts_in_atom called_counts atom
     else if Formula.is_unop fml then
      let _, fml, _ = Formula.let_unop fml in
      update_called_counts_in_fml called_counts fml
     else if Formula.is_binop fml then
      let _, fml1, fml2, _ = Formula.let_binop fml in
      update_called_counts_in_fml called_counts fml1;
      update_called_counts_in_fml called_counts fml2
     else if Formula.is_bind fml then
      let _, fml, _ = Formula.let_bind fml in
      update_called_counts_in_fml called_counts fml
     else
      failwith @@ Printf.sprintf "InlineExtension.update_called_counts_in_fml: not implemented for: %s" (Convert.PrinterHum.str_of_formula fml) *)
  let optimize hes =
    let funcs_list, entry = HesLogic.let_hes hes in
    let n = List.length funcs_list in
    (* pvar -> depth *)
    let depth_ht = HesLogic.get_depth_ht hes in
    let pvar_to_id = (fun pvar -> Hashtbl.find depth_ht pvar) in
    let called_counts = get_pvar_called_counts pvar_to_id funcs_list in
    let expanded = Array.make n false in
    let funcs = Array.of_list funcs_list in
    List.rev funcs_list
    |> List.iteri
      (fun i func ->
         let func_id = n - i - 1 in
         let fix, pvar, args, body = HesLogic.let_function func in
         let body =
           Hesutil.replace_app
             (fun fml ->
                let atom, _ = Formula.let_atom fml in
                let pred, args, _ = Atom.let_app atom in
                let pvar, _ = Predicate.let_var pred in
                let func_id' = pvar_to_id pvar in
                if called_counts.(func_id') = 1 && func_id' > func_id then (
                  expanded.(func_id') <- true;
                  let _, pvar', args', body = HesLogic.let_function funcs.(func_id') in
                  assert (pvar = pvar');
                  let subst =
                    Core.List.zip_exn (List.map Util.fst args') args
                    |> Core.Map.Poly.of_alist_exn
                  in
                  Formula.subst subst body
                )
                else
                  fml
             )
             body
         in
         funcs.(func_id) <- HesLogic.mk_func fix pvar args body
      );
    let funcs =
      Array.to_list funcs
      |> List.filter (fun func -> let pvar = HesLogic.get_pvar_of_function func in not expanded.(pvar_to_id pvar))
    in
    HesLogic.mk_hes funcs entry
end

module EraseQuantifiers : sig
  val optimize: HesLogic.hes -> HesLogic.hes
end = struct
  let seed = 1007

  let is_equal_as_sets l1 l2 =
    List.sort compare l1 = List.sort compare l2
    
  (*
    AV(a+1) = {a}
    AV(a*2) = {}
    AV(a + a + b) = {b}
    AV(a + b + c) = {a, b, c}
    AV(1) = {}
  *)
  let rec adj_vars_of_term term =
    if Term.is_var term then
      (* AV(a) = {a} *)
      let tvar, _, _ = Term.let_var term in
      Core.Set.Poly.of_list [tvar]
    else if Term.is_funapp term then
      let funsym, args, _ = Term.let_funapp term in
      (*
        AV(a + b) = AV(a - b) = AV(a) + AV(b) - (AV(a) and AV(b))
        AV(a * b) = AV(a / b) = {}
        AV(-a) = AV(a)
      *)
      match funsym, args with
      | (T_int.Add, [a; b]) | (T_int.Sub, [a; b]) ->
        let av1 = adj_vars_of_term a in
        let av2 = adj_vars_of_term b in
        Core.Set.Poly.diff (Core.Set.Poly.union av1 av2) (Core.Set.Poly.inter av1 av2)
      | (T_int.Mult, [_; _]) | (T_int.Div, [_; _])
      | (T_int.Int _, []) ->
        Core.Set.Poly.empty
      | (T_int.UnaryNeg, [a]) ->
        adj_vars_of_term a
      | _ -> failwith @@ Printf.sprintf "unknown operation: %s" (Term.str_of term)
    else
      assert false

  let check_separatable avfvs =
    let avfvs = Array.of_list avfvs in
    (* multiset of fv1 U fv2 U ... U fvN *)
    let fv_count: (Ident.tvar, int) Hashtbl.t = Hashtbl.create seed in
    (* x in fv1 iff 1 in indexes_of_ftv[x] *)
    let indexes_of_ftv: (Ident.tvar, int) Hashtbl.t = Hashtbl.create seed in
    Array.iteri (fun idx (_, fv) ->
        Core.Set.Poly.to_list fv
        |> List.iter (fun tvar ->
            let current_count = match Hashtbl.find_opt fv_count tvar with None -> 0 | Some x -> x in
            Hashtbl.add fv_count tvar (current_count + 1);
            Hashtbl.add indexes_of_ftv tvar idx;
          )
      ) avfvs;
    let tvars = Hashtbl.to_seq_keys fv_count |> List.of_seq in
    let n = Array.length avfvs in
    let is_assigned = Array.make n false in
    let queue = Queue.create () in
    List.iter (fun tvar ->
        if Hashtbl.find fv_count tvar = 1 then
          Queue.push tvar queue
      ) tvars;
    while not (Queue.is_empty queue) do
      let tvar = Queue.pop queue in
      if Hashtbl.find fv_count tvar = 1 then
        List.iter (fun idx ->
            if not is_assigned.(idx) && Core.Set.Poly.mem (fst avfvs.(idx)) tvar then (
              is_assigned.(idx) <- true;
              snd avfvs.(idx)
              |> Core.Set.Poly.to_list
              |> List.iter (fun tvar' ->
                  let nxt_count = Hashtbl.find fv_count tvar' - 1 in
                  Hashtbl.add fv_count tvar' nxt_count;
                  if nxt_count = 1 then
                    Queue.push tvar' queue
                )
            )
          ) (Hashtbl.find_all indexes_of_ftv tvar);
    done;
    Array.for_all Util.id is_assigned

  (* let str_of_tvarset s =
     Core.Set.Poly.to_list s
     |> List.map Ident.name_of_tvar
     |> String.concat ", "
     |> Printf.sprintf "{%s}" *)

  let bound_flags_of_app_opt bounds args =
    (* let args = List.map Term.simplify args in *)
    let bounds = List.map Util.fst bounds |> Core.Set.Poly.of_list in
    let avs = List.map adj_vars_of_term args |> List.map (Core.Set.Poly.inter bounds) in
    let fvs = List.map Term.get_ftv args |> List.map (Core.Set.Poly.inter bounds) in
    let avfvs = Core.List.zip_exn avs fvs in
    (* Printf.printf "[%s]: %s\n"
       (List.map PrinterHum.str_of_term args |> String.concat "; ")
       (List.map (fun (av, fv) -> Printf.sprintf "(%s, %s)" (str_of_tvarset av) (str_of_tvarset fv)) avfvs |> String.concat " "); *)
    if List.exists (fun (av, fv) -> not (Core.Set.Poly.is_empty fv) && Core.Set.Poly.is_empty av) avfvs then
      (* if FV(t) and bounds != {} /\ AV(t) and bounds = {} for some arg t *)
      None
    else if check_separatable (List.filter (fun (_, fv) -> not (Core.Set.Poly.is_empty fv)) avfvs) then
      (*
        exists x, y. F x (x + y) -> exists x, y. F x y
        exists x, y. F (x + y) (x + y) -> exists x, y. F (x + y) (x + y)
      *)
      Some (List.map (fun av -> Core.Set.Poly.is_empty av |> not) avs)
    else
      None

  let create_initial_pvar_to_xpvar bounds pvar =
    let res = Hashtbl.create seed in
    Hashtbl.add res (List.map (fun _ -> false) bounds) pvar;
    res

  let flip_op = function Formula.And -> Formula.Or | Formula.Or -> Formula.And | _ -> assert false

  let let_if_opt fml =
    if not (SimpleFormula.is_branch fml) then
      None
    else
      let outer_op, fmls = SimpleFormula.let_branch fml in
      match fmls with
      | [fml1; fml2] ->
        let inner_op = flip_op outer_op in
        let get_formulas op fml =
          (* for fmls: atom *)
          if SimpleFormula.is_branch fml then
            let op', fmls = SimpleFormula.let_branch fml in
            if op' = op then fmls
            else [fml]
          else
            [fml]
        in
        let ht_of_formulas fmls =
          let ht = Hashtbl.create 1234 in
          List.iteri (fun i fml -> Hashtbl.add ht fml i) fmls;
          ht
        in
        let search_for_dual_formulas fmls ht =
          List.fold_left
            (fun res (fml, i) ->
               if Option.is_none res then
                 if SimpleFormula.get_fpv fml |> Core.Set.Poly.is_empty then (* TODO: to be more efficient *)
                   let fml = SimpleFormula.neg fml in
                   let fmls = get_formulas inner_op fml in
                   if List.for_all (Hashtbl.mem ht) fmls then
                     Some ([i], List.map (Hashtbl.find ht) fmls)
                   else
                     None
                 else
                   None
               else
                 res
            )
            None
            (Util.List.zip_index fmls)
        in
        let fmls1 = get_formulas inner_op fml1 in
        let fmls2 = get_formulas inner_op fml2 in
        let ht1 = ht_of_formulas fmls1 in
        let ht2 = ht_of_formulas fmls2 in
        let result =
          match search_for_dual_formulas fmls1 ht2 with
          | Some result -> Some result
          | None ->
            match search_for_dual_formulas fmls2 ht1 with
            | Some (pos2, pos1) -> Some (pos1, pos2)
            | None -> None
        in
        if Option.is_none result then
          None
        else
          let pos1, pos2 = Util.Option.unwrap result in
          let set_pos1 = Core.Set.Poly.of_list pos1 in
          let set_pos2 = Core.Set.Poly.of_list pos2 in
          let cond_fml =
            List.filter (fun (_, i) -> Core.Set.Poly.mem set_pos1 i) (Util.List.zip_index fmls1)
            |> List.map Util.fst
            |> SimpleFormula.mk_branch_with_simplification_one inner_op
          in
          (* TODO: O(nlogn) -> O(n) *)
          let fml1 = List.filter (fun (_, i) -> Core.Set.Poly.mem set_pos1 i |> not) (Util.List.zip_index fmls1) |> List.map Util.fst |> SimpleFormula.mk_branch_with_simplification_one inner_op in
          let fml2 = List.filter (fun (_, i) -> Core.Set.Poly.mem set_pos2 i |> not) (Util.List.zip_index fmls2) |> List.map Util.fst |> SimpleFormula.mk_branch_with_simplification_one inner_op in
          Some (outer_op, cond_fml, fml1, fml2)
      | _ -> None

  let let_if fml = match let_if_opt fml with Some res -> res | None -> assert false
  let is_from_if fml = match let_if_opt fml with Some _ -> true | None -> false

  let optimize hes =
    let funcs, entry = HesLogic.let_hes hes in
    let funcs = Array.of_list funcs in
    let pvar_to_func: (Ident.pvar, HesLogic.func) Hashtbl.t = Hashtbl.create seed in
    let pvar_to_nxtpvar: (Ident.pvar, Ident.pvar) Hashtbl.t = Hashtbl.create seed in
    let pvar_to_epvar: (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t = Hashtbl.create seed in
    let pvar_to_fpvar: (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t = Hashtbl.create seed in
    let endpvar = Ident.mk_fresh_pvar () in
    let startpvar =
      if Array.length funcs = 0 then
        endpvar
      else
        funcs.(0) |> HesLogic.get_pvar_of_function
    in
    let ht_of_binder = function Formula.Forall -> pvar_to_fpvar | Formula.Exists -> pvar_to_epvar in
    (* init pvar_to_func, pvar_to_nxtpvar, pvar_to_epvar, pvar_to_fpvar *)
    Array.iteri
      (fun i func ->
         let _, pvar, bounds, _ = HesLogic.let_function func in
         let nxtpvar =
           if i = Array.length funcs - 1 then
             endpvar
           else
             let pvar' = HesLogic.get_pvar_of_function funcs.(i+1) in
             pvar'
         in
         Hashtbl.add pvar_to_nxtpvar pvar nxtpvar;
         Hashtbl.add pvar_to_func pvar func;
         Hashtbl.add pvar_to_epvar pvar (create_initial_pvar_to_xpvar bounds pvar);
         Hashtbl.add pvar_to_fpvar pvar (create_initial_pvar_to_xpvar bounds pvar)
      )
      funcs;
    (* queue for erase_quantifiers_rep *)
    let queue = Queue.create () in
    (* add exists/forall func of [pvar] func and return the pvar of it *)
    let add_func binder bound_flags pvar =
      (* construct new function *)
      let func = Hashtbl.find pvar_to_func pvar in
      let fix, pvar, bounds, body = HesLogic.let_function func in
      let pvar' = Ident.mk_fresh_pvar () in (* TODO *)
      let bounds' =
        Core.List.zip_exn bounds bound_flags
        |> List.filter (fun (_, bf) -> not bf)
        |> List.map Util.fst
      in
      let qbounds =
        Core.List.zip_exn bounds bound_flags
        |> List.filter Util.snd
        |> List.map Util.fst
      in
      let body' = Formula.mk_bind_if_bounded binder qbounds body Dummy in
      let func = HesLogic.mk_func fix pvar' bounds' body' in
      (* update pvar_to_nxtpvar: insert the func just after [pvar] *)
      let nxtpvar = Hashtbl.find pvar_to_nxtpvar pvar in
      Hashtbl.add pvar_to_nxtpvar pvar pvar';
      Hashtbl.add pvar_to_nxtpvar pvar' nxtpvar;
      (* update pvar_to_func *)
      Hashtbl.add pvar_to_func pvar' func;
      (* update pvar_to_fpvar, pvar_to_epvar *)
      Hashtbl.add (Hashtbl.find (ht_of_binder binder) pvar) bound_flags pvar';
      Hashtbl.add (ht_of_binder binder) pvar' (Hashtbl.create seed);
      (* push to the queue for erase_quantifiers_rep *)
      Queue.push pvar' queue;
      (* return new pvar *)
      pvar'
    in
    let get_or_add_func binder bound_flags pvar =
      let ht = ht_of_binder binder in
      let ht' = Hashtbl.find ht pvar in
      if not (Hashtbl.mem ht' bound_flags) then
        (add_func binder bound_flags pvar: Ident.pvar) |> ignore;
      Hashtbl.find ht' bound_flags
    in
    let binder_of_op = function Formula.Forall -> Formula.And | Formula.Exists -> Formula.Or in
    (* erase quantifiers in [binder] [bounds]. [fml] *)
    let rec erase_quantifiers_rep_bind binder bounds fml =
      let ftv = SimpleFormula.get_ftv fml in
      let bounds = List.filter (fun (tvar, _) -> Core.Set.Poly.mem ftv tvar) bounds in
      if bounds = [] then
        erase_quantifiers_rep fml
      else if SimpleFormula.is_branch fml then
        (*
          exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b))
          exists a. P(a) /\ Q -> (exists a. P(a)) /\ Q
        *)
        let op, fmls = SimpleFormula.let_branch fml in
        if binder_of_op binder = op then
          (* exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b)) *)
          List.map (erase_quantifiers_rep_bind binder bounds) fmls
          |> SimpleFormula.mk_branch op
        else if is_from_if fml then
          (*
            forall x. (P /\ Q) \/ (not P /\ R)
            -> forall x. (P => Q) /\ (not P => R)
            -> (forall x. not P \/ Q) /\ (forall x. P \/ R)

            exists x. (P \/ Q) /\ (not P \/ R)
            -> exists x. (not P => Q) /\ (P => R)
            -> exists x. (not P /\ Q) \/ (P /\ R)
            -> (exists x. not P /\ Q) \/ (exists x. P /\ R)
          *)
          let op', cond_fml, fml1, fml2 = let_if fml in
          assert (op' = op);
          let fml1 =
            SimpleFormula.mk_branch_with_simplification_one op [SimpleFormula.neg cond_fml; fml1]
            |> erase_quantifiers_rep_bind binder bounds
          in
          let fml2 =
            SimpleFormula.mk_branch_with_simplification_one op [cond_fml; fml2]
            |> erase_quantifiers_rep_bind binder bounds
          in
          SimpleFormula.mk_branch_with_simplification_one (flip_op op) [fml1; fml2]
        else

          (*
            exists a. P(a) /\ Q
              -> (exists a. P(a)) /\ Q

            [exists a, b, c. P1(a, b) /\ P2(a) /\ P3(c)]
              -> [exists a, b, c. P1(a, b) /\ P2(a)] /\ [exists a, b, c. P3(c)]
              with UnionFind
          *)
          let bounds_tvar_set = List.map Util.fst bounds |> Core.Set.Poly.of_list in
          let ht = Hashtbl.create seed in
          List.iteri
            (fun i fml ->
               SimpleFormula.get_ftv fml
               |> Core.Set.Poly.iter
                 ~f:(fun tvar ->
                     if Core.Set.Poly.mem bounds_tvar_set tvar then
                       let ids =
                         match Hashtbl.find_opt ht tvar with
                         | Some ids -> ids
                         | None -> []
                       in
                       Hashtbl.add ht tvar (i :: ids)
                   )
            ) fmls;
          let n = List.length fmls in
          (* Printf.printf "%s\n\n" (List.map (SimpleFormulaUtil.string_of) fmls |> String.concat "\n"); *)
          assert (n >= 2); (* because of simplification *)
          (* construct uf *)
          let uf = UnionFind.mk_size_uf ~size:n in
          Hashtbl.iter
            (fun _ ids ->
               let ids = Array.of_list ids in
               Array.iteri
                 (fun i _ ->
                    if i+1 < Array.length ids then
                      UnionFind.unite ids.(i) ids.(i+1) uf
                 ) ids
            ) ht;
          (* reconstruct the branch *)
          let fmls = Array.of_list fmls in
          UnionFind.get_groups uf
          |> List.map
            (fun ids ->
               let fmls' = List.map (fun id -> fmls.(id)) ids in
               match fmls' with
               | [fml'] -> erase_quantifiers_rep_bind binder bounds fml'
               (* try let_if *)
               | [_; _] ->
                 (* TODO *)
                 let fml' = SimpleFormula.mk_branch_with_simplification_one op fmls' in
                 if is_from_if fml' then erase_quantifiers_rep_bind binder bounds fml'
                 else
                   List.map erase_quantifiers_rep fmls'
                   |> SimpleFormula.mk_branch_with_simplification_one op
                   |> SimpleFormula.mk_bind_with_filter binder bounds
               | _ -> (* List.length fmls >= 2 *)
                 List.map erase_quantifiers_rep fmls'
                 |> SimpleFormula.mk_branch_with_simplification_one op
                 |> SimpleFormula.mk_bind_with_filter binder bounds
            )
          |> SimpleFormula.mk_branch_with_simplification_one op
      else if SimpleFormula.is_bind fml then
        let binder', bounds', fml' = SimpleFormula.let_bind fml in
        (* forall x. forall y. P -> forall x, y. P *)
        if binder = binder' then (
          (* bounds, bounds' must be distinct *)
          let new_bounds = bounds @ bounds' in
          (* update_bounds sometimes changes the order of elements of its arguments *)
          assert (is_equal_as_sets (SimpleFormula.update_bounds bounds bounds') new_bounds);
          erase_quantifiers_rep_bind binder new_bounds fml'
        )
        else
          (*
            forall x. exists y. P
            1. process [exists y. P]
            2. if it's still of the form [forall x. exists y. P] then give up erasing (to avoid an infinite-loop)
            3. otherwise, continue to process erase_quantifiers_rep_bind
          *)
          let fml = erase_quantifiers_rep_bind binder' bounds' fml' in
          if SimpleFormula.is_bind fml then
            let binder', _, _ = SimpleFormula.let_bind fml in
            if binder != binder' then
              SimpleFormula.mk_bind_with_filter binder bounds fml
            else
              erase_quantifiers_rep_bind binder bounds fml
          else
            erase_quantifiers_rep_bind binder bounds fml
      else if SimpleFormula.is_app fml then
        let pvar, args = SimpleFormula.let_app fml in
        match bound_flags_of_app_opt bounds args with
        | Some bound_flags ->
          let pvar' = get_or_add_func binder bound_flags pvar in
          let args =
            Core.List.zip_exn args bound_flags
            |> List.filter (fun (_, bf) -> not bf)
            |> List.map Util.fst
          in
          SimpleFormula.mk_app pvar' args
        | None -> SimpleFormula.mk_bind_with_filter binder bounds fml
      else if SimpleFormula.is_cond fml then
        SimpleFormula.mk_bind_with_filter binder bounds fml
      else
        assert false
    and erase_quantifiers_rep fml =
      if SimpleFormula.is_and fml then
        SimpleFormula.let_and fml
        |> List.map erase_quantifiers_rep
        |> SimpleFormula.mk_and
      else if SimpleFormula.is_or fml then
        SimpleFormula.let_or fml
        |> List.map erase_quantifiers_rep
        |> SimpleFormula.mk_or
      else if SimpleFormula.is_bind fml then
        let binder, bounds, fml = SimpleFormula.let_bind fml in
        erase_quantifiers_rep_bind binder bounds fml
      else if SimpleFormula.is_atom fml then
        fml
      else
        assert false
    in
    let erase_quantifiers fml =
      let fml = SimpleFormula.of_formula fml in
      (* Printf.printf "%s\n\n" (SimpleFormulaUtil.string_of fml); *)
      erase_quantifiers_rep fml
      |> SimpleFormula.formula_of
    in
    (* init queue *)
    Array.iter
      (fun func ->
         let pvar = HesLogic.get_pvar_of_function func in
         Queue.push pvar queue
      ) funcs;
    let entry = erase_quantifiers entry in
    while not (Queue.is_empty queue) do
      let pvar = Queue.pop queue in
      let fix, pvar_confirm, bounds, body = Hashtbl.find pvar_to_func pvar |> HesLogic.let_function in
      assert (pvar = pvar_confirm);
      (* Printf.printf "%s: " (Ident.name_of_pvar pvar); *)
      let body = erase_quantifiers body in
      let func = HesLogic.mk_func fix pvar bounds body in
      Hashtbl.add pvar_to_func pvar func
    done;
    (* reconstruct funcs from startpvar, endpvar, pvar_to_nxtpvar, pvar_to_func, processed_pvars(reached) *)
    let funcs_queue = Queue.create () in
    let current_pvar = ref startpvar in
    while !current_pvar != endpvar do
      let func = Hashtbl.find pvar_to_func !current_pvar in
      Queue.push func funcs_queue;
      current_pvar := Hashtbl.find pvar_to_nxtpvar !current_pvar
    done;
    let funcs = Queue.to_seq funcs_queue |> List.of_seq in
    HesLogic.mk_hes funcs entry
end

(* exists x. 0 <= x /\ x <= 100 -> true *)
module CheckAndReplaceToTopOrBot : sig
  val optimize: is_print_for_debug:bool -> HesLogic.hes -> HesLogic.hes
end = struct
  let bind_free_tvas_with_forall fml =
    let ftv = Formula.get_ftv fml in
    let bounds =
      Core.Set.Poly.to_list ftv
      |> List.map (fun tvar -> tvar, T_int.SInt) (* TODO *)
    in
    Formula.mk_forall_if_bounded bounds fml Dummy

  let gen_smt_solver timeout_milliseconds =
    let options = ["timeout", string_of_int timeout_milliseconds] in
    let ctx = mk_context options in
    let solver = Solver.mk_simple_solver ctx in
    solver, ctx

  let check_always_true ?(timeout_milliseconds=1000) ~is_print_for_debug fml =
    let fpv = Formula.get_fpv fml in
    if not (Core.Set.Poly.is_empty fpv) then
      false
    else (
      if is_print_for_debug then (
        Debug.print @@ Printf.sprintf "";
        Debug.print @@ Printf.sprintf "[optimize][check_always_true]";
        Debug.print @@ Printf.sprintf "input: %s" (PrinterHum.str_of_formula fml);
      );
      (* x >= 10 -> forall (x: int). x >= 10 *)
      let fml = bind_free_tvas_with_forall fml in
      (* to smt format and solve it with z3 *)
      let solver, ctx = gen_smt_solver timeout_milliseconds in
      let expr = Z3interface.of_formula ctx Env.empty Env.empty fml in
      if is_print_for_debug then
        Debug.print @@ Printf.sprintf "expr: %s" (Expr.to_string expr);
      try let z3result = Solver.check solver [expr] in
        if is_print_for_debug then
          (Debug.print @@ Printf.sprintf "Z3: %s" (Solver.string_of_status z3result);
           Debug.print @@ "");
        match z3result with
        | Solver.SATISFIABLE -> true
        | _ -> false
      with
      | Z3.Error reason ->
        if is_print_for_debug then
          (Debug.print @@ Printf.sprintf "Z3: %s" reason;
           Debug.print @@ "");
        (* timeout *)
        if is_print_for_debug then
          Debug.print @@ Printf.sprintf "Z3 Error: %s" reason;
        flush stderr;
        false
    )

  let rec replace_to_topbot ~is_print_for_debug fml =
    if Formula.is_binop fml then
      let binop, fml1, fml2, info = Formula.let_binop fml in
      let fml1 = replace_to_topbot ~is_print_for_debug fml1 in
      let fml2 = replace_to_topbot ~is_print_for_debug fml2 in
      Formula.mk_binop binop fml1 fml2 info
    else if Formula.is_unop fml then
      let unop, fml, info = Formula.let_unop fml in
      let fml = replace_to_topbot ~is_print_for_debug fml in
      Formula.mk_unop unop fml info
    else if Formula.is_atom fml then
      fml
    else if Formula.is_bind fml then
      if check_always_true ~is_print_for_debug fml then
        Formula.mk_atom (Atom.mk_true Dummy) Dummy
      else if check_always_true ~is_print_for_debug (Formula.simplify_neg fml) then
        Formula.mk_atom (Atom.mk_false Dummy) Dummy
      else
        let binder, bounds, fml, info = Formula.let_bind fml in
        let fml = replace_to_topbot ~is_print_for_debug fml in
        Formula.mk_bind binder bounds fml info
    else
      assert false

  let optimize ~is_print_for_debug hes =
    let funcs, entry = HesLogic.let_hes hes in
    let entry = replace_to_topbot ~is_print_for_debug entry in
    let funcs =
      List.map
        (fun func ->
           let fix, pvar, args, body = HesLogic.let_function func in
           let body = replace_to_topbot ~is_print_for_debug body in
           HesLogic.mk_func fix pvar args body
        )
        funcs
    in
    HesLogic.mk_hes funcs entry
end

module EraseConstVariables : sig
  val optimize: HesLogic.hes -> HesLogic.hes
end = struct
  type vartype =
    | UnReached
    | Const of Bigint.t
    | NonConst

  let merge_vt vt1 vt2 =
    match (vt1, vt2) with
    | (UnReached, vt) | (vt, UnReached) -> vt
    | (NonConst, _) | (_, NonConst) -> NonConst
    | (Const x, Const y) ->
      if x = y then
        Const x
      else
        NonConst

  let is_const = function
    | Const _ -> true
    | _ -> false

  (* let string_of_vt = function
     | UnReached -> "unreached"
     | NonConst -> "nonconst"
     | Const x -> Printf.sprintf "const %s" (Bigint.to_string x) *)

  let seed = 1007

  let vt_of_pt ht_vt (pvar, tvar) =
    Hashtbl.find (Hashtbl.find ht_vt pvar) tvar

  let init_ht_vt hes =
    let funcs = HesLogic.get_functions hes in
    let ht_vt: (Ident.pvar, (Ident.tvar, vartype) Hashtbl.t) Hashtbl.t = Hashtbl.create seed in
    List.iter
      (fun func ->
         let _, pvar, bounds, _ = HesLogic.let_function func in
         let ht = Hashtbl.create seed in
         List.iter (fun (tvar, _) -> Hashtbl.add ht tvar UnReached) bounds;
         Hashtbl.add ht_vt pvar ht
      ) funcs;
    ht_vt

  let rec nonconst_update ht_vt graph pt =
    let pvar, tvar = pt in
    Hashtbl.add (Hashtbl.find ht_vt pvar) tvar NonConst;
    Hashtbl.find graph pt
    |> List.iter
      (fun (nxt_pvar, nxt_tvar, _) ->
         let nxt_pt = (nxt_pvar, nxt_tvar) in
         let env = Hashtbl.find ht_vt nxt_pvar in
         if Hashtbl.find env nxt_tvar != NonConst then (
           nonconst_update ht_vt graph nxt_pt
         )
      )

  let rec vt_of_term env term =
    if Term.is_var term then
      let tvar, _, _ = Term.let_var term in
      if Hashtbl.mem env tvar then
        Hashtbl.find env tvar
      else
        NonConst
    else if Term.is_funapp term then
      let funsym, args, _ = Term.let_funapp term in
      let arg_vts = List.map (vt_of_term env) args in
      if List.exists (fun vt -> vt = NonConst) arg_vts then
        NonConst
      else if List.exists (fun vt -> vt = UnReached) arg_vts then
        UnReached
      else
        match funsym, arg_vts with
        | (T_int.Int x, []) -> Const x
        | (T_int.Add, [Const x; Const y]) -> Const (Bigint.(+) x y)
        | (T_int.Sub, [Const x; Const y]) -> Const (Bigint.(-) x y)
        | (T_int.Mult, [Const x; Const y]) -> Const (Bigint.( * ) x y)
        | _ -> failwith "EraseConstVariables.vt_of_term: illegal funapp"
    else
      assert false

  let value_of_const_term term =
    let dummy_ht = Hashtbl.create seed in
    match vt_of_term dummy_ht term with
    | Const x -> x
    | _ -> assert false

  let rec get_vargraph_rep (tvars_of_pvar: Ident.pvar -> Ident.tvar list) (pvar: Ident.pvar) arg_tvars consts nonconsts graph fml =
    if Formula.is_unop fml then
      let _, fml, _ = Formula.let_unop fml in
      get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml
    else if Formula.is_binop fml then
      let _, fml1, fml2, _ = Formula.let_binop fml in
      let consts, nonconsts = get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml1 in
      get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml2
    else if Formula.is_atom fml then
      let atom, _ = Formula.let_atom fml in
      if Atom.is_varapp atom then
        let pvar', args, _ = Atom.let_varapp atom in
        let tvars = tvars_of_pvar pvar' in
        Core.List.zip_exn args tvars
        |> List.fold_left
          (fun (consts, nonconsts) (arg, tvar') ->
             let ftv = Term.get_ftv arg in
             if Core.Set.Poly.is_empty ftv then
               let value = value_of_const_term arg in
               (pvar', tvar', value) :: consts, nonconsts
             else if Core.Set.Poly.diff ftv arg_tvars |> Core.Set.Poly.is_empty then (
               Core.Set.Poly.inter ftv arg_tvars
               |> Core.Set.Poly.to_list
               |> List.iter (fun tvar ->
                   let pt = (pvar, tvar) in
                   let edges = Hashtbl.find graph pt in
                   Hashtbl.add graph pt ((pvar', tvar', arg) :: edges));
               consts, nonconsts
             )
             else
               consts, (pvar', tvar') :: nonconsts
          )
          (consts, nonconsts)
      else
        consts, nonconsts
    else if Formula.is_bind fml then
      let _, bounds, fml, _ = Formula.let_bind fml in
      let bound_tvars = List.map Util.fst bounds |> Core.Set.Poly.of_list in
      let arg_tvars = Core.Set.Poly.diff arg_tvars bound_tvars in
      get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph fml
    else
      assert false

  let tvars_of_pvar_of_hes hes =
    let funcs, _ = HesLogic.let_hes hes in
    let tvars_of_pvar_ht = Hashtbl.create seed in
    List.iter
      (fun func ->
         let _, pvar, bounds, _ = HesLogic.let_function func in
         let tvars = List.map Util.fst bounds in
         Hashtbl.add tvars_of_pvar_ht pvar tvars
      )
      funcs;
    fun pvar -> Hashtbl.find tvars_of_pvar_ht pvar

  let get_vargraph hes =
    let funcs, entry = HesLogic.let_hes hes in
    let dummy_pvar = Ident.Pvar "dummy" in
    let consts: (Ident.pvar * Ident.tvar * Bigint.t) list = [] in
    let nonconsts: (Ident.pvar * Ident.tvar) list = [] in
    let graph: (Ident.pvar * Ident.tvar, (Ident.pvar * Ident.tvar * Term.t) list) Hashtbl.t = Hashtbl.create seed in
    let tvars_of_pvar = tvars_of_pvar_of_hes hes in
    List.iter
      (fun pvar ->
         List.iter
           (fun tvar -> Hashtbl.add graph (pvar, tvar) [])
           (tvars_of_pvar pvar);
      )
      (HesLogic.get_pvars_of_functions funcs);
    let consts, nonconsts =
      List.fold_left
        (fun (consts, nonconsts) func ->
           let _, pvar, bounds, body = HesLogic.let_function func in
           let arg_tvars = List.map Util.fst bounds |> Core.Set.Poly.of_list in
           get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph body
        )
        (get_vargraph_rep tvars_of_pvar dummy_pvar Core.Set.Poly.empty consts nonconsts graph entry)
        funcs
    in
    consts, nonconsts, graph

  let gen_ht_vt hes =
    let ht_vt = init_ht_vt hes in
    let consts, nonconsts, graph = get_vargraph hes in
    (* Printf.printf "nonconsts: %s\n" (List.map (fun (pvar, tvar) -> Printf.sprintf "(%s, %s)" (Ident.name_of_pvar pvar) (Ident.name_of_tvar tvar)) nonconsts |> String.concat " "); *)
    List.iter (fun pt -> nonconst_update ht_vt graph pt) nonconsts;
    let queue = Queue.create () in
    let update_ht_vt pt value =
      let current_vt = vt_of_pt ht_vt pt in
      if current_vt <> NonConst then
        let new_vt = merge_vt current_vt (Const value) in
        if new_vt <> current_vt then (
          let pvar, tvar = pt in
          Hashtbl.add (Hashtbl.find ht_vt pvar) tvar new_vt;
          if new_vt = NonConst then
            nonconst_update ht_vt graph pt
          else
            Queue.push pt queue
        )
    in
    List.iter (fun (pvar, tvar, value) -> update_ht_vt (pvar, tvar) value) consts;
    while not (Queue.is_empty queue) do
      let pt = Queue.pop queue in
      let pvar, _ = pt in
      (* Printf.printf "%s, %s: %s\n" (Ident.name_of_pvar pvar) (Ident.name_of_tvar tvar) (string_of_vt (vt_of_pt ht_vt pt)); flush stdout; *)
      if (vt_of_pt ht_vt pt) <> NonConst then
        Hashtbl.find graph pt
        |> List.iter
          (fun (nxt_pvar, nxt_tvar, term) ->
             let nxt_pt = (nxt_pvar, nxt_tvar) in
             let current_vt = vt_of_pt ht_vt nxt_pt in
             if current_vt <> NonConst then
               let env = Hashtbl.find ht_vt pvar in
               (* it's ok *)
               let vt = vt_of_term env term in
               match vt with
               | NonConst -> nonconst_update ht_vt graph nxt_pt
               | Const value -> update_ht_vt nxt_pt value
               | UnReached -> ()
          );
    done;
    ht_vt

  let filter_nonconst_args tvars_of_pvar ht_vt fml =
    Hesutil.replace_app
      (fun fml ->
         let atom, info = Formula.let_atom fml in
         let pvar, args, info' = Atom.let_varapp atom in
         let ht_vt_of_tvar = Hashtbl.find ht_vt pvar in
         let tvars = tvars_of_pvar pvar in
         let args =
           Core.List.zip_exn args tvars
           |> List.filter
             (fun (_, tvar) -> Hashtbl.find ht_vt_of_tvar tvar |> is_const |> not)
           |> List.map Util.fst
         in
         Formula.mk_atom (Atom.mk_varapp pvar args info') info
      )
      fml

  let optimize hes =
    (* Printf.printf "[ReplaceConstVariables]\n";
       Printf.printf "Input: %s\n\n" (Hesutil.str_of_hes hes); *)
    let ht_vt = gen_ht_vt hes in
    let funcs, entry = HesLogic.let_hes hes in
    let tvars_of_pvar = tvars_of_pvar_of_hes hes in
    let entry = filter_nonconst_args tvars_of_pvar ht_vt entry in
    let funcs =
      List.map
        (fun func ->
           let fix, pvar, bounds, fml = HesLogic.let_function func in
           let ht_vt_of_tvar = Hashtbl.find ht_vt pvar in
           let subst =
             List.fold_left
               (fun subst (tvar, _) ->
                  match Hashtbl.find ht_vt_of_tvar tvar with
                  | Const x -> Core.Map.Poly.add_exn subst ~key:tvar ~data:(T_int.mk_int x Dummy)
                  | _ -> subst
               )
               Core.Map.Poly.empty
               bounds
           in
           let fml =
             Formula.subst subst fml
             |> filter_nonconst_args tvars_of_pvar ht_vt
           in
           let bounds =
             List.filter (fun (tvar, _) -> Hashtbl.find ht_vt_of_tvar tvar |> is_const |> not) bounds
           in
           HesLogic.mk_func fix pvar bounds fml
        )
        funcs
    in
    HesLogic.mk_hes funcs entry
end

let optimize_formula hes =
  let funcs, entry = HesLogic.let_hes hes in
  let funcs =
    List.map
      (fun func ->
         let fix, pvar, bounds, body = HesLogic.let_function func in
         let body = FormulaOptimizer.optimize body in
         HesLogic.mk_func fix pvar bounds body)
      funcs
  in
  let entry = FormulaOptimizer.optimize entry in
  HesLogic.mk_hes funcs entry

let optimize ?(is_print_for_debug=true) hes =
  hes
  |> optimize_formula
  |> InlineExtension.optimize
  |> EraseQuantifiers.optimize
  |> EraseUnreachedPredicates.optimize
  |> EraseConstVariables.optimize
  |> CheckAndReplaceToTopOrBot.optimize ~is_print_for_debug
  |> Hesutil.simplify
  |> InlineExtension.optimize
