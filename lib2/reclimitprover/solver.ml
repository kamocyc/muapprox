open Ast
open Logic
open Convert
open Fptprover
open Hes

(* let merge_pvars pvars1 pvars2 =
   List.sort_uniq Ident.pvar_compare
   @@ List.merge Ident.pvar_compare pvars1 pvars2

   let rec intersect_pvars pvars1 pvars2 =
   match pvars1, pvars2 with
   | [], _ | _, [] -> []
   | pvar1 :: pvars1, pvar2 :: pvars2 ->
    if Ident.pvar_compare pvar1 pvar2 < 0 then
      intersect_pvars pvars1 (pvar2 :: pvars2)
    else if Ident.pvar_compare pvar1 pvar2 > 0 then
      intersect_pvars (pvar1 :: pvars1) pvars2
    else
      pvar1 :: intersect_pvars pvars1 pvars2 *)

let rectvar_prefix = "#rec_"
let rectvar_of_pvar pvar = Ident.Tvar (rectvar_prefix ^ (Ident.name_of_pvar pvar))
let is_rectvar tvar =
  let varname = Ident.name_of_tvar tvar in
  String.length varname >= String.length rectvar_prefix
  && String.sub varname 0 (String.length rectvar_prefix) = rectvar_prefix

(* [-coe * a - coe * b + coe; -coe * a + coe * b + coe; coe * a - coe * b + coe; coe * a + coe * b + coe] *)
let rec get_guessed_terms_rep coe arg_terms term res = match arg_terms with
  | [] -> res
  | arg_term :: tail ->
      let pterm = T_int.mk_add term (T_int.mk_mult (T_int.mk_from_int coe Dummy) arg_term Dummy) Dummy in
      let nterm = T_int.mk_add term (T_int.mk_mult (T_int.mk_from_int (-coe) Dummy) arg_term Dummy) Dummy in
(*
    let pterm = (T_int.mk_mult (T_int.mk_from_int coe Dummy) arg_term Dummy) in
    let nterm = (T_int.mk_mult (T_int.mk_from_int (-coe) Dummy) arg_term Dummy) in
 *)
    if Term.is_var arg_term && (Term.let_var arg_term |> (fun (tvar, _, _) -> is_rectvar tvar)) then
      get_guessed_terms_rep coe tail term res
    else if T_int.is_int arg_term then
      let arg_int = T_int.let_int arg_term in
      if Bigint.(arg_int = zero) then
        get_guessed_terms_rep coe tail term res
      else
         get_guessed_terms_rep coe tail term (pterm::nterm::res)
    else
         get_guessed_terms_rep coe tail term (pterm::nterm::res)
(*    
  | [] -> term :: res
  | arg_term :: tail ->
    let normal_case () =
      let pterm = T_int.mk_add term (T_int.mk_mult (T_int.mk_from_int coe Dummy) arg_term Dummy) Dummy in
      let nterm = T_int.mk_add term (T_int.mk_mult (T_int.mk_from_int (-coe) Dummy) arg_term Dummy) Dummy in
      get_guessed_terms_rep coe tail pterm
      @@ get_guessed_terms_rep coe tail nterm res
    in
    (* skip if arg_term = 0 *)
    if Term.is_var arg_term && (Term.let_var arg_term |> (fun (tvar, _, _) -> is_rectvar tvar)) then
      get_guessed_terms_rep coe tail term res
    else if T_int.is_int arg_term then
      let arg_int = T_int.let_int arg_term in
      if Bigint.(arg_int = zero) then
        get_guessed_terms_rep coe tail term res
      else
        normal_case ()
    else
      normal_case ()
 *)

let get_guessed_terms coe1 coe2 arg_terms =
  let const_term = T_int.mk_int coe2 Dummy in
  let res = get_guessed_terms_rep coe1 arg_terms const_term [const_term] in
(*
  if res = [] then
    [const_term]
  else
 *)
    res

let replace_app coe1 coe2 outer_mu_funcs current_terms_of_pvars fml =
  Hesutil.replace_app
    (fun fml_app ->
       let atom, info = Formula.let_atom fml_app in
       let pred, args, info' = Atom.let_app atom in
       let pvar, arg_sorts = Predicate.let_var pred in
       let arg_pvars = Env.lookup pvar outer_mu_funcs in
       let arg_sorts' = List.map (fun _ -> T_int.SInt) arg_pvars in
       let pred = Predicate.mk_var pvar (arg_sorts' @ arg_sorts) in
       let make_args env_guessed env =
         List.map
           (fun pvar' ->
              try let term = Env.lookup pvar' env in
                if pvar' = pvar then
                  T_int.mk_sub term (T_int.one Dummy) Dummy
                else
                  term
              with
                Not_found -> Env.lookup pvar' env_guessed
           ) arg_pvars
       in
       (* S_j - S_i *)
       let new_pvars = List.filter (fun pvar -> not @@ Env.has pvar current_terms_of_pvars) arg_pvars in
       if new_pvars = [] then
         Formula.mk_atom
           (Atom.mk_app pred (make_args Env.empty current_terms_of_pvars @ args) info')
           info
       else
         let new_tvars = List.map rectvar_of_pvar new_pvars in
         let new_terms = List.map (fun tvar -> Term.mk_var tvar T_int.SInt Dummy) new_tvars in
         let guessed_terms = get_guessed_terms coe1 coe2 args in
         let havocs = Formula.and_of
             (* [a1; a2], [b1; b2] -> [a1 >= b1; a1 >= b2; a2 >= b1; a2 >= b2] *)
             (List.map
                (fun (term1, term2) -> Formula.mk_atom (T_int.mk_geq term1 term2 Dummy) Dummy)
                (Core.List.cartesian_product new_terms guessed_terms))
             Dummy
         in
         let args = make_args (Env.update (Core.List.zip_exn new_pvars new_terms) Env.empty) current_terms_of_pvars @ args in
         Formula.mk_forall
           (List.map (fun tvar -> (tvar, T_int.SInt)) new_tvars)
           (Formula.mk_imply
              havocs
              (Formula.mk_atom
                 (Atom.mk_app pred args info')
                 info)
              Dummy)
           Dummy
    )
    fml

let get_outer_mu_funcs funcs =
  let funcs_count = List.length funcs in
  (* construct a table *)
  let pvar_to_nid = Hashtbl.create funcs_count in
  let dummy_pvar = Ident.Pvar "" in
  let is_mu = Array.init funcs_count (fun _ -> false) in
  let nid_to_pvar = Array.init funcs_count (fun _ -> dummy_pvar) in
  List.iteri
    (fun nid (fix, pvar, _, _) ->
       Hashtbl.add pvar_to_nid pvar nid;
       nid_to_pvar.(nid) <- pvar;
       is_mu.(nid) <- fix = Predicate.Mu
    )
    funcs;
  (* make a graph *)
  let g = Graph.init funcs_count in
  List.iter
    (fun (_, pvar, _, body) ->
       let nid = Hashtbl.find pvar_to_nid pvar in
       Hesutil.get_next_funcs body
       |> List.iter
         (fun pvar' ->
            try
              let to_nid = Hashtbl.find pvar_to_nid pvar' in
              Graph.add_edge nid to_nid g
            with
              Not_found ->
              failwith @@ Printf.sprintf "Predicate %s is not found in hes graph" (Ident.name_of_pvar pvar')
         )
    )
    funcs;
  (* make a rev graph *)
  let rg = Graph.reverse_edges g in
  (* get nid list s.t. a ->* b /\ b *<- a through only min(a, b) nodes *)
  let outer_nids = Graph.init funcs_count in
  for i = 0 to funcs_count - 1 do
    let nids1 = Graph.reachable_nodes_from ~start_is_reachable_initially:false i g in
    let nids2 = Graph.reachable_nodes_from ~start_is_reachable_initially:false i rg in
    Core.Set.Poly.inter
      (Core.Set.Poly.of_list nids1)
      (Core.Set.Poly.of_list nids2)
    |> Core.Set.Poly.to_list
    |> List.iter
      (fun nid ->
         Graph.add_edge nid i outer_nids
      );
    Graph.reset_node i g;
    Graph.reset_node i rg
  done;
  (* filter by fixpoints *)
  let res =
    List.map
      (fun (_, pvar, _, _) ->
         let nid = Hashtbl.find pvar_to_nid pvar in
         pvar,
         Graph.get_next_nids nid outer_nids
         |> List.filter
           (fun to_nid -> is_mu.(to_nid))
         |> List.map
           (fun to_nid ->
              nid_to_pvar.(to_nid)
           )
      )
      funcs
  in
  (* List.map (fun (pvar, pvars) -> Printf.sprintf "%s: %s" (Ident.name_of_pvar pvar) (List.map Ident.name_of_pvar pvars |> String.concat ", ")) res
     |> String.concat "\n"
     |> print_endline; *)
  Env.update res Env.empty

let elim_mu_with_rec hes coe1 coe2 =
  let funcs = HesLogic.get_functions hes in
  (* calc outer_mu_funcs *)
  let outer_mu_funcs = get_outer_mu_funcs funcs in
  (* make tvars *)
  let rec_tvars =
    List.fold_left
      (fun env (fix, pvar, _, _) ->
         if fix = Predicate.Mu then
           Env.update [pvar, rectvar_of_pvar pvar] env
         else
           env
      )
      Env.empty
      funcs
  in
  (* make new hes *)
  let funcs = List.map
      (fun (_, mypvar, bounds, body) ->
         let outer_pvars = Env.lookup mypvar outer_mu_funcs in
         let env = Env.update
             (List.map
                (fun pvar ->
                   (pvar, Term.mk_var (Env.lookup pvar rec_tvars) T_int.SInt Dummy))
                outer_pvars)
             Env.empty
         in
         let body = replace_app coe1 coe2 outer_mu_funcs env body in
         (* add rec > 0 if need *)
         let body = if Env.has mypvar env then
             let mytvar = Env.lookup mypvar env in
             Formula.mk_and
               (Formula.mk_atom
                  (T_int.mk_gt mytvar (T_int.zero Dummy) Dummy)
                  Dummy
               )
               body
               Dummy
           else
             body
         in
         let bounds' = List.map (fun pvar -> Env.lookup pvar rec_tvars, T_int.SInt) outer_pvars in
         (Predicate.Nu, mypvar, bounds' @ bounds, body)
      )
      funcs
  in
  let entry = FormulaConverter.elim_fv_with_forall
    @@ replace_app coe1 coe2 outer_mu_funcs []
    @@ HesLogic.get_entrypoint hes in
  HesLogic.mk_hes funcs entry

(*  
let flip_solver solver =
  fun timeout is_print_for_debug ->
  let status, original_status = solver timeout is_print_for_debug in
  Status.flip status, original_status
  
let rec run_solvers timeout is_print_chc = function
  | [] -> Status.Unknown
  | solvers ->
    let rec rep next_solvers = function
      | [] ->
        let next_timeout =
          timeout * 2
          (* if List.length next_solvers = 1 then 0 else timeout * 2 *)
        in
        run_solvers next_timeout false (List.rev next_solvers)
      | (solver, title, is_print) :: tail ->
        let is_print_chc = is_print_chc && is_print in
        if is_print_chc then
          (Debug.print "======================================";
           Debug.print ("CHC of " ^ title);
           Debug.print "======================================");
        if !Global.config.verbose then
          (Printf.printf "Solving %s %s..." title
           @@ if timeout = 0 then "without timeout" else Printf.sprintf "with timeout %d sec" timeout;
           if is_print_chc then
             Printf.printf "\n";
           flush stdout);
        try
          let status, original_status = solver timeout is_print_chc in
          if not is_print_chc && !Global.config.verbose then
            (Printf.printf " %s (<= %s)\n" (Status.string_of status) (Status.string_of original_status); flush stdout);
          if status = Status.Unknown then
            rep next_solvers tail
          else
            status
        with Status.Timeout ->
          if not is_print_chc && !Global.config.verbose then
            (Printf.printf " timeout\n"; flush stdout);
          rep ((solver, title, is_print) :: next_solvers) tail
    in
    rep [] solvers
*)

let get_mu_elimed_solver coe1 coe2 is_print_for_debug hes =
  if is_print_for_debug then
    (Debug.print @@ Printf.sprintf "vvvvvvvvvvvvvvvvvv Original Hes vvvvvvvvvvvvvvvvvv\n";
     Debug.print @@ Hesutil.str_of_hes hes;
     Debug.print "");
  let hes = Hesutil.encode_body_exists coe1 ~range:coe2 @@ Hesutil.encode_top_exists coe1 ~range:coe2 hes in
  if is_print_for_debug then
    (Debug.print @@ Printf.sprintf "vvvvvvvvvvvvvvvvvv Encoded Hes vvvvvvvvvvvvvvvvvv\n";
     Debug.print @@ Hesutil.str_of_hes hes;
     Debug.print "");
  let hes = elim_mu_with_rec hes coe1 (Bigint.of_int coe2) in
  if is_print_for_debug then
    (Debug.print @@ Printf.sprintf "vvvvvvvvvvvvv Eliminate Mu (coe: %d, %d) vvvvvvvvvvvvv\n" coe1 coe2;
     Debug.print @@ Hesutil.str_of_hes hes;
     Debug.print "");
  let hes = Hesutil.simplify hes in
  if is_print_for_debug then
    (Debug.print "vvvvvvvvvvvvvvv Simplify vvvvvvvvvvvvvvv\n";
     Debug.print @@ Hesutil.str_of_hes hes;
     Debug.print "");
  fun timeout is_print_for_debug ->
    let result, _ = Rfunprover.Solver.solve_onlynu_onlyforall false timeout is_print_for_debug hes in
    match result with
    | Status.Valid -> Status.Valid, Status.Valid
    | status -> Status.Unknown, status

(*
let kill_child id =
   print_string ("killing children of "^(Core.Pid.to_string id)^"\n");
   let _ = Unix.system ("killpstree "^(Core.Pid.to_string id)) in ()
 *)


open Async;;

let rec mu_elim_solver coe1 coe2 is_print_for_debug hes name =
  if !Global.config.verbose then
    print_string ("called "^name^" with coe1,coe2="^(string_of_int coe1)^","^(string_of_int coe2)^"\n");
  if is_print_for_debug then
    (Debug.print @@ Printf.sprintf "vvvvvvvvvvvvvvvvvv Original Hes (" ^ name ^ ") vvvvvvvvvvvvvvvvvv\n";
     Debug.print @@ Hesutil.str_of_hes hes;
     Debug.print "");
  let hes' = Hesutil.encode_body_exists coe1 ~range:coe2 @@ Hesutil.encode_top_exists coe1 ~range:coe2 hes in
  if is_print_for_debug then
    (Debug.print @@ Printf.sprintf "vvvvvvvvvvvvvvvvvv Encoded Hes (" ^ name ^ ") vvvvvvvvvvvvvvvvvv\n";
     Debug.print @@ Hesutil.str_of_hes hes';
     Debug.print "");
  let hes' = elim_mu_with_rec hes' coe1 (Bigint.of_int coe2) in
  if is_print_for_debug then
    (Debug.print @@ Printf.sprintf "vvvvvvvvvvvvv Eliminate Mu (coe: %d, %d) (%s) vvvvvvvvvvvvv\n" coe1 coe2 name;
     Debug.print @@ Hesutil.str_of_hes hes';
     Debug.print "");
  let hes' = Hesutil.simplify hes' in
  if is_print_for_debug then
    (Debug.print @@ "vvvvvvvvvvvvvvv Simplify (" ^ name ^ ") vvvvvvvvvvvvvvv\n";
     Debug.print @@ Hesutil.str_of_hes hes';
     Debug.print "");
  (Rfunprover.Solver.solve_onlynu_onlyforall_z3 false 0 is_print_for_debug hes')
   >>=
    (fun result ->
      match result with
    | Status.Valid -> return Status.Valid
    | Status.Invalid -> let (coe1',coe2') = if (coe1,coe2)=(1,1) then (1,8) else (2*coe1,2*coe2)
                in mu_elim_solver coe1' coe2' false hes name                  
    | _ -> return Status.Unknown)

                   
let solve_onlyforall _ hes =
  let solvers = ref [] in
  if Hesutil.is_onlyforall hes then (
    let nu_relaxed_hes = Hesutil.get_greatest_approx_hes ~range:100 hes in
    Debug.print "======================================";
    Debug.print "nu-relaxed hes";
    Debug.print "======================================";
    Debug.print @@ Hesutil.str_of_hes nu_relaxed_hes;
    Debug.print "";
    let nu_relax_solver = fun timeout is_print_for_debug ->
      let result, _ = Rfunprover.Solver.solve_onlynu_onlyforall false timeout is_print_for_debug nu_relaxed_hes in
      match result with
      | Status.Invalid -> Status.Invalid, Status.Invalid
      | status -> Status.Unknown, status
    in
    solvers := !solvers @ [nu_relax_solver, "nu-relaxed hes", true]
  );
  let config = !Global.config in
  let coe1, coe2 = match config.coe with
    | None -> 1, 1
    | Some coe -> coe
  in
  let hes_for_disprove = Hesutil.get_dual_hes hes in
  (* Debug.print "======================================";
  Debug.print "Generating mu-eliminated hes";
  Debug.print "======================================"; *)
  ignore @@ get_mu_elimed_solver coe1 coe2 false hes;
  Debug.print "======================================";
  Debug.print "Generating hes for disproving";
  Debug.print "======================================";
  let dresult = Deferred.any
                  [mu_elim_solver coe1 coe2 true hes "prover";
                   (mu_elim_solver coe1 coe2 true hes_for_disprove "disprover" >>| Status.flip)] in
  dresult

(*
  solvers := !solvers @ [
      (get_mu_elimed_solver coe1 coe2 false hes, Printf.sprintf "mu-eliminated hes with coe=%d,%d" coe1 coe2, true);
      (flip_solver @@ get_mu_elimed_solver coe1 coe2 false hes_for_disprove, Printf.sprintf "hes for disproving with coe=%d,%d" coe1 coe2, true);
    ];
  if config.coe = None then
    solvers := !solvers @ [
        (get_mu_elimed_solver 1 2 false hes,  "mu-eliminated hes with coe=1,2", false);
        (flip_solver @@ get_mu_elimed_solver 1 2 false hes_for_disprove,  "hes for disproving with coe=1,2", false);
        (get_mu_elimed_solver 1 10 false hes,  "mu-eliminated hes with coe=1,10", false);
        (flip_solver @@ get_mu_elimed_solver 1 10 false hes_for_disprove,  "hes for disproving with coe=1,10", false);
      ];
  run_solvers 1 true !solvers
 *)
  
(* let solve_onlyexists timeout hes cont =
  solve_onlyforall timeout (Hesutil.get_dual_hes hes) (fun r -> cont (Status.flip r)) *)

let solve hes cont =
  let timeout = 10 in
(*  
  if Hesutil.is_onlyforall hes && HesLogic.is_onlynu (Hesutil.encode_body_exists hes) then
 *)
  let dresult = 
    (if Hesutil.is_onlyforall hes && HesLogic.is_onlynu hes then
      Rfunprover.Solver.solve_onlynu_onlyforall_par false timeout true hes
  (*  
    else if Hesutil.is_onlyexists hes && HesLogic.is_onlynu (Hesutil.get_dual_hes hes |> Hesutil.encode_body_exists) then
  *)
    else if Hesutil.is_onlyexists hes && HesLogic.is_onlynu (Hesutil.get_dual_hes hes) then
      Rfunprover.Solver.solve_onlymu_onlyexists_par false timeout true hes
    else
      solve_onlyforall timeout hes) in
  upon dresult (fun result -> cont result; Rfunprover.Solver.kill_z3();
                              (*kill_child(Unix.getpid());*) shutdown 0
                              );
  Core.never_returns(Scheduler.go())
  
let solve_hes hes cont =
  Debug.print @@ Printf.sprintf "Input Hes: %s" @@ Hesutil.str_of_hes hes;
  Debug.print "";
  (* let hes = Hesutil.simplify hes in
  let hes = HesOptimizer.optimize hes in
  Debug.print @@ Printf.sprintf "Simplified/Optimized Hes: %s" @@ Hesutil.str_of_hes hes;
  Debug.print ""; *)
  solve hes cont

let solve_formula fml cont =
  Debug.print @@ Printf.sprintf "Input Formula: %s" @@ PrinterHum.str_of_formula fml;
  let fml = Ast.Logic.Formula.simplify @@ FormulaConverter.elim_fv_with_forall fml in
  Debug.print @@ Printf.sprintf "Simplified Formula: %s" @@ PrinterHum.str_of_formula fml;
  let hes = Hesutil.hes_of_formula fml in
  Debug.print @@ Printf.sprintf "Hes: %s" @@ Hesutil.str_of_hes hes;
  Debug.print "";
  solve_hes hes cont
