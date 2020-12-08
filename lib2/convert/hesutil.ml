open Ast
open Ast.Logic
open Fptprover
open Hes

let rec iter_app (f: Ident.pvar -> Term.t list -> unit) formula =
  if Formula.is_atom formula then (
    let atom, _ = Formula.let_atom formula in
    if Atom.is_app atom then
      let pred, args, _ = Atom.let_app atom in
      if Predicate.is_var pred then
        let pvar, _ = Predicate.let_var pred in
        f pvar args
  )
  else if Formula.is_unop formula then
    let _, fml, _ = Formula.let_unop formula in
    iter_app f fml
  else if Formula.is_binop formula then
    let _, fml1, fml2, _ = Formula.let_binop formula in
    iter_app f fml1;
    iter_app f fml2
  else if Formula.is_bind formula then
    let _, _, fml, _ = Formula.let_bind formula in
    iter_app f fml
  else
    assert false
(* failwith @@ Printf.sprintf "Hesutil.iter_app: not implemented: %s" @@ Convert.PrinterHum.str_of_formula formula *)

(* applicationを置換 *)
let rec replace_app (replacer: Formula.t -> Formula.t) formula =
  if Formula.is_atom formula then
    let atom, info = Formula.let_atom formula in
    let formula = Formula.mk_atom atom info in
    if Atom.is_app atom then
      let pred, _, _ = Atom.let_app atom in
      if Predicate.is_var pred then
        replacer formula
      else formula
    else
      formula
  else if Formula.is_binop formula then
    let binop, left, right, info = Formula.let_binop formula in
    Formula.mk_binop binop (replace_app replacer left) (replace_app replacer right) info
  else if Formula.is_unop formula then
    let unop, body, info = Formula.let_unop formula in
    Formula.mk_unop unop (replace_app replacer body) info
  else if Formula.is_bind formula then
    let binder, bounds, body, info = Formula.let_bind formula in
    Formula.mk_bind binder bounds (replace_app replacer body) info
  else assert false

(* 出現するfunctionを取得 *)
let get_next_funcs fml =
  let res = ref [] in
  let _ = replace_app (fun fml ->
      let atom, _ = Formula.let_atom fml in
      let pred, _, _ = Atom.let_app atom in
      let pvar, _ = Predicate.let_var pred in
      res := pvar :: !res;
      fml
    ) fml
  in
  List.sort_uniq Ident.pvar_compare !res

(* applicationに引数を追加する *)
let replace_app_add formula arg sort =
  replace_app (fun fml ->
      let atom, info = Formula.let_atom fml in
      let pred, args, info' = Atom.let_app atom in
      let pvar, arg_sorts = Predicate.let_var pred in
      Formula.mk_atom
        (Atom.mk_app
           (Predicate.mk_var pvar (sort :: arg_sorts))
           (arg :: args)
           info'
        ) info
    ) formula

let elim_mu_from_funcs_with_rec funcs tvar_rec =
  List.map (fun func ->
      let fix, pvar, args, body = (HesLogic.let_function func) in
      let args = (tvar_rec, T_int.SInt) :: args in
      let term = Term.mk_var tvar_rec T_int.SInt Dummy in
      if fix = Predicate.Nu then
        let body = replace_app_add body term T_int.SInt in
        HesLogic.mk_func Predicate.Nu pvar args body
      else
        (* replace all F X Y --> F (rec_ - 1) X Y in body*)
        let term = Term.mk_funapp T_int.Sub [term; T_int.one Dummy] Dummy in
        let body = replace_app_add body term T_int.SInt in
        (* body --> rec_ > 0 /\ body *)
        let body = Formula.mk_and
            (Formula.mk_atom
               (T_int.mk_gt term (T_int.zero Dummy) Dummy)
               Dummy)
            body Dummy in
        HesLogic.mk_func Predicate.Nu pvar args body
    ) funcs

let avoid_dup pvar pvars =
  if not @@ List.exists (fun pvar' -> Ident.name_of_pvar pvar' = Ident.name_of_pvar pvar) pvars then
    pvar
  else
    let suffix = ref 2 in
    while List.exists (fun pvar' -> Ident.name_of_pvar pvar' = Ident.name_of_pvar pvar ^ (string_of_int !suffix)) pvars do
      suffix := !suffix + 1
    done;
    Ident.Pvar (Ident.name_of_pvar pvar ^ (string_of_int !suffix))

(* Usage: let entry, funcs, _ = hes_of_formula_with_env fml [] Env.empty Env.empty *)
(* Note: bound_tvars: term variables bound by fixpoint predicates *)
let rec hes_of_formula_with_env fml funcs env used_pvars bound_tvars = let open Formula in
  match fml with
  | Atom (atom, info) -> begin
      match atom with
      | App (Fixpoint (fp, pvar, bounds, body), outer_args, info') ->
        (* (fp pvar(bounds). body)(args) *)
        let new_pvar = avoid_dup pvar used_pvars in
        let used_pvars = new_pvar :: used_pvars in
        let env = Env.update [pvar, new_pvar] env in
        let bound_tvars = Gather.Variables.union bound_tvars (Gather.Variables.of_list bounds) in
        let body, funcs, used_pvars = hes_of_formula_with_env body funcs env used_pvars bound_tvars in

        let fvs_of_body = Gather.free_variables_of_formula body in
        let additional_params = Gather.Variables.to_list @@
          Gather.Variables.diff
            fvs_of_body
            (Gather.Variables.inter
               bound_tvars
               (Gather.Variables.of_list bounds)) in

        let new_bounds = bounds @ additional_params in
        let new_outer_args = outer_args @ AstUtil.args_of_params  additional_params in
        let new_inner_args = AstUtil.args_of_params new_bounds in
        let new_sorts = AstUtil.sorts_of_params new_bounds in

        let new_pvar_app = Formula.mk_atom (Atom.mk_app (Predicate.Var(new_pvar, new_sorts)) new_inner_args Dummy) Dummy in
        let body = subst_pred pvar bounds new_pvar_app body in
        let funcs = (HesLogic.mk_func fp new_pvar new_bounds body) :: funcs in
        let fml' = Formula.mk_atom
            (Atom.mk_app
               (Predicate.mk_var new_pvar new_sorts)
               new_outer_args info')
            info in
        fml', funcs, used_pvars
      | App (Var (pvar, sorts), args, info') ->
        let new_pred = Predicate.mk_var (Env.lookup pvar env) sorts in
        let fml' = Formula.mk_atom (Atom.mk_app new_pred args info') info in
        fml', funcs, used_pvars
      | _ -> fml, funcs, used_pvars
    end
  | UnaryOp (op, fml, info) ->
    let entry, funcs, used_pvars = hes_of_formula_with_env fml funcs env used_pvars bound_tvars in
    let fml' = Formula.mk_unop op entry info in
    fml', funcs, used_pvars
  | BinaryOp (op, lhs, rhs, info) ->
    let left_entry, funcs, used_pvars = hes_of_formula_with_env lhs funcs env used_pvars bound_tvars in
    let right_entry, funcs, used_pvars = hes_of_formula_with_env rhs funcs env used_pvars bound_tvars in
    let fml' = Formula.mk_binop op left_entry right_entry info in
    fml', funcs, used_pvars
  | Bind (binder, bounds, body, info) ->
    let entry, funcs, used_pvars = hes_of_formula_with_env body funcs env used_pvars bound_tvars in
    let fml' = Formula.mk_bind binder bounds entry info in
    fml', funcs, used_pvars
  | LetRec (letrec_funcs, body, _) ->
    let env, used_pvars = List.fold_left
        (fun (env, used_pvars) (_, pvar, _, _) ->
           let new_pvar = avoid_dup pvar used_pvars in
           let used_pvars = new_pvar :: used_pvars in
           Env.update [pvar, new_pvar] env, used_pvars)
        (env, used_pvars)
        letrec_funcs in
    let entry, funcs, used_pvars = hes_of_formula_with_env body funcs env used_pvars bound_tvars in
    let funcs, used_pvars = List.fold_left
        (fun (funcs, used_pvars) (fp, pvar, bounds, body) ->
           let body, funcs, used_pvars = hes_of_formula_with_env body funcs env used_pvars bound_tvars in
           HesLogic.mk_func fp (Env.lookup pvar env) bounds body :: funcs, used_pvars
        ) (funcs, used_pvars) letrec_funcs
    in
    entry, funcs, used_pvars

let hes_of_formula fml =
  let entry, funcs, _ = hes_of_formula_with_env fml [] Env.empty [] Gather.Variables.empty in
  HesLogic.mk_hes funcs entry

let formula_of_hes _ =
  assert false (* TODO *)

let str_of_func func =
  let fix, Ident.Pvar pvar_name, args, body = Hes.HesLogic.let_function func in
  Printf.sprintf
    "%s%s: bool =%s %s;"
    pvar_name
    (if List.length args > 0 then " "^PrinterHum.str_of_params args else "")
    (PrinterHum.str_of_fixpoint fix)
    (PrinterHum.str_of_formula body)

let str_of_func_list funcs =
  List.map str_of_func funcs
  |> String.concat "\n"

let str_of_hes hes =
  let funcs, entry = HesLogic.let_hes hes in
  (PrinterHum.str_of_formula entry) ^ "\n"
  ^ "where\n"
  ^ str_of_func_list funcs
(*  ^ (String.concat "\n"
       (List.map
          (fun func ->
             let fix, Ident.Pvar pvar_name, args, body = HesLogic.let_function func in
             pvar_name
             ^ "(" ^ (String.concat "," (List.map (fun (Ident.Tvar var_name, _) -> var_name) args)) ^ ")"
             ^ " =" ^ (PrinterHum.str_of_fixpoint fix) ^ " "
             ^ (PrinterHum.str_of_formula body)
          ) funcs)
    ) *)
  
let move_quantifiers_to_front hes =
  let funcs, entry = HesLogic.let_hes hes in
  HesLogic.mk_hes
    (List.map
       (fun func ->
          let fix, pvar, args, body = HesLogic.let_function func in
          HesLogic.mk_func fix pvar args @@ FormulaConverter.move_quantifiers_to_front body
       ) funcs)
  @@ FormulaConverter.move_quantifiers_to_front entry

let simplify hes =
  let funcs, entry = HesLogic.let_hes hes in
  HesLogic.mk_hes
    (List.map
       (fun (fixpoint, pvar, args, formula) ->
          (fixpoint, pvar, args, Formula.simplify formula))
       funcs)
    (Formula.simplify entry)

let output_text text file =
  if !Global.config.convert then begin
    let file =
      match file with
      | None -> begin
        let org_fullpath = !Global.config.filename in
        Filename.basename org_fullpath
      end
      | Some s -> s
    in
    let file = Filename.concat "./converted/" file in
    print_endline @@ "output_text: " ^ file;
    let oc = open_out file in
    output_string oc text;
    close_out oc
  end
  
let get_dual_hes hes =
  let funcs, entry = HesLogic.let_hes hes in
  let pvars = List.map (fun (_, pvar, _, _) -> pvar) funcs in
  let subst formula = List.fold_left (fun fml pvar -> Formula.subst_neg pvar fml) formula pvars in
  let hes = HesLogic.mk_hes
    (List.map
       (fun (fixpoint, pvar, args, formula) ->
          (Predicate.flip_fixpoint fixpoint,
           pvar, args, Formula.simplify_neg (subst formula)))
       funcs)
    (Formula.simplify_neg (subst entry)) in
  output_text (PrinterHum2.str_of_hes' hes) (Some "dual1");
  hes

let add_prefix_to_tvars prefix bounds fml =
  let subst, bounds_rev =
    List.fold_left
      (fun (subst, bounds_rev) (tvar, sort) ->
         let new_tvar = Ident.Tvar (prefix ^ Ident.name_of_tvar tvar) in
         Core.Map.Poly.add_exn subst ~key:tvar ~data:(Term.mk_var new_tvar sort Dummy),
         (new_tvar, sort) :: bounds_rev
      )
      (Core.Map.Poly.empty, [])
      bounds
  in
  let bounds = List.rev bounds_rev in
  bounds,
  Formula.subst subst fml

let mk_exists_funs_mu funname_cand bounds_for_fv pvars exists_formula =
  (* avoid dup *)
  let pvar = avoid_dup (Ident.Pvar funname_cand) pvars in
  (* make exists body *)
  let bounds, body, _ = Formula.let_exists exists_formula in
  let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
  let mk_app ?replacer () =
    Formula.mk_atom
      (Atom.mk_app
         (Predicate.mk_var pvar
          @@ List.map (fun (_, sort) -> sort) (bounds_for_fv @ bounds))
         ((List.map (fun (tvar, sort) -> Term.mk_var tvar sort Dummy) bounds_for_fv)
          @ (List.map
               (fun (tvar, sort) ->
                  let term_var = Term.mk_var tvar sort Dummy in
                  match replacer with
                  | Some replacer -> replacer tvar term_var
                  | None -> term_var
               ) bounds))
         Dummy)
      Dummy
  in
  let mk_replacer tvar op =
    fun tvar' term_var ->
      if tvar' = tvar then
        op term_var (T_int.one Dummy) Dummy
      else
        term_var
  in
  let body =
    Formula.or_of
      (body :: List.fold_left
         (fun res (tvar, _) ->
            mk_app ~replacer:(mk_replacer tvar T_int.mk_add) ()
            :: mk_app ~replacer:(mk_replacer tvar T_int.mk_sub) ()
            :: res
         )
         []
         bounds) Dummy
  in
  [HesLogic.mk_func Predicate.Mu pvar (bounds_for_fv @ bounds) body], mk_app ~replacer:(fun _ _ -> T_int.zero Dummy) ()


let mk_exists_funs_mus funname_cand bounds_for_fv pvars exists_formula =
  let bounds, body, _ = Formula.let_exists exists_formula in
  let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
  let rec mk_exists_funs bounds_for_fv bounds pvars =
    match bounds with
    | [] -> [], body
    | (tvar, sort) :: tail ->
      (* avoid dup *)
      let tvar_name = Ident.name_of_tvar tvar in
      let pvar_left = avoid_dup (Ident.Pvar (funname_cand ^ "_" ^ tvar_name ^ "_n")) pvars in
      let pvar_right = avoid_dup (Ident.Pvar (funname_cand ^ "_" ^ tvar_name ^ "_p")) pvars in
      (* rec *)
      let args = (tvar, sort) :: bounds_for_fv in
      let funcs, body = mk_exists_funs args tail (pvar_left :: pvar_right :: pvars) in
      (* make exists body *)
      let mk_body pvar arg =
        Formula.mk_atom
          (Atom.mk_app
             (Predicate.mk_var pvar
              @@ List.map (fun (_, sort) -> sort) (bounds_for_fv @ bounds))
             (arg :: List.map (fun (tvar, sort) -> Term.mk_var tvar sort Dummy) bounds_for_fv)
             Dummy)
          Dummy
      in
      let term_var = Term.mk_var tvar sort Dummy in
      let zero = T_int.zero Dummy in
      let one = T_int.one Dummy in
      let body_left = Formula.mk_or body (mk_body pvar_left @@ T_int.mk_sub term_var one Dummy) Dummy in
      let body_right = Formula.mk_or body (mk_body pvar_right @@ T_int.mk_add term_var one Dummy) Dummy in
      HesLogic.mk_func Predicate.Mu pvar_left args body_left
      :: HesLogic.mk_func Predicate.Mu pvar_right args body_right
      :: funcs,
      Formula.mk_or
        (mk_body pvar_left zero)
        (mk_body pvar_right zero)
        Dummy
  in
  mk_exists_funs bounds_for_fv bounds pvars

let mk_exists_funs_nu range funname_cand bounds_for_fv pvars exists_formula =
  (* avoid dup *)
  let pvar = avoid_dup (Ident.Pvar funname_cand) pvars in
  (* make exists body *)
  let bounds, body, _ = Formula.let_exists exists_formula in
  let bounds, body = add_prefix_to_tvars "#exists_" bounds body in
  let mk_app ?replacer () =
    Formula.mk_atom
      (Atom.mk_app
         (Predicate.mk_var pvar
          @@ List.map (fun (_, sort) -> sort) (bounds_for_fv @ bounds))
         ((List.map (fun (tvar, sort) -> Term.mk_var tvar sort Dummy) bounds_for_fv)
          @ (List.map
               (fun (tvar, sort) ->
                  let term_var = Term.mk_var tvar sort Dummy in
                  match replacer with
                  | Some replacer -> replacer tvar term_var
                  | None -> term_var
               ) bounds))
         Dummy)
      Dummy
  in
  let mk_replacer tvar op =
    fun tvar' term_var ->
      if tvar' = tvar then
        op term_var (T_int.one Dummy) Dummy
      else
        term_var
  in
  let rec rep body subst res = function
    | [] -> Formula.subst subst body :: res
    | (tvar, sort) :: tail ->
      let subst' =
        Core.Map.Poly.add_exn subst ~key:tvar ~data:(T_int.mk_unary_neg (Term.mk_var tvar sort Dummy) Dummy)
      in
      rep body subst (rep body subst' res tail) tail
  in
  (* F x =nu x >= 0 /\ (F(x) \/ F(-x) \/ Exists(x-1)) *)
  let body =
    Formula.and_of
      (* F(x) \/ F(-x) \/ Exists(x-1) *)
      ((Formula.or_of
          (* F(x) \/ F(-x) *)
          (rep body Core.Map.Poly.empty [] bounds
           (* Exists(x-1) *)
           @ (List.map
                (fun (tvar, _) -> mk_app ~replacer:(mk_replacer tvar T_int.mk_sub) ()))
             bounds)
          Dummy)
       (* x >= 0 *)
       :: List.map
         (fun (tvar, sort) ->
            Formula.mk_atom (T_int.mk_geq (Term.mk_var tvar sort Dummy) (T_int.zero Dummy) Dummy) Dummy
         ) bounds)
      Dummy
  in
  (* forall x. x >= range => Exists(x) *)
  let entry =
    Formula.simplify
    @@ Formula.mk_forall bounds
      (Formula.mk_imply
         (* x >= range *)
         (Formula.and_of
            (List.map
               (fun (tvar, sort) ->
                  Formula.mk_atom (T_int.mk_geq (Term.mk_var tvar sort Dummy) (T_int.mk_int range Dummy) Dummy) Dummy
               ) bounds)
            Dummy)
         (* Exists(x) *)
         (mk_app ())
         Dummy)
      Dummy
  in
  [HesLogic.mk_func Predicate.Nu pvar (bounds_for_fv @ bounds) body], entry

let mk_exists_funs ?(range=100) funname_cand bounds_for_fv pvars fml =
  let config = !Global.config in
  let dispatched =
    match config.encoding_mode with
    | Config.Mu -> mk_exists_funs_mu
    | Config.Mus -> mk_exists_funs_mus
    | Config.Nu -> mk_exists_funs_nu (Bigint.of_int range)
  in
  let rec add_pvars pvars = function
    | [] -> pvars
    | func :: tail ->
      let _, pvar, _, _ = HesLogic.let_function func in
      add_pvars (pvar :: pvars) tail
  in
  let rec rep pvars bounds_for_fv fml =
    if Formula.is_atom fml then
      [], fml, pvars
    else if Formula.is_and fml || Formula.is_or fml then
      let binop, fml_left, fml_right, info = Formula.let_binop fml in
      let funcs_left, fml_left, pvars = rep pvars bounds_for_fv fml_left in
      let funcs_right, fml_right, pvars = rep pvars bounds_for_fv fml_right in
      funcs_left @ funcs_right, Formula.mk_binop binop fml_left fml_right info, pvars
    else if Formula.is_forall fml then
      let bounds, fml, info = Formula.let_forall fml in
      let funcs, fml, pvars = rep pvars (bounds @ bounds_for_fv) fml in
      funcs, Formula.mk_forall bounds fml info, pvars
    else if Formula.is_exists fml then
      let bounds, fml, info = Formula.let_exists fml in
      let funcs, fml, pvars = rep pvars (bounds @ bounds_for_fv) fml in
      let fv = Formula.get_ftv fml in
      let fml = Formula.mk_exists bounds fml info in
      let bounds_for_fv = List.filter
          (fun (tvar, _) -> Core.Set.Poly.mem fv tvar)
          bounds_for_fv
      in
      let funcs', fml = dispatched funname_cand bounds_for_fv pvars fml in
      funcs' @ funcs, fml, add_pvars pvars funcs'
    else
      failwith "not implemented"
  in
  let funcs, fml, _ = rep pvars bounds_for_fv fml in
  funcs, fml

let encode_top_exists ?range hes =
  let funcs, entry = HesLogic.let_hes hes in
  let pvars = List.map
      (fun func ->
         let _, pvar, _, _ = HesLogic.let_function func in pvar) funcs
  in
  let funcs', caller = mk_exists_funs ?range "Exists" [] pvars entry in
  HesLogic.mk_hes (funcs' @ funcs) caller

(* move_quantifiers_to_front must be called before this is called *)
let encode_body_exists ?range hes =
  let funcs, entry = HesLogic.let_hes hes in
  let pvars = List.map
      (fun func ->
         let _, pvar, _, _ = HesLogic.let_function func in pvar) funcs
  in
  let funcs, _ =
    (List.fold_left
       (fun (funcs, pvars) func ->
          let fix, pvar, bounds, body = HesLogic.let_function func in
          let funcs', caller = mk_exists_funs ?range (Ident.name_of_pvar pvar ^ "!") bounds pvars body in
          let func = HesLogic.mk_func fix pvar bounds caller in
          funcs' @ func :: funcs, pvars
       ) ([], pvars) funcs)
  in
  let funcs = List.rev funcs in
  HesLogic.mk_hes funcs entry

let is_onlyexists hes =
  let funcs, entry = HesLogic.let_hes hes in
  let rec check fml =
    if Formula.is_atom fml then
      true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then
      false
    else if Formula.is_exists fml then
      let _, fml, _ = Formula.let_exists fml in
      check fml
    else
      (Debug.print @@ Printf.sprintf "not implemented for: %s" @@ PrinterHum.str_of_formula fml;
       failwith "not implemented")
  in
  List.for_all (fun fml -> check @@ Formula.simplify fml)
  @@ entry :: List.map (fun (_, _, _, body) -> body) funcs

let is_onlyforall hes =
  let funcs, entry = HesLogic.let_hes hes in
  let rec check fml =
    if Formula.is_atom fml then
      true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then
      let _, fml, _ = Formula.let_forall fml in
      check fml
    else if Formula.is_exists fml then
      false
    else
      failwith "not implemented"
  in
  List.for_all check
  @@ entry :: List.map (fun (_, _, _, body) -> body) funcs

let is_noquantifier hes =
  is_onlyexists hes && is_onlyforall hes

let get_greatest_approx_hes ?range hes =
  let hes = encode_body_exists ?range hes |> encode_top_exists ?range in
  let funcs, entry = HesLogic.let_hes hes in
  HesLogic.mk_hes (List.map (fun (_, pvar, args, formula) -> (Predicate.Nu, pvar, args, formula)) funcs) entry

let elim_fv_with_forall hes =
  let funcs, entry = HesLogic.let_hes hes in
  let entry = FormulaConverter.elim_fv_with_forall entry in
  HesLogic.mk_hes funcs entry

let str_of_hes' = PrinterHum2.str_of_hes'
