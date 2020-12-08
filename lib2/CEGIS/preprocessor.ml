open Ast.Logic
open Core open Core.Poly

module Debug = Fptprover.Debug

let count_pvar_apps_clauses cls =
  let pvs =
    List.concat_map cls ~f:(fun (ps, ns, _) -> (ps @ ns) |> List.map ~f:Atom.get_fpv)
    |> Set.Poly.union_list
  in
  let pos_nonlin = ref Set.Poly.empty in
  let neg_nonlin = ref Set.Poly.empty in
  pvs
  |> Set.Poly.to_list
  |> List.map ~f:(fun pvar ->
      pvar,
      List.map cls ~f:(fun (ps, ns, _) ->
          let pc = List.count ps ~f:(Atom.occur pvar) in
          let nc = List.count ns ~f:(Atom.occur pvar) in
          (if pc >= 2 then pos_nonlin := Set.Poly.add !pos_nonlin pvar);
          (if nc >= 2 then neg_nonlin := Set.Poly.add !neg_nonlin pvar);
          if pc > 0 && nc > 0 then 1, 0, 0 else 0, pc, nc)
      |> List.unzip3
      |> (fun (dcs, pcs, ncs) -> List.fold dcs ~init:0 ~f:(+),
                                 List.fold pcs ~init:0 ~f:(+),
                                 List.fold ncs ~init:0 ~f:(+))),
  Set.Poly.inter !pos_nonlin !neg_nonlin


let resolve pv clauses =
  Debug.print @@ "eliminating " ^ Ast.Ident.name_of_pvar pv;
  let clauses_pos, clauses_neg, clauses_rest =
    List.partition3_map clauses ~f:(fun (ps, ns, phi) ->
        if List.exists ps ~f:(Atom.occur pv) then `Fst (ps, ns, phi)
        else if List.exists ns ~f:(Atom.occur pv) then `Snd (ps, ns, phi)
        else `Trd (ps, ns, phi))
  in
  clauses_rest @
  (List.cartesian_product clauses_pos clauses_neg
   |> List.map ~f:(fun (pcl, ncl) ->
       let (ps1, ns1, phi1) = pcl in
       let (ps2, ns2, phi2) = ncl in

       if List.count ns2 ~f:(Atom.occur pv) = 1 then
         let ps, ps1 = List.partition_tf ps1 ~f:(Atom.occur pv) in
         List.map ps ~f:(function
             | Atom.App(_, ts1, _) -> begin
                 let (ps2, ns2, phi2) = Formula.alpha_conv_clause ncl in
                 let ns, ns2 = List.partition_tf ns2 ~f:(Atom.occur pv) in
                 match ns with
                 | [Atom.App(_, ts2, _)] ->
                   ps2, ns2, phi2 ::
                             (match
                                List.map2 ts1 ts2 ~f:(fun t1 t2 ->
                                    Formula.mk_atom (T_bool.mk_neq t1 t2 Dummy) Dummy)
                              with
                              | Ok res -> res
                              | Unequal_lengths -> assert false)
                 | _ -> assert false
               end
             | _ -> assert false)
         |> List.unzip3
         |> (fun (pss, nss, phiss) ->
             List.concat (ps1 :: pss),
             List.concat (ns1 :: nss),
             Formula.or_of (phi1 :: List.concat phiss) Dummy)
       else if List.count ps1 ~f:(Atom.occur pv) = 1 then
         let ns, ns2 = List.partition_tf ns2 ~f:(Atom.occur pv) in
         List.map ns ~f:(function
             | Atom.App(_, ts2, _) -> begin
                 let (ps1, ns1, phi1) = Formula.alpha_conv_clause pcl in
                 let ps, ps1 = List.partition_tf ps1 ~f:(Atom.occur pv) in
                 match ps with
                 | [Atom.App(_, ts1, _)] ->
                   ps1, ns1, phi1 ::
                             (match
                                List.map2 ts1 ts2 ~f:(fun t1 t2 ->
                                    Formula.mk_atom (T_bool.mk_neq t1 t2 Dummy) Dummy)
                              with
                              | Ok res -> res
                              | Unequal_lengths -> assert false)
                 | _ -> assert false
               end
             | _ -> assert false)
         |> List.unzip3
         |> (fun (pss, nss, phiss) ->
             List.concat (ps2 :: pss),
             List.concat (ns2 :: nss),
             Formula.or_of (phi2 :: List.concat phiss) Dummy)
       else assert false))

let elim_trivial_pvars clauses =
  let pvs =
    List.rev_filter_map (clauses |> count_pvar_apps_clauses |> fst)
      ~f:(fun (pvar, (_, pc, nc)) ->
          if pc = 0 (* pvar can be false *) then
            (Debug.print @@ "assigning " ^ Ast.Ident.name_of_pvar pvar ^ " to false"; Some pvar)
          else  if nc = 0 (* pvar can be true *) then
            (Debug.print @@ "assigning " ^ Ast.Ident.name_of_pvar pvar ^ " to true"; Some pvar)
          else None)
  in
  List.filter clauses ~f:(fun (ps, ns, _) ->
      List.for_all pvs ~f:(fun pv -> List.for_all (ps @ ns) ~f:(fun a -> not (Atom.occur pv a))))

let rec find_elim_interm_pvars clauses =
  let config = !Fptprover.Global.config in
  let p = clauses |> count_pvar_apps_clauses in
  fst p
  |> List.filter_map ~f:(fun (pvar, (dc, pc, nc)) ->
      if dc = 0 && not (Set.Poly.mem (snd p) pvar) then Some(pvar, (pc, nc)) else None)
  |> List.min_elt ~compare:(fun (_, (pc1, nc1)) (_, (pc2, nc2)) -> pc1 * nc1 - pc2 * nc2)
  |> function
  | None -> clauses
  | Some (pv, (pc, nc)) ->
    Debug.print @@ Ast.Ident.name_of_pvar pv ^ " occurs " ^
                   (string_of_int pc) ^ " times positively and " ^
                   (string_of_int nc) ^ " times negatively";
    if pc * nc <= config.resolution_threshold then
      clauses |> resolve pv |> find_elim_interm_pvars
    else clauses

(* Formula.t list -> Formula.t list *)
let elim_pvars (phis: Formula.t list) : Formula.t list =
  Formula.and_of phis Dummy
  |> Formula.cnf_of
  |> elim_trivial_pvars
  |> find_elim_interm_pvars
  |> List.map ~f:Formula.of_clause

let get_elimed_trivial_pvars (phis: Formula.t list) : (Ast.Ident.pvar list * Ast.Ident.pvar list) =
  let clauses = Formula.and_of phis Dummy |> Formula.cnf_of in
  let pvar_count = clauses |> count_pvar_apps_clauses |> fst in
  List.rev_filter_map pvar_count ~f:(fun (pvar, (_, _, nc)) -> if nc = 0 then Some pvar else None),
  List.rev_filter_map pvar_count ~f:(fun (pvar, (_, pc, _)) -> if pc = 0 then Some pvar else None)

let const_predicates (phis: Formula.t list) =
  let ppvs, npvs = get_elimed_trivial_pvars phis in
  let phi = List.fold_left ~init:(List.hd_exn phis) (List.tl_exn phis)
      ~f:(fun phi phi' -> Formula.mk_and phi phi' Dummy) in
  let atoms = Formula.atoms phi in
  let const_ value pvs =
    List.map ~f:(fun pv -> Set.Poly.find atoms
                    ~f:(fun atom ->
                        match atom with
                        | App (pred, _, _) -> begin
                            match pred with
                            | Var (pv', _) -> pv = pv'
                            | _ -> false
                          end
                        | _ -> false)) pvs
    |> List.map ~f:(fun atom -> match atom with
        | Some (Atom.App (Predicate.Var (pvar, sorts), _, _)) ->
          let params = Template.params_of_sorts sorts in
          (pvar, params), Formula.mk_atom (value Dummy) Dummy
        | _ -> assert false) in
  const_ Atom.mk_true ppvs @ const_ Atom.mk_false npvs

let solution_of_unit_clause clause =
  let (ps, ns, phi) = clause in
  let ftv = Formula.get_ftv_sort phi |> Set.Poly.elements in
  let quantifiers = List.map ~f:(fun (_, sort) -> Ast.Ident.mk_fresh_tvar (), sort) ftv in
  let subst_map =
    List.zip_exn ftv quantifiers
    |> List.map ~f:(fun ((tvar, sort), (bvar, sort')) ->
        assert (sort=sort');
        tvar, Term.mk_var bvar sort Dummy)
    |> Map.Poly.of_alist_exn
  in
  let phi = Formula.subst subst_map phi in
  if List.length ps = 1 then
    match List.hd_exn ps with
    | Atom.App (Predicate.Var (pvar, sorts), terms, _) -> begin
        let phi = Formula.mk_neg phi Dummy |> Formula.simplify in
        let params = Template.params_of_sorts sorts in
        let phi = try
            List.fold_left ~init:phi (List.zip_exn params terms)
              ~f:(fun phi ((tvar, sort), term) ->
                  let term = Term.subst subst_map term in
                  let eq = Formula.mk_atom (T_bool.mk_eq term (Term.mk_var tvar sort Dummy) Dummy) Dummy in
                  Formula.mk_and eq phi Dummy)
          with _ -> failwith "params must be exactly same length to terms"
        in
        let phi = Formula.mk_exists quantifiers phi Dummy in
        let target = pvar, params in
        target, phi
      end
    | _ -> assert false
  else if List.length ns = 1 then
    match List.hd_exn ns with
    | Atom.App (Predicate.Var (pvar, sorts), terms, _) -> begin
        let params = Template.params_of_sorts sorts in
        let condition = try
            List.fold_left ~init:None (List.zip_exn params terms)
              ~f:(fun condition ((tvar, sort), term) ->
                  let term = Term.subst subst_map term in
                  let eq = Formula.mk_atom (T_bool.mk_eq term (Term.mk_var tvar sort Dummy) Dummy) Dummy in
                  match condition with
                  | None -> Some eq
                  | Some phi -> Some (Formula.mk_and eq phi Dummy))
          with _ -> failwith "params must be exactly same length to terms"
        in
        let phi =
          match condition with
          | Some condition ->
            Formula.mk_imply condition phi Dummy
            |> fun phi -> Formula.mk_forall quantifiers phi Dummy
          | None -> failwith "there must be at least one params"
        in
        let target = pvar, params in
        target, phi
      end
    | _ -> assert false
  else failwith "one of ps or ns has one element, the other does zero"

let subst_solution cnf sol =
  let ((pvar, params), phi) = sol in
  let subst_solution (atom : Atom.t) : Formula.t =
    Atom.subst_pred pvar params phi atom
  in
  let subst_aux atoms phi pos : Atom.t list * Formula.t =
    List.fold_left ~init:([], phi) ~f:(fun (atoms, phi) -> function
        | Atom.App (Predicate.Var(pvar', _), _, _) as atom ->
          if pvar' = pvar
          then atoms,
               if pos then Formula.mk_or phi (subst_solution atom) Dummy
               else Formula.mk_or phi (Formula.mk_neg (subst_solution atom) Dummy) Dummy
          else atom::atoms, phi
        | _ -> failwith "Invalid pattern of Atom") atoms
  in
  List.filter_map cnf ~f:(fun (ps, ns, phi) ->
      let (ps, phi) = subst_aux ps phi true in
      let (ns, phi) = subst_aux ns phi false in
      let phi = Formula.simplify phi in
      if List.length ps + List.length ns > 0 then Some (ps, ns, phi) else None)

let rec solve_non_rec cnf =
  let sol =
    match List.find ~f:(fun (ps, ns, _) -> List.length ps + List.length ns = 1) cnf with
    | Some clause -> solution_of_unit_clause clause
    | None -> failwith "At least one clause must have exactly one predicate variable."
  in
  let cnf = subst_solution cnf sol in
  if List.length cnf = 0 then [sol] else sol :: solve_non_rec cnf
