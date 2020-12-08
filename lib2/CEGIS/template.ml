open Ast.Logic
open Ast
open Core open Core.Poly

type t = (Ident.pvar * (Ident.tvar * Sort.t) list) * Formula.t

let izero = T_int.zero Dummy
let rzero = T_int.mk_real "0" Dummy

let str_of ((Ident.Pvar pvar, _), phi) =
  Printf.sprintf "(%s -> %s)" pvar (Convert.PrinterHum.str_of_formula phi)

let params_of_sorts sorts =
  let param_ident_count = ref 0 in
  let mk_param_ident() =
    incr param_ident_count;
    Ident.Tvar ("x" ^ (string_of_int !param_ident_count)) in
  List.map sorts ~f:(fun sort -> (mk_param_ident(), sort))

(* stub implimentation *)
let join_targets target1 _ = target1

let mk_and ((target1, phi1): t) ((target2, phi2): t) : t =
  join_targets target1 target2, Formula.mk_and phi1 phi2 Dummy

let mk_or ((target1, phi1): t) ((target2, phi2): t) : t =
  join_targets target1 target2, Formula.mk_or phi1 phi2 Dummy

let mk_neg ((target, phi): t): t =
  target, Formula.mk_neg phi Dummy

let mk_and_ (phi: Formula.t) ((target, phi'): t) : t =
  target, Formula.mk_and phi phi' Dummy

let preprocess xs =
  if List.exists xs ~f:(fun (_, sort) -> sort = T_int.SReal)
  then (List.map xs ~f:(function
      | x, T_int.SInt -> (x, T_int.SReal)
      | x -> x
    ), true)
  else (xs, false)

let gen_arithmetic_invariant_template params is_real =
  let int_template x =
    let coeff = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt Dummy in
    T_int.mk_mult coeff (Term.mk_var x T_int.SInt Dummy) Dummy in
  let real_template x =
    let coeff = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SReal Dummy in
    T_int.mk_mult coeff (Term.mk_var x T_int.SReal Dummy) Dummy in
  let negb = Term.mk_var
      (Ident.mk_fresh_parameter ())
      (if is_real then T_int.SReal else T_int.SInt)
      Dummy in
  let zero = if is_real then rzero else izero in
  List.map params ~f:(function
      | x, T_int.SInt -> int_template x
      | x, T_int.SReal -> real_template x
      | _ -> failwith "can not happen")
  |> (fun terms ->
      Formula.mk_atom
        (T_int.mk_geq
           (T_int.mk_sum terms negb Dummy)
           zero
           Dummy)
        Dummy)

let gen_arithmetic_well_founded_template params is_real =
  assert ((List.length params)%2 = 0);
  assert (List.length params > 1);
  let xs, ys = List.split_n params (List.length params/2) in
  assert (List.length xs = List.length ys);
  let int_template (x, y) =
    let coeff = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt Dummy in
    (T_int.mk_mult coeff x Dummy, T_int.mk_mult coeff y Dummy) in

  let real_template (x, y) =
    let coeff = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SReal Dummy in
    (T_int.mk_mult coeff x Dummy, T_int.mk_mult coeff y Dummy) in

  let xys = List.zip_exn xs ys in
  List.iter xys ~f:(fun ((_, sx), (_, sy)) -> assert (sx=sy));
  let c = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt Dummy in
  let zero =
    if is_real then T_int.mk_real "0.0" Dummy
    else T_int.zero Dummy in
  List.map xys ~f:(fun ((x, xs), (y, ys)) ->
      match xs with
      | T_int.SInt ->
        int_template (Term.mk_var x xs Dummy,
                      Term.mk_var y ys Dummy)
      | T_int.SReal ->
        real_template (Term.mk_var x xs Dummy,
                       Term.mk_var y ys Dummy)
      | _ -> failwith "can not happen"
    )
  |> (fun xyz ->
      let xs, ys = List.unzip xyz in
      let xs = (T_int.mk_sum xs c Dummy) in
      let ys = (T_int.mk_sum ys c Dummy) in
      let xs_gt_yt = Formula.mk_atom (T_int.mk_gt xs ys Dummy) Dummy in
      let ys_geq_zero = Formula.mk_atom (T_int.mk_geq ys zero Dummy) Dummy in
      Formula.mk_and xs_gt_yt ys_geq_zero Dummy
    )


let gen_atomic_template gen_arithmetic_template params =
  let params, is_real = preprocess params in
  let bool_params, arithmetic_params =
    Logicutil.div_params params
      (function (_, T_bool.SBool) -> true | _ -> false)
  in
  let rec aux: (Ident.tvar * Sort.t) list -> Formula.t = function
    | [] -> gen_arithmetic_template arithmetic_params is_real
    | (x, sort) :: xs -> begin
        assert (sort = T_bool.SBool);
        let phi1 = Formula.mk_and
            (Formula.var x)
            (aux xs)
            Dummy
        in
        let phi2 = Formula.mk_and
            (Formula.mk_neg (Formula.var x) Dummy)
            (aux xs)
            Dummy in
        Formula.mk_or phi1 phi2 Dummy
      end
  in
  aux bool_params

let gen_dnf_template params conj disj =
  List.range ~stride:1 0 disj
  |> List.map
    ~f:(fun _ ->
        List.range ~stride:1 0 conj
        |> List.map
          ~f:(fun _ -> gen_atomic_template gen_arithmetic_invariant_template params)
        |> fun conj -> Formula.and_of conj Dummy
      )
  |> fun disj -> Formula.or_of disj Dummy

let gen_linear_rf params =
  gen_atomic_template gen_arithmetic_well_founded_template params

let gen_candidates map (templates:t list) =
  List.map templates ~f:(fun ((pvar, params), phi) ->
      ((pvar, params), Formula.subst map phi)
    )


let add (t, s) (t', s') = let open Ast.Logic in (T_int.mk_add t t' Dummy, T_int.mk_add s s' Dummy)
let sub (t, s) (t', s') = let open Ast.Logic in (T_int.mk_sub t t' Dummy, T_int.mk_sub s s' Dummy)
let geq (t, s) = let open Ast.Logic in Formula.mk_atom (T_int.mk_geq t s Dummy) Dummy

let zip_type_number tvars sorts terms =
  let rec zip_type_number tvars sorts terms res =
    match sorts, tvars, terms with
    | [], _, _ -> res
    | T_bool.SBool::sorts, _::tvars, _::terms ->
      zip_type_number tvars sorts terms res
    | T_int.SInt::sorts, tvar::tvars, term::terms
    | T_int.SReal::sorts, tvar::tvars, term::terms ->
      zip_type_number tvars sorts terms ((tvar,term)::res)
    | _ -> assert false
  in
  zip_type_number tvars sorts terms []

let mk_var_bool tvar =
  let atm_bool = Atom.mk_true Dummy in
  T_bool.mk_eq
    tvar
    (Term.mk_funapp (T_bool.Formula (Formula.mk_atom atm_bool Dummy)) [] Dummy)
    Dummy
  |>  fun atm -> Formula.mk_atom atm Dummy

let mk_bool_qualifier_set tvars sorts =
  List.fold_left ~f:(fun quals (tvar, sort) ->
      match sort with
      | T_bool.SBool -> Set.Poly.add quals (mk_var_bool tvar)
      | _ -> quals)
    ~init:Set.Poly.empty @@ List.zip_exn tvars sorts

let gen_octagon_half_spaces sorts examples =
  let open Ast.Logic in
  let examples = examples |> Set.Poly.to_list in
  let params = params_of_sorts sorts in
  let tvars =
    List.map params ~f:(fun (id, sorts) -> Term.mk_var id sorts Dummy) in
  let rec tail_after_s s = function
    | [] -> []
    | s'::ls when s = s'-> ls
    | _::ls -> tail_after_s s ls
  in
  let neg (t, s) =
    (T_int.mk_neg t Dummy, T_int.mk_neg s Dummy) in
  let gen_unit seeds acc  =
    List.fold_left seeds ~init:acc ~f:(fun acc s -> s::(neg s)::acc) in
  let gen_plus seeds acc  =
    List.fold_left
      ~f:(fun acc s ->
          List.fold_left ~f:(fun acc' s' -> (add s s')::(neg(add s s'))::acc')
            (tail_after_s s seeds) ~init:acc
        ) seeds ~init:acc in
  let gen_minus seeds acc =
    List.fold_left
      ~f:(fun acc s ->
          List.fold_left ~f:(fun acc' s' -> (sub s s')::(neg(sub s s'))::acc')
            (tail_after_s s seeds) ~init:acc
        ) seeds ~init:acc in
  let bool_quals = mk_bool_qualifier_set tvars sorts in
  List.fold_left
    examples
    ~f:(fun acc (_, terms) ->
        let seeds = zip_type_number tvars sorts terms in
        gen_unit seeds acc
        |> gen_plus seeds
        |> gen_minus seeds
      ) ~init:[]
  |> List.map ~f:geq
  |> fun phis -> params, List.fold_left ~f:(fun acc phi -> Set.Poly.add acc phi) ~init:bool_quals phis

let gen_octahedron_half_spaces sorts examples =
  let open Ast.Logic in
  let examples = examples |> Set.Poly.to_list in
  let rec inner seeds res =
    match seeds with
    | [] -> [res]
    | hd::tl ->
      let pos  = inner tl (add res hd) in
      let neg  = inner tl (sub res hd) in
      let zero = inner tl res in
      pos @ neg @ zero
  in
  let params = params_of_sorts sorts in
  let tvars = List.map params ~f:(fun (id, sorts) -> Term.mk_var id sorts Dummy) in
  let bool_quals = mk_bool_qualifier_set tvars sorts in
  List.fold_left ~f:(fun acc (_, terms) ->
      let seeds = zip_type_number tvars sorts terms in
      (inner seeds (T_int.zero Dummy, T_int.zero Dummy)) @ acc
    ) ~init:[] examples
  |> List.map ~f:geq
  |> fun phis -> params, List.fold_left ~f:(fun acc phi -> Set.Poly.add acc phi) ~init:bool_quals phis

let gen_half_spaces sorts examples =
  let config = !Fptprover.Global.config in
  match config.qualifier_domain with
  | Config.Octagon ->
    Fptprover.Debug.print "********* Octagon **************";
    gen_octagon_half_spaces sorts examples
  | Config.Octahedron ->
    Fptprover.Debug.print "********* Octahedron ***********";
    gen_octahedron_half_spaces sorts examples


let str_of_qualifiers phis =
  let rec inner cnt qs =
    if cnt = 0 then "...." else
      match qs with
      | [] -> ""
      | q::[] -> "\n" ^ Convert.PrinterHum.str_of_formula q
      | q::qs -> "\n" ^ Convert.PrinterHum.str_of_formula q ^ ";" ^ (inner (cnt-1) qs)
  in "[" ^ inner 100 phis ^ "]"

let get_default_qualifiers cs =
  List.fold_left
    ~f:(fun acc -> function
        | Constraint.WellFounded _ -> acc
        | Constraint.Formula phi ->
          let atomics, papps =
            Formula.atoms phi
            |> Set.Poly.to_list
            |> List.fold_left
              ~f:(fun (atmics, papps) a ->
                  if Atom.is_symapp a then a::atmics, papps
                  else if Atom.is_varapp a then atmics, a::papps
                  else atmics, papps)
              ~init:([], [])
          in
          let papp_ftv_lst = List.map ~f:(fun a -> let ftv = Atom.get_ftv a in (a, ftv)) papps in
          List.fold_left ~f:(fun acc atomic ->
              let ftv = Atom.get_ftv atomic in
              List.fold_left ~f:(fun acc (pa, pftv) ->
                  if not (Set.Poly.is_empty ftv)
                  && Set.Poly.equal (Set.Poly.union ftv pftv) pftv
                  then (pa,atomic)::acc else acc) ~init:acc papp_ftv_lst
            ) ~init:acc atomics
      )
    ~init:[]
    cs
  |> List.group ~break:(fun (pa1,_) (pa2,_) ->
      match pa1, pa2 with
      | Atom.App(Predicate.Var(pvar1, _), _, _),
        Atom.App(Predicate.Var(pvar2, _), _, _) -> Ident.pvar_compare pvar1 pvar2 <> 0
      | _, _ -> assert false
    )
  |> List.map ~f:(fun lst ->
      let pvar, sorts =
        match List.hd lst with
        | None -> failwith "each group must contains at least one term"
        | Some (pred, _) -> begin
            match pred with
            | Atom.App (Predicate.Var (pvar, sorts), _, _) -> pvar, sorts
            | _ -> assert false
          end
      in
      let terms =
        List.map ~f:(fun (v, s) -> Term.mk_var v s Dummy) @@ params_of_sorts sorts
      in
      pvar, Set.Poly.of_list @@ List.map lst
        ~f:(fun (pa, atomic) ->
            match pa with
            | Atom.App (_, terms', _) ->
              let tvars = List.map ~f:(function
                  | Term.Var (tv, _, _) -> tv
                  | _ -> assert false) terms' in
              Formula.mk_atom (Atom.subst (List.zip_exn tvars terms
                                           |> Map.Poly.of_alist_exn) atomic) Dummy
            | _ -> assert false))

