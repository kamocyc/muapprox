open Hes
open Ast.Logic

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

let optimize hes =
  hes
  |> optimize_formula
  |> InlineExtension.optimize
