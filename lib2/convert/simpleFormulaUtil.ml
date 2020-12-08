open Ast
open Ast.SimpleFormula

let rec string_of fml =
  if is_and fml then
    let fmls = let_and fml in
    Printf.sprintf "/\\[%s]"
      (List.map string_of fmls |> String.concat "; ")
  else if is_or fml then
    let fmls = let_or fml in
    Printf.sprintf "\\/[%s]"
      (List.map string_of fmls |> String.concat "; ")
  else if is_forall fml then
    let bounds, fml = let_forall fml in
    Printf.sprintf "forall %s. %s"
      (PrinterHum.str_of_params bounds)
      (string_of fml)
  else if is_exists fml then
    let bounds, fml = let_exists fml in
    Printf.sprintf "exists %s. %s"
      (PrinterHum.str_of_params bounds)
      (string_of fml)
  else if is_top fml then
    "true"
  else if is_bot fml then
    "false"
  else if is_app fml then
    let pvar, args = let_app fml in
    Printf.sprintf "%s(%s)"
      (Ident.name_of_pvar pvar)
      (String.concat "," (List.map PrinterHum.str_of_term args))
  else if is_cond fml then
    PrinterHum.str_of_formula (formula_of fml)
  else
    assert false
