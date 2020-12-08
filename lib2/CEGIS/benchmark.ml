open Core open Core.Poly
open Ast.Logic

module FormulaAttr : sig
  type fixpoints =
    {mu_positive: int; mu_negative: int; nu_positive: int; nu_negative: int;}
  type t = {ast_size: int; fixpoints: fixpoints; quantifiers: int; nesting_level: int;}
  val mk: Ast.Logic.Formula.t -> t
  val str_of: t -> string
  val csv_of: t -> string
end = struct
  type fixpoints =
    {mu_positive: int; mu_negative: int; nu_positive: int; nu_negative: int;}
  type t = {ast_size: int; fixpoints: fixpoints; quantifiers: int; nesting_level: int;}

  let init =
    {mu_positive = 0; mu_negative = 0; nu_positive = 0; nu_negative = 0}
  let find_fixpoints phi =
    let open Logicutil in
    let rec inner acc =
      function
      | [] -> acc
      | (Predicate.Mu, Pos)::ls ->
        inner {acc with mu_positive = acc.mu_positive + 1} ls
      | (Predicate.Mu, Neg)::ls ->
        inner {acc with mu_negative = acc.mu_negative + 1} ls
      | (Predicate.Nu, Pos)::ls ->
        inner {acc with nu_positive = acc.nu_positive + 1} ls
      | (Predicate.Nu, Neg)::ls ->
        inner {acc with nu_negative = acc.nu_negative + 1} ls
    in inner init @@ all_fixpoints_of_formula phi
  let mk phi =
    {
      ast_size = Formula.ast_size phi;
      fixpoints = find_fixpoints phi;
      quantifiers = Formula.number_of_quantifiers phi;
      nesting_level = Formula.nesting_level phi;
    }

  let str_of_fixpoints attr =
    Printf.sprintf "\t{mupos: %d, muneg: %d, nupos: %d, nuneg: %d}"
      attr.mu_positive attr.mu_negative
      attr.nu_positive attr.nu_negative

  let str_of attr =
    Printf.sprintf "{ast_size: %d, quantifiers: %d, nesting: %d, fixpoints:\n %s}"
      attr.ast_size attr.quantifiers attr.nesting_level (str_of_fixpoints attr.fixpoints)

  let csv_of_fixpoints attr =
    Printf.sprintf "%d, %d, %d, %d"
      attr.mu_positive attr.mu_negative
      attr.nu_positive attr.nu_negative

  let csv_of attr =
    Printf.sprintf "%d, %s, %d, %d"
      attr.ast_size
      (csv_of_fixpoints attr.fixpoints)
      attr.quantifiers
      attr.nesting_level
end

module ConstraintsAttr : sig
  type arity = {max: int; min:int; average:float;}
  type t = {length: int; pvars: int; arity: arity;}
  val mk: Constraint.t list -> t
  val str_of: t -> string
  val csv_of: t -> string
end = struct
  type arity = {max: int; min:int; average:float;}
  type t = {length: int; pvars: int; arity: arity;}

  let arity cs =
    let intmax = 99999999 in
    let ars = Constraint.arities cs in
    let max = List.fold_left ~init:0 ~f:(fun acc a-> max acc a) ars in
    let min = List.fold_left ~init:intmax ~f:(fun acc a -> min acc a) ars in
    let ave =
      let sum = List.fold_left ~init:0 ~f:(fun acc a -> acc + a) ars in
      (float_of_int sum) /. (float_of_int (List.length ars))
    in
    {max = max; min = min; average = ave;}

  let mk cs =
    {length = List.length cs;
     pvars = Constraint.number_of_pvars cs;
     arity = arity cs;}

  let str_of_arity arity =
    Printf.sprintf "{max: %d, min: %d, ave: %f}"
      arity.max arity.min arity.average

  let str_of attr =
    Printf.sprintf " {number_of_cs: %d, number_of_pvars: %d,\n  arity: %s}"
      attr.length
      attr.pvars
      (str_of_arity attr.arity)

  let csv_of_arity arity =
    Printf.sprintf "%d, %d, %f"
      arity.max arity.min arity.average

  let csv_of attr =
    Printf.sprintf "%d, %d, %s"
      attr.length
      attr.pvars
      (csv_of_arity attr.arity)
end

module Attribute : sig
  type t =
    {raw : FormulaAttr.t;
     desugared : FormulaAttr.t;
     constraints : ConstraintsAttr.t;}

  val mk: Ast.Logic.Formula.t -> t
  val str_of: t -> string
  val csv_of: t -> string
end = struct
  type t =
    {raw : FormulaAttr.t;
     desugared : FormulaAttr.t;
     constraints : ConstraintsAttr.t;}

  let mk phi =
    let phi' = Convert.Desugar.of_formula phi in
    (*Printf.printf "phi'@benchmark.ml: %s\n" (Convert.PrinterHum.str_of_formula phi');*)
    let cs = phi |> Convert.Hesutil.hes_of_formula |> Constraint.extract in
    { raw = FormulaAttr.mk phi;
      desugared = FormulaAttr.mk phi';
      constraints = ConstraintsAttr.mk cs;}

  let str_of attr =
    "problem information:\n" ^
    "Raw formula:\n" ^ (FormulaAttr.str_of attr.raw) ^
    "\nDesugared:\n" ^ (FormulaAttr.str_of attr.desugared) ^
    "\nConstraints:\n" ^
    (ConstraintsAttr.str_of attr.constraints)

  let csv_of attr =
    (FormulaAttr.csv_of attr.raw) ^ ", " ^
    (FormulaAttr.csv_of attr.desugared) ^ ", " ^
    (ConstraintsAttr.csv_of attr.constraints) ^ "\n"

end

let preprocess outfile csv =
  if Sys.file_exists outfile = `Yes then csv
  else
    "filename, ast_size, mupos_raw, muneg_raw, "
    ^ "nupos_raw\ nuneg_raw, quantifiers_raw, "
    ^ "nesting_raw, "
    ^ "mupos, muneg, nupos, nuneg, "
    ^ "quantifiers, nesting, "
    ^ "number_of_cs, number_of_pvars, "
    ^ "max_arity, min_arity, ave_arity\n"
    ^ csv

let mk_bench infile outfile phi =
  let attr = Attribute.mk phi in
  let csv = infile ^", " ^ (Attribute.csv_of attr) in
  let csv' = csv |> preprocess outfile in
  let ch = Out_channel.create
      outfile
      ~append:(match Sys.file_exists outfile with
            `Yes -> true | _ -> false ) in
  Out_channel.output_string ch csv';
  Out_channel.close ch
(*  print_endline @@ Attribute.str_of attr *)

let mk_bench_for_psat infile outfile phis =
  let open Ast.Logic in
  let is_linear = List.fold_left
      ~f:(fun acc phi -> acc && (Formula.number_of_pvar_apps false phi) <= 1)
      ~init:true phis in
  let csv = infile ^ ", " ^ (if is_linear then "Linear" else "Non-Linear") ^ "\n" in
  let ch = Out_channel.create outfile ~append:(match Sys.file_exists outfile with `Yes -> true | _ -> false) in
  Out_channel.output_string ch csv;
  Out_channel.close ch

