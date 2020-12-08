open Bes
open Core open Core.Poly

type t = dnf_expression

let str_of_extbool = function
  | `True     -> "1"
  | `False    -> "0"
  | `Dontcare -> "x"

let gen_solver (): dnf_expression = []

let add_positive_s str solver = (`True::(dnf_minterm_of_string str))::solver

let add_negative_s str solver = (`False::(dnf_minterm_of_string str))::solver

let is_required e = (List.hd_exn e) = `True

let to_function dnf_exp =
  List.filter dnf_exp ~f:is_required
  |> List.map ~f:(fun dnf_min -> List.tl_exn dnf_min)

let synthesize solver =
  (*  Fptprover.Debug.print @@
      "given problem:" ^ (string_of_dnf_expression solver); *)
  optimize Qmc_PetricksMethod solver |> to_function

let filter op_neg ls dnf_min =
  assert (List.length ls = List.length dnf_min);
  let z = List.zip_exn ls dnf_min in
  List.fold_left
    ~f:(fun acc -> function
        | (l, `True) -> l::acc
        | (l, `False) -> (op_neg l)::acc
        | (_, `Dontcare) -> acc) ~init:[] z

let filter_ op_neg ls dnf_exp =
  let filter = filter op_neg ls in
  List.map ~f:(fun dnf_min -> filter dnf_min) dnf_exp

let test () =
  let conj ls = List.fold_left
      ~init:""
      ~f:(fun acc s -> Printf.sprintf "%s /\\ %s " acc s) ls in
  print_endline "BooleanF Test";
  gen_solver ()
  |> add_positive_s "001"
  |> add_positive_s "100"
  |> add_positive_s "101"
  |> add_negative_s "010"
  |> add_negative_s "110"
  |> synthesize
  |> (fun func ->
      print_dnf_expression func;
      print_endline "result";
      List.iter ~f:(fun d -> print_endline (conj d))
        (filter_ (fun x -> Printf.sprintf "(not %s)" x)
           ["q_a";"q_b";"q_c"] func)
    )
