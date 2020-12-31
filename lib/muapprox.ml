module Util        = Hflmc2_util
module Syntax      = Hflmc2_syntax
module Options     = Hflmc2_options

open Util
open Syntax

let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start

let times = Hashtbl.create (module String)
let add_mesure_time tag f =
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let all_start = Unix.gettimeofday ()
let report_times () =
  let total = Unix.gettimeofday() -. all_start in
  let kvs = Hashtbl.to_alist times @ [("total", total)] in
  match List.max_elt ~compare (List.map kvs ~f:(String.length<<<fst)) with
  | None -> Print.pr "no time records"
  | Some max_len ->
      Print.pr "Profiling:@.";
      List.iter kvs ~f:begin fun (k,v) ->
        let s =
          let pudding = String.(init (max_len - length k) ~f:(Fn.const ' ')) in
          "  " ^ k ^ ":" ^ pudding
        in Print.pr "%s %f sec@." s v
      end

let show_result = Muapprox_prover.Status.string_of

let parse file =
  if !Options.hes then (
    let psi =
    match Hes.HesParser.from_file file with
    | Ok hes -> Muapprox_prover.Hflz_convert.of_hes hes
    | Error _ -> failwith "hes_parser" in
    Log.app begin fun m -> m ~header:"hes Input" "%a" Print.(hflz_hes simple_ty_) psi end;
    psi  
  ) else (
    let psi, _ = Syntax.parse_file file in
    Log.app begin fun m -> m ~header:"Input" "%a" Print.(hflz_hes simple_ty_) psi end;
    psi
  )

let get_solve_options () =
  let open Muapprox_prover.Solve_options in
  {
    no_backend_inlining = !Options.no_backend_inlining;
    timeout = !Options.timeout;
    print_for_debug = !Options.print_for_debug;
    oneshot = !Options.oneshot;
    separate_original_formula_in_exists = not !Options.no_separate_original_formula_in_exists;
    solver = get_solver !Options.solver;
    first_order_solver = get_first_order_solver !Options.first_order_solver;
    coe = get_coe !Options.coe;
  }
  
let main file =
  let solve_options = get_solve_options () in
  let psi = parse file in
  (* coefficients's default values are 1, 1 (defined in solve_options.ml) *)
  let coe1, coe2 = solve_options.coe in
  let inlining = not @@ !Options.no_inlining in
  (* for debug *)
  let psi = if inlining then (
    let psi = Syntax.Trans.Simplify.hflz_hes psi inlining in
    Log.app begin fun m -> m ~header:"Simplified" "%a" Print.(hflz_hes simple_ty_) psi end;
    psi
  ) else psi in
  (* TODO: *)
  let s1, _ = Muapprox_prover.check_validity coe1 coe2 solve_options psi in
  s1
  (* TODO: topのpredicate variableの扱い？ *)
  (* let psi, top = Syntax.Trans.Preprocess.main psi in
  match top with
  | Some(top) -> begin
    match Typing.main psi top with  
    | `Sat ->  `Valid
    | `Unsat ->  `Invalid
    | `Unknown -> `Unknown
    | _ -> `Fail
    end
  | None -> print_string "[Warn]input was empty\n";
      `Valid (* because the input is empty *)
 *)
