
open Hflmc2_util

(******************************************************************************)
(* Options                                                                    *)
(******************************************************************************)

let hes = ref (Obj.magic())
let no_inlining = ref (Obj.magic())
let oneshot = ref (Obj.magic())
let no_approx_mu = ref (Obj.magic())
let timeout = ref (Obj.magic())
let print_for_debug = ref (Obj.magic())
let no_backend_inlining = ref (Obj.magic())
let no_separate_original_formula_in_exists = ref (Obj.magic())
let solver = ref (Obj.magic())

(******************************************************************************)
(* Parser                                                                     *)
(******************************************************************************)

let set_ref ref x = ref := x

type params =
  { input : string list [@pos 0] [@docv "FILE"]
  
  ; hes : bool [@default false]
  (** Read hes file format **)

  (* Preprocess *)
  ; no_inlining : bool [@default false]
  (** Disable inlining *)

  ; no_backend_inlining : bool [@default false]
  (** Disable inlining in a backend solver*)
  
  ; oneshot : bool [@default false]
  
  ; no_approx_mu : bool [@default false]
  (** Do not perform approximation of mu and exists. This may cause wrong verification result **)
    
  ; timeout : float [@default 240.0]
  (** Timeout for a backend solver **)
  
  ; print_for_debug : bool [@default true]
  
  ; no_separate_original_formula_in_exists : bool [@default true]
  (** If specified, when approximating exists do not create new predicate that reduces the formula size **)
  
  ; solver : string [@default "katsura"]
  (** Choose background mu-only-CHC solver. Available: katsura, iwayama *)
  }
  [@@deriving cmdliner,show]

let set_up_params params =
  set_ref no_inlining              params.no_inlining;
  set_ref no_approx_mu             params.no_approx_mu;
  set_ref oneshot                  params.oneshot;
  set_ref hes                      params.hes;
  set_ref timeout                  params.timeout;
  set_ref print_for_debug          params.print_for_debug;
  print_endline "no_separate_original_formula_in_exists";
  set_ref no_separate_original_formula_in_exists params.no_separate_original_formula_in_exists;
  set_ref no_backend_inlining      params.no_backend_inlining;
  set_ref solver                   params.solver;
  params.input

(******************************************************************************)
(* Term                                                                       *)
(******************************************************************************)

let term_set_up_params () =
  Cmdliner.Term.(const set_up_params $ params_cmdliner_term ())

(* Log *)
let term_setup_log () =
  (*{{{*)
  let setup style_renderer level =
    Format.set_margin 100;
    Fmt_tty.setup_std_outputs ?style_renderer ();
    let pp_header ppf (src, level, header) =
      let src_str =
        if Logs.Src.(equal src Logs.default)
        then None
        else Some (Logs.Src.name src)
      in
      let level_str, style = match (level : Logs.level) with
        | App     -> "App"     , Logs_fmt.app_style
        | Error   -> "Error"   , Logs_fmt.err_style
        | Warning -> "Warning" , Logs_fmt.warn_style
        | Info    -> "Info"    , Logs_fmt.info_style
        | Debug   -> "Debug"   , Logs_fmt.debug_style
      in
      let (<+) x y = match x with None -> y | Some x -> x ^ ":" ^ y in
      let (+>) x y = match y with None -> x | Some y -> x ^ ":" ^ y in
      let str = src_str <+ level_str +> header in
      Fmt.pf ppf "@[<v 2>[%a]@ @]" Fmt.(styled style string) str
    in
    let reporter =
      { Logs.report = fun src level ~over k msgf ->
          let k _ = over (); k () in
          msgf @@ fun ?header ?tags:_ fmt ->
            let ppf = Fmt.stdout in
            Format.kfprintf k ppf ("%a@[" ^^ fmt ^^ "@]@.")
              pp_header (src, level, header)
      }
    in
    Logs.set_reporter reporter;
    Logs.set_level level
  in
    Cmdliner.Term.(const setup $ Fmt_cli.style_renderer () $ Logs_cli.level ())
(*}}}*)

type input = [`File of string | `Stdin]
let parse ?argv () : input option =
  let term () =
    let open Cmdliner.Term in
    const (fun _ file -> file)
      $ term_setup_log () (* NOTE order matters *)
      $ term_set_up_params ()
  in match Cmdliner.Term.(eval ?argv (term (), info "muapprox")) with
  | `Ok [] -> Some `Stdin
  | `Ok [file] -> Some (`File file)
  | `Ok _ -> Fn.todo ~info:"multiple input files" ()
  | _     -> None

