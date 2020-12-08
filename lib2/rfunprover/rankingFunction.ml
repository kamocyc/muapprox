module rec RankingFunction : sig
  exception InvalidLength
  type t = RankingFunction of int list

  (** constructor *)
  val mk_rfun: int list -> t

  (** destructor *)
  val let_rfun: t -> int list

  val apply: t -> int list -> int
end = struct
  exception InvalidLength
  type t = RankingFunction of int list

  (** constructor *)
  let mk_rfun coes = RankingFunction coes

  (** destructor *)
  let let_rfun = function RankingFunction coes -> coes

  let apply (rfun: t) (args: int list) =
    let rec rep = function
        ([coeconst], []) -> coeconst
      | (coehead :: coetail, xhead :: xtail) -> coehead * xhead + rep (coetail, xtail)
      | _ -> raise @@ InvalidLength
    in
    rep (let_rfun rfun, args)
end

module rec RankingFunctionFinder : sig
  exception Unknown
  exception Unsatisfiable
  (* a1x1 + a2x2 + ... + anxn >= b *)
  type restriction = Restriction of int list
  type t = Finder of int * restriction list ref

  (* constructor *)
  val mk_finder: int -> t

  val add_positive: t -> int list -> unit
  val add_transition: t -> int list -> int list -> unit

  val solve: t -> RankingFunction.t
end = struct
  exception Unknown
  exception Unsatisfiable
  type restriction = Restriction of int list
  type t = Finder of int * restriction list ref

  (* a1x1 + a2x2 + ... + anxn + b > 0 *)
  let mk_rest = function r -> Restriction r
  let mk_finder numargs = Finder (numargs, ref [])

  let let_rests = function Finder (_, rests) -> !rests
  let let_numargs = function Finder (numargs, _) -> numargs
  let let_coes = function Restriction coes -> coes

  let mk_vars finder ctx =
    List.map (fun symbol -> Z3.Expr.mk_const ctx symbol (Z3.Arithmetic.Integer.mk_sort ctx))
    @@ Z3.Symbol.mk_ints ctx @@ Core.List.range 1 @@ let_numargs finder + 1

  let add_rest finder rest = match finder with
      Finder (_, rests) ->
      rests := rest :: !rests

  let add_positive finder args =
    (* TODO: check args len *)
    (* x1a1 + ... + xnan + 1 * b > 0 *)
    let rest = args @ [1] in
    add_rest finder (mk_rest rest)

  let add_transition finder fromargs toargs =
    (* TODO: check args len *)
    add_rest finder
    @@ mk_rest
    (* (x1-x1')a1 + ... + (xn-xn')an + 0 * b > 0 *)
    @@ (List.map (fun (x, y) -> x - y) @@ Core.List.zip_exn fromargs toargs) @ [0]

  let solve finder =
    let ctx = (Z3.mk_context [("model", "true")]) in
    let solver = (Z3.Solver.mk_simple_solver ctx) in
    (* a1, ..., an *)
    let vars = mk_vars finder ctx in
    let zero = (Z3.Expr.mk_numeral_int ctx 0 (Z3.Arithmetic.Integer.mk_sort ctx)) in
    let rec add_rests = function
        [] -> ()
      | rest :: tail ->
        (* a1 * k1 + ... + an * kn + b * k *)
        let expr = Z3.Arithmetic.mk_add ctx
          @@ List.map (fun (a, k) -> Z3.Arithmetic.mk_mul ctx [a; (Z3.Expr.mk_numeral_int ctx k (Z3.Arithmetic.Integer.mk_sort ctx))])
          @@ Core.List.zip_exn vars (let_coes rest) in
        Z3.Solver.add solver [(Z3.Arithmetic.mk_gt ctx expr zero)];
        add_rests tail
    in
    add_rests @@ let_rests finder;
    let status = Z3.Solver.check solver [] in
    if status = Z3.Solver.SATISFIABLE then
      let model = Util.Option.unwrap @@ Z3.Solver.get_model solver in
      let open Smt.Extarithmetic in
      RankingFunction.mk_rfun
      @@ List.map (fun var -> Arithmetic.Integer.get_int @@ Util.Option.unwrap @@ Z3.Model.eval model var false) vars
    else if status = Z3.Solver.UNKNOWN then
      raise Unknown
    else
      raise Unsatisfiable
end
