open Hflmc2_syntax
open Print
open Core

let fmt_string s = fun fmt () -> Fmt.string fmt s

(*
  * nu-HFL(Z)はcall-by-name相当だが、OCamlはcall-by-valueであるため、対応が取れていない（また、引数が無い再帰述語があるときにOCamlでエラーになる）
  * OCamlで無限ループだが、nu-HFL(Z)では全体の値がfalseになることはある。関数抽象の中の式の型はPred型であることは保証されているので、関数の引数の型がpred型になるとき (fully-appliedされるとき) のみthunkにすればよいはず
    * その場合、型の整合性と保つために、型推論で再記述後の最後のunitがどこで現れるかを知る必要があるはず（あるいはオーバーヘッドが大きそうだが、全てのbool型をunit->bool型に変換する？）
*)
let convert_nu_hflz_to_program_with_exception ppf hes =
  let exn_name = "E" in
  let id ppf id =
    Fmt.pf ppf "%s" (Id.to_string id |> String.lowercase) in
  let formula = gen_formula_ void_ (ignore_prec id) Prec.zero in
  let arith_ prec ppf a = gen_arith_ (ignore_prec id) prec ppf a in
  let rec go prec ppf phi = match phi with
    | Hflz.Bool true ->
      Fmt.string ppf "true"
    | Bool false ->
      show_paren (prec > Prec.app) ppf "%s"
        ("raise " ^ exn_name)
    | Pred (pred, as') ->
      show_paren (prec > Prec.abs) ppf "@[<1>if@ %a@ then@ true@ else@ raise %s@]"
        formula (Formula.Pred(pred, as'))
        exn_name
    | And (Or ((Pred _) as p1, p2), Or ((Pred (pred, as')) as p1', p3)) when Stdlib.(=) p1 (Hflz.negate_formula p1') ->
      show_paren (prec > Prec.abs) ppf "@[<1>if@ %a@ then@ %a@ else@ %a@]"
        formula (Formula.Pred(pred, as'))
        (go Prec.abs) p2
        (go Prec.abs) p3
    | Or (And ((Pred (pred, as')) as p1, p2), And ((Pred _) as p1', p3)) when Stdlib.(=) p1 (Hflz.negate_formula p1') ->
      show_paren (prec > Prec.abs) ppf "@[<1>if@ %a@ then@ %a@ else@ %a@]"
        formula (Formula.Pred(pred, as'))
        (go Prec.abs) p2
        (go Prec.abs) p3
    | Or (p1, p2) ->
      let result = go_ors prec ppf phi in
      if not result then
        show_paren (prec > Prec.abs) ppf "@[<1>try@ %a@ with@ %s@ ->@ %a@]"
          (go Prec.abs) p1 exn_name (go Prec.abs) p2
    | And (p1, p2) ->
      show_paren (prec > Prec.abs) ppf "@[<1>if@ Random.bool ()@ then@ %a@ else@ %a@]"
        (go Prec.abs) p1 (go Prec.abs) p2
    | Forall (x, p1) ->
      show_paren (prec > Prec.abs) ppf "@[<1>let@ %a =@ Random.int 0 in@ %a@]"
        id x (go Prec.abs) p1
    | App (p1, p2) ->
      show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
        (go Prec.app) p1
        (go Prec.(succ app)) p2
    | Arith a ->
      arith_ prec ppf a
    | Abs (x, p1) ->
      show_paren (prec > Prec.abs) ppf "@[<1>fun (%a:%a) ->@,%a@]"
        id x
        simple_argty x.Id.ty
        (go Prec.abs)
        p1
    | Var x -> Fmt.pf ppf "%a" id x
    | Exists _ -> assert false
  and go_ors prec ppf phi =
    let rec agg_ors phi = match phi with
      | Hflz.Or (p1, p2) ->
        agg_ors p1 @ agg_ors p2
      | _ -> [phi]
    in
    let ors = agg_ors phi in
    let preds, others =
      List.partition_tf
        ~f:(fun e ->
          match e with 
          | Pred _ -> true
          | _ -> false
        )
        ors in
    let fmt_formula ppf f = match f with
      | Hflz.Pred (pred, as') ->
        formula ppf (Formula.Pred(pred, as'))
      | _ -> assert false
    in
    let format_sub a b =
      show_paren (prec > Prec.abs) ppf "@[<1>if@ %a@ then@ true@ else@ %a@]"
        (Fmt.list ~sep:(fmt_string " || ") fmt_formula) preds
        a b
    in
    if List.length preds >= 2 then (
      (match others with
      | [] ->
        format_sub Fmt.string ("raise " ^ exn_name)
      | [other] ->
        format_sub (go Prec.abs) other
      | others ->
        let others =
          let rec go o = match o with
            | [x] -> x
            | x::xs -> Hflz.Or (x, go xs)
            | [] -> assert false
          in
          go others in
        format_sub (go Prec.abs) others);
      true
    ) else false
  in
  let go_arg ppf arg =
    Fmt.pf ppf "(%a: %a)"
      id arg
      simple_argty arg.Id.ty
  in
  let go_rule ppf rule =
    let {Hflz.var; body; fix} = rule in
    let args, body = Hflz.decompose_abs body in
    assert (Stdlib.(=) fix Fixpoint.Greatest);
    Fmt.pf ppf "@[<2>%a@ %a@ : bool =@ %a@]"
      id var
      (Fmt.list ~sep:(fmt_string " ") go_arg) args
      (go Prec.abs) body in
  let (entry, rules) = hes in
  Fmt.pf ppf "@[<v>exception E\nlet rec@ %a@ let main =@ %a@]"
    (Fmt.list ~sep:(fmt_string "\nand ") (go_rule)) rules
    (go Prec.abs) entry
