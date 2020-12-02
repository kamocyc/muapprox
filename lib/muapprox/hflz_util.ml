module Hflz = Hflmc2_syntax.Hflz
open Hflz_typecheck
open Hflz

(* 自身に到達可能なノードのみを返す *)
(* 構文的に展開していって、再帰的に参照していなければ、不動点を使う必要はない。 *)
let get_recurring_predicates (hes : Type.simple_ty hes) = 
  let preds = List.mapi (fun i {var; _} -> (i, var)) hes in
  let graph_size = List.length hes in
  let graph = Mygraph.init graph_size in
  (* 参照の依存グラフを作成 *)
  List.iteri
    (fun index {var; body; _} -> 
      fvs body
      |> Hflmc2_syntax.IdSet.to_list
      |> List.filter_map
        (fun v ->
          List.find_opt (fun (_, v') -> Id.eq v' v) preds
        )
      |> List.iter (fun (i', v') -> 
        Mygraph.add_edge index i' graph
      )
    )
    hes;
  (* 自身に到達可能なノードのみを返す *)
  List.filter_map
    (fun (i, var) -> 
      let reachables = Mygraph.reachable_nodes_from ~start_is_reachable_initially:false i graph in
      match List.find_opt (fun n -> n = i) reachables with
      | None -> None
      | Some _ -> Some var
    )
    preds
  