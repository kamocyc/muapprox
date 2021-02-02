open Hflz_typecheck
open Hflz

let get_dependency_graph (hes : 'a hes_rule list) =
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
  preds, graph
