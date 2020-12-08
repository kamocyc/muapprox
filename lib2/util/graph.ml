type attribute = {is_visited: bool; number: int}

let print_attribute attr =
  Array.iter (fun a -> print_int a.number; print_string ",") attr; print_endline ""

let rev graph =
  let n = Array.length graph in
  let graph' = Array.make_matrix n n 0 in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if graph.(i).(j) = 1 then graph'.(j).(i) <- 1
    done
  done; graph'

let mk_graph n = let graph = Array.make_matrix n n 0 in graph

let left (l, _) = l
let visit ar v = ar.(v) <- {ar.(v) with is_visited = true}
let is_visited ar v = ar.(v).is_visited
let set_ct ar v n = ar.(v) <- {ar.(v) with number = n}
let reset_visited attr = Array.iteri (fun i _ -> attr.(i) <- {attr.(i) with is_visited = false}) attr
let neighbors graph v = graph.(v)
                        |> Array.mapi (fun i a -> (i, a))
                        |> Array.to_list |> List.filter (fun (_, a) -> a = 1)
                        |> List.map (fun (i,_) -> i)
let connect graph a b = graph.(a).(b) <- 1
let can_reach graph a b = graph.(a).(b) = 1

let max_ (x1, y1) (x2, y2) = if y1 < y2 then (x2, y2) else (x1, y1)

let scc_of graph : int list list =
  let ct = let ct = ref 0 in fun () -> ct := !ct + 1; !ct in
  let n = Array.length graph in
  let attribute = Array.make n {is_visited = false; number = -1} in
  let rec numbering attr v =
    visit attr v;
    for i = 0 to n - 1 do
      if can_reach graph v i && not (is_visited attr i) then numbering attr i
    done;
    set_ct attr v (ct ())
  in
  let mk_sc graph (attr : attribute array) =
    let biggest (attr: attribute array) =
      let ls = Array.mapi (fun i a -> (i, a.number)) attr |> Array.to_list in
      match List.filter (fun (i, _) -> not @@ is_visited attr i) ls with
      | [] -> None
      | ls -> List.sort (fun (_, n1) (_, n2) -> compare n2 n1) ls
              |> List.hd |> (fun (i,_) -> Some i)
    in
    let rec dfs acc v =
      visit attr v;
      match List.filter (fun v -> not @@ is_visited attr v) (neighbors graph v) with
      | [] -> v::acc
      | l::_ -> dfs (v::acc) l
    in
    let rec inner res () =
      match biggest attr with
      | None -> res
      | Some v -> inner ((dfs [] v) :: res) ()
    in inner [] ()
  in
  numbering attribute 0;
  reset_visited attribute;
  let graph' = rev graph in mk_sc graph' attribute


(* test *)
(*
let print_list str_of ls =
  let rec inner = function | [] -> () | l::ls -> Printf.printf "%s;" (str_of l); inner ls in
  print_string "["; inner ls; print_string "]"

let print_graph g =
  Array.iteri (fun i _ -> print_string "("; print_int i;
                          print_string ","; print_list string_of_int (neighbors g i);
                          print_string ") ") g

let test () =
  let g = mk_graph 4 in
  let connect = connect g in
  connect 0 1; connect 1 2; connect 2 0; connect 2 3;
  List.iter (fun l -> print_list string_of_int l; print_endline "") @@ scc_of g
*)
