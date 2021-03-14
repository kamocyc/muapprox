
let list_product l1 l2 =
  List.map (fun e1 -> List.map (fun e2 -> (e1, e2)) l2) l1
  |> List.flatten

let rec merge_and_unify comp l1 l2 =
  match (l1, l2) with
    (_,[]) -> l1
  | ([], _)->l2
  | (x::l1',y::l2') -> 
        let c = comp x y in
         if c=0 then x::(merge_and_unify comp l1' l2')
         else if c<0 then x::(merge_and_unify comp l1' l2)
         else y::(merge_and_unify comp l1 l2');;
let rec merge_and_unify_list comp ll =
  List.fold_left
  (fun l1 l2 -> merge_and_unify comp l1 l2)
  [] ll

let upto m =
  let rec go m = if m = 0 then [0] else m :: (go (m - 1)) in    
  go m |> List.rev

let contains_duplicates ls = (List.length @@ List.sort_uniq compare ls) <> List.length ls
