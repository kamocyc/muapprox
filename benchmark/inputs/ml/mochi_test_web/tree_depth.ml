type tree = Leaf | Node of tree * tree

let max x y = if x > y then x else y

let rec depth = function
    Leaf -> 0
  | Node(t1,t2) -> 1 + max (depth t1) (depth t2)

let rec make_tree () =
  if Random.bool ()
  then Leaf
  else Node(make_tree(), make_tree())

let main (n:int) = assert (depth (make_tree()) >= 0)
