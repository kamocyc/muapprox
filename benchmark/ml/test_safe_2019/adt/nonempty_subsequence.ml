
let rec fold_right f l accu =
  match l with
  | [] -> accu
  | a::l -> f a (fold_right f l accu)

let rec nonempty_subsequences l =
  match l with
  | [] -> []
  | x::xs ->
      let f ys r = ys :: (x :: ys) :: r in
      [x] :: fold_right f [] (nonempty_subsequences xs)

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let rec assert_nonempty = function
  | [] -> assert false
  | _ -> ()

let rec map f = function
  | [] -> []
  | x::l -> f x :: map f l

let main l = map assert_nonempty (nonempty_subsequences l)

