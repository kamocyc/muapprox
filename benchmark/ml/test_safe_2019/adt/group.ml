
let rec span_eq (p: int) xs = match xs with
  | [] -> [], []
  | x::xs' when p = x -> let ys,zs = span_eq p xs' in x::ys, zs
  | x::xs' -> ([], xs)

(* group [1;1;3;2;2;1] = [[1;1];[3];[2;2];[1]] *)
let rec group xs = match xs with
  | [] -> []
  | x::xs ->
      let ys, zs = span_eq x xs in
      (x :: ys) :: group zs

let rec length = function
  | [] -> 0
  | _::l -> 1 + length l

let rec assert_nonempty = function
  | [] -> assert false
  | _ -> ()

let rec map f = function
  | [] -> []
  | x::l -> f x :: map f l

let main l = map assert_nonempty (group l)

