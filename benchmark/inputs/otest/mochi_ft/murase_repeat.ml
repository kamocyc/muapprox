let event s = print_string s

let rec xx (flag:int) (g:(unit -> int) -> unit) (fx:unit->int):unit =
  if flag = 1 then
    g fx
  else
    xx 1 g fx

let check (fx:unit->int):int =
  let x = fx () in
  if x > 0 then 1 else 0

let pred (fx:(unit->int)) (u:unit): int =
  let x = fx () in
  x - 1

let rec repeat (g:((unit->int)->unit)):unit =
  let v = Random.int 0 in
  xx 0 g (fun u -> v);
  repeat g

let rec f (fx:unit->int):unit =
  let b = check fx in
  if b = 1 then
    f (pred fx)
  else
    event "A"

(* let () =
  repeat f *)

let main = repeat f