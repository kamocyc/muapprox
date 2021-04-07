let make_array = (fun (i : int) -> 0)
let update ar (i : int) (x : int) =
  fun j -> if j = i then x else ar j
let check ar (i : int) (x: int) =
  (ar i) = x

let pred ar i =
  let x = ar i in
  update ar i (x - 1)
  
let rec loop ar i j =
  let x = ar i in
  let y = ar j in
  if x + y <= 0 then 0
  else begin
    let ar = pred ar 0 in
    loop ar 0 1
  end

let mmain ar =
  loop ar 0 1

(* input 10 -> output 55 *)
let main () =
  let x = read_int () in
  let y = read_int () in
  let ar = make_array in
  let ar = update ar 0 x in
  let ar = update ar 1 y in
  mmain ar

let () = main () |> print_int
