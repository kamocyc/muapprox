
let pred f k = f (fun r -> if r <= 0 then k 0 (fun k -> k (r - 1)) else k 1 (fun k -> k (r - 1)))

let rec loop f k =
  f (fun b g ->
    if b = 0 then k 0
    else loop (pred g) k
  )

let rec times n m k =
  if m <= 0
  then k ([0], 0)
  else times n (m - 1) (fun (acc, r) -> k ((n + r)::acc, n + r))

let pred' f k = f (fun (acc, r) -> if r <= 0 then k 0 (fun k -> k (r - 1)) else k 1 (fun k -> k (r - 1)))

let rec init n = if n < 0 then init (n + 1) else pred' (times n n)

(* このような場合、再帰回数の情報を得るのが非常に難しい *)
(* ナイーブには、nをスコープにある関数でなんとかするものを合成する？それで解けるのか？ *)
let () =
  let n = read_int () in
  
  (* 使わない値はunit *)
  let aa = init
    n (* int *)
    (fun a b -> b (fun c ->
      loop (fun f -> f a b) (fun _ -> ())
    ) ) in
  
  (fun k -> k (init n))
  (fun f -> loop f (fun _ -> ()))
  
let zero : (unit -> unit) -> unit -> unit = fun f -> fun x -> x
let one : (unit -> unit) -> unit -> unit = fun f -> fun x -> f x

(* ここからうまく情報を取り出す？ *)

