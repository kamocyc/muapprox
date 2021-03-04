
let pred f k = f (fun r -> if r <= 0 then k 0 (fun (a: int) k -> k (r - 1)) else k 1 (fun (a: int) k -> k (r - 1)))

let rec loop
    (f : ((int -> (int -> (int -> unit) -> unit) -> unit) -> unit))
    (k : (int -> unit)) : unit =
  f (fun b g ->
    if b = 0 then k 0
    else loop (pred (g 0)) k
  )

let rec times n m k =
  if m <= 0
  then k 0
  else times n (m - 1) (fun r -> k (n + r))

let pred' f k =
  (* assert (a = 0 || a != 0); *)
  f (fun r -> if r <= 0 then k 0 (fun (a: int) k -> k (r - 1)) else k 1 (fun (a: int) k -> k (r - 1)))

let rec init (n : int): (int -> (int -> (int -> unit) -> unit) -> unit) -> unit
 = if n < 0 then init (n + 1) else pred' (times n n)

(* このような場合、再帰回数の情報を得るのが非常に難しい *)
(* ナイーブには、nをスコープにある関数でなんとかするものを合成する？それで解けるのか？ *)
let () =
  let n = read_int () in
  
  (* 使わない値はunit *)
  let aa = init
    n (* int *) (* l.1 *)
    (fun (a : int) (b : int -> (int -> unit) -> unit) (* l.2  *)->
      let d = read_int () in (* l.3 *)
      b d (fun c -> (* l.4 *)
        loop
          (fun (f : int -> (int -> (int -> unit) -> unit) -> unit) ->
            f a (fun (d': int) -> (* d = d' => *) b d')
          )
          (fun _ -> ())
      )
    ) in
  ()
  (* (fun k -> k (init n))
  (fun f -> loop f (fun _ -> ())) *)

let zero : (unit -> unit) -> unit -> unit = fun f -> fun x -> x
let one : (unit -> unit) -> unit -> unit = fun f -> fun x -> f x

(* ここからうまく情報を取り出す？ *)

(* 
後でちゃんと考える。

int -> (
  a:int -> b:(
    d:int -> (c:int -> 'a) -> 'a
  ) -> 'b
) -> '

dはpositiveの位置にあり、不明
forallで決める必要がある。
ここは、callbackでうまくやる必要がある

 *)