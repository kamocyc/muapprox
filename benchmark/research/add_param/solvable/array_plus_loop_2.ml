type arr = (int->int->(int->unit)->unit)

let make_array (s1:int) (k:int->arr->unit) = k s1 (fun (i:int) (s1:int) (k':int->unit) -> k' 0)
let update (s1:int) (ar:arr) (i:int) (x:int) (s2:int) (k:int->arr->unit) =
  k s1 (fun j s1 k' -> if j = i then k' x else ar j s1 k')
  
(* let check ar i x k =
  ar i (fun r -> k (r = x)) *)

let pred (s1:int) (ar:arr) (i:int) (s1:int) k =
  ar i s1 (fun x ->
    update s1 ar i (x - 1) s1 k
  )
  
let rec loop (s1:int) (ar:arr) (i:int) (j:int) (s1:int) k =
  ar i s1 (fun x ->
      ar j s1 (fun y ->
        if x + y <= 0 then k 0
        else pred s1 ar 0 s1 (fun s1 ar -> loop s1 ar 0 1 s1 k)
      )
    )

let main s1 ar s1 k =
  loop s1 ar 0 1 s1 (fun r -> k r)
    
let () =
  let s1 = 0 in
  let x = read_int () in
  let y = read_int () in
  make_array s1 (fun s1 ar ->
    update s1 ar 0 x s1 (fun s1 ar ->
      update s1 ar 1 y s1 (fun s1 ar ->
        main s1 ar s1 (fun r -> print_int r)     
      )
    )
  )


  