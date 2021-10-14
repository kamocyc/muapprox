let event s = print_string s

let rec halt u =
  halt u

let check1 x_ k =
  x_ (fun x ->
    if x>0 then k 1 else k 0
  )

let pred x_ k =
  x_ (fun x ->
    k (x - 1)
  )
  
let rec bar x_ k =
  check1 x_ (fun b ->
    if b = 1 then bar (pred x_) k else k x_
  )

let check2 x_ k =
  x_ (fun x ->
    if x<=0 then k 1 else k 0
  )

let rec foo x_ =
  event "foo";
  check2 x_ (fun b ->
    if b = 1 then foo x_ else halt ()
  )

let rec xx flag x_ =
  if flag = 1 then (
    if read_int () > 0 then foo (fun k -> 0)
    else bar x_ (fun r_ ->
      foo r_
    )
  ) else
    xx 1 x_
  
let _ =
  let x = read_int () in
  xx 0 (fun k -> k x)