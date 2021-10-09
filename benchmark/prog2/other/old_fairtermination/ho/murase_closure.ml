let event e = print_endline e

let const (x:(int->unit)->unit) k = event "called"; k x

let rec finish k = event "called"; event "a"; finish k

let rec check f_ k =
  if read_int () > 0 then
    f_ (fun x ->
      if x > 0 then k 1 else k 0
    )
  else check f_ k

let pred f_ k =
  f_ (fun x ->
    k (x - 1)
  )

let rec f g k =
  event "called";
  g (fun fn ->
    check fn (fun b ->
      if b = 1 then
        f (const (pred fn)) k
      else finish k
    )
  )

let rec xx g k =
  (* infinite sequence of "called"s is valid because in this point, the state is qa (even priority) *)
  event "called";
  event "a";
  if read_int () > 0 then
    f g k
  else
    xx g k

let () =
  let n = read_int () in
  xx (const (fun k -> k n)) ()
