let f (x : int -> (int -> (int -> (int -> unit) -> unit) -> unit) -> unit) = ()

let aaa
    (x1_1 : int)
    (x1_2 : int -> (int -> (int -> unit) -> unit) -> unit): unit =
  let x2_1 = 10 in
  x1_2 x2_1 (fun (y3_1 : int) (y3_2 : (int -> unit)) ->
    y3_2 (x2_1 + x2_1)
  )

let () =
  (fun k ->
    let n = read_int () in
    aaa
      n
      (fun (x2_1 : int) (x2_2 : (int -> (int -> unit) -> unit)) ->
        let x3_1 = read_int () in
        x2_2 x3_1 (fun (x4_1 : int) ->
          k x4_1 (fun (y1_1 : int) (y1_2 : int -> (int -> (int -> unit) -> unit) -> unit) ->
            if y1_1 = n then
              y1_2 x2_1 (fun (y3_1 : int) (y3_2 : (int -> unit)) ->
                if x3_1 = y3_1 then
                  y3_2 x4_1
                else assert false
              )
            else assert false
          )
        )
      )
  ) (fun x f ->
    loop f
  )
    
(*   
let () =
  f aaa *)