(*let test j n queenArray =
  let rec abs r = if r >= 0 then r else - r in
  let get i n map = map i in
  let qj = get j n queenArray in
  let rec aux i =
    if i < j then
      let qi = get i n queenArray in
      if qi = qj then false else if abs(qj - qi) = j - i then false else aux (i+1)
    else true
  in aux 0
 *)
let rec loop row size n queenArray =
  let assign n queenArray i j =
    let update i x n map = map i; fun j -> if i = j then x else map j in
    update i j n queenArray
  in
  let get i n map = map i in
  let next = get row n queenArray + 1 in
  if next > size then
    let queenArray = assign n queenArray row 0 in
    if row = 0 then () else loop (row-1) size n queenArray
  else
    let queenArray = assign n queenArray row next in
    if Random.bool() then
      if (row+1) = size then begin (*queenPrint size n queenArray;*) loop(row) size n queenArray end else loop(row+1) size n queenArray
    else loop row size n queenArray

let main size =
  let make_vect n s = fun i -> assert (0 <= i && i < n); s in
  let queenArray = make_vect size 0 in
  if size > 0 then
    loop(0) size size queenArray
