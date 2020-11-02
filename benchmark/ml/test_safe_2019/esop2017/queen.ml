
let rec dotsPrint n = if n = 0 then () else begin print_string "."; dotsPrint (n-1) end

let queenPrint size n queenArray =
  let get i n map = map i in

  let rec aux row = begin
      if row = size then () else
        begin
          assert (0 <= row);
          let m = get row n queenArray in
          dotsPrint(m-1); print_string "Q"; dotsPrint(size - m); print_string "\n"; aux (row + 1)
        end
    end
  in
  aux(0); print_string "\n"


let rec loop row size n queenArray =
let test j n queenArray =
  let get i n map = map i in
  assert (0 <= j);
  let qj = get j n queenArray in
  let rec aux i =
    if i < j then
      let () = assert (0 <= i) in
      let qi = get i n queenArray in
      if qi = qj then false else if abs(qj - qi) = j - i then false else aux (i+1)
    else true
  in aux 0
in
  let get i n map = map i in
  let update i x n map = fun j -> if i = j then x else map j in

  let assign n queenArray i j =
    update i j n queenArray
  in
  assert (0 <= row);
  let next = get row n queenArray + 1 in
  if next > size then
    let queenArray = assign n queenArray row 0 in
    if row = 0 then () else loop (row-1) size n queenArray
  else
    let queenArray = assign n queenArray row next in
    if test row n queenArray then
      if (row+1) = size then begin queenPrint size n queenArray; loop(row) size n queenArray end else loop(row+1) size n queenArray
    else loop row size n queenArray

let main size =
  let make_vect n s = fun i -> s in

  let queenArray = make_vect size 0 in
  if size > 0 then
    loop(0) size size queenArray
