
let rec mean xs =
  let rec f = function
    | [] -> assert false
    | [n] -> (1,n)
    | n::ns -> let (k,m) = f ns in (k+1, n+m)
  in
    let (k,n) = f xs in n / k

let main xs = if xs <> [] then let _ = mean xs in ()

