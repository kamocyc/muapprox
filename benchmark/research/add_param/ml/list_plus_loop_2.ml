let hd len l k = l 0 k

let (=>) a b = not a || b

let isNil len l k =
  (len = 0 => k 1) && (len != 0 => k 0)

let tl len l k = k (len - 1) (fun i k2 -> l (i + 1) k2)

let len l k = l 0 k

let cons a len l k =
  k (len + 1) (fun i k2 -> (i = 0 => k2 a) && (i != 0 => l (i - 1) k2))

let nil k = k 0 (fun i k -> k 0)

let rec loop len l k =
  hd len l (fun x ->
    tl len l (fun len2 l2 ->
      hd len2 l2 (fun y ->
        (x + y > 0 =>
          nil (fun len3 l3 ->
            cons y len3 l3 (fun len4 l4 ->
              cons (x - 1) len4 l4 (fun len5 l5 ->
                loop len5 l5 k
              )
            )
          )
        ) &&
        (x + y <= 0 => k false)
      )
    )
  )

let sentry =
  let x = read_int () in
  let y = read_int () in
  nil (fun len l ->
    cons y len l (fun len2 l2 ->
      cons x len2 l2 (fun len3 l3 ->
        loop len3 l3 (fun _ -> true)
      )
    )
  )
  