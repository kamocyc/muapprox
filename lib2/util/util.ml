include Ordinal

let log2 x = log x /. log 2.

let id x = x
let const c () = c

let (>>) f g = fun x -> g (f x)

let (>>=) x f =
  match x with
  | None -> None
  | Some(x) -> f x

let flip f x y = f y x

(** Options *)
module Option = struct
  let unwrap = function
    | Some x -> x
    | None -> raise Not_found

  let map f = function None -> None | Some x -> Some (f x)

  let and_then f = function
    | None -> None
    | Some x -> f x

  let compose x1 x2 =
    match x1, x2 with
    | Some(x), _ -> Some x
    | _, Some(x) -> Some x
    | _, _ -> None
end

let fst (x, _) = x
let snd (_, x) = x

(** Results *)
module Result = struct
  type ('ok, 'err) t =  ('ok, 'err) result

  let and_then f = function
    | Ok x -> f x
    | Error x -> Error x

  let or_then f = function
    | Ok x -> Ok x
    | Error x -> f x

  let map_ok f = function
    | Ok x -> Ok(f x)
    | Error x -> Error x

  let map_err f = function
    | Ok x -> Ok x
    | Error x -> Error (f x)

  let collect_from_list xs =
    let rec aux acc xs = match acc, xs with
      | acc, [] -> Ok(acc)
      | acc, (Ok(x) :: xs) -> aux (x :: acc) xs
      | _, (Error (x) :: _) -> Error x
    in
    aux [] xs
end

module List = struct
  include List

  let rec classify eqrel = function
    | [] -> []
    | x :: xs ->
      let t, f = List.partition (eqrel x) xs in
      (x :: t) :: (classify eqrel f)

  let rec power f = function
    | [] -> [[]]
    | x :: xs ->
      power f xs
      |> List.map (fun ys -> f x |> List.map (fun y -> y :: ys))
      |> List.concat

  let zip_index l =
    Core.List.zip_exn l (List.init (List.length l) id)
end

module LexingHelper = struct
  let update_loc (lexbuf: Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with
        pos_lnum = pos.pos_lnum + 1;
        pos_bol = pos.pos_cnum;
      }

  let get_position_string (lexbuf: Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    Printf.sprintf "%d:%d"
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
end

module Command : sig
  exception Shell_error of string
  val async_command: string -> string list -> in_channel * out_channel * in_channel
  val sync_command: string -> string list -> string list -> string list
  val output_lines: string list -> out_channel -> unit
  val input_lines: in_channel -> string list
end = struct
  exception Shell_error of string

  let output_lines (output : string list) (chan : out_channel) : unit =
    (List.iter (fun line -> output_string chan (line ^ "\n")) output); flush chan

  let rec do_channel_lines (f : string -> 'a) (chan : in_channel) : 'a list =
    try
      let line = input_line chan in
      f line :: do_channel_lines f chan
    with End_of_file -> []

  let input_lines = do_channel_lines (fun x -> x)

  let unlines : string list -> string =
    String.concat "\n"

  let async_command
      (name : string)
      (arguments : string list)
    : (in_channel * out_channel * in_channel) =
    Unix.open_process_full
      (Printf.sprintf "bash -c '%s %s 2>&1'" name (String.concat " " arguments))
      (Unix.environment ())

  let show_commands name arguments input =
    print_endline "show_commands";
    print_endline @@ "name: " ^ name;
    print_endline @@ "arguments: " ^ (String.concat "," arguments);
    print_endline @@ "input: " ^ (String.concat "," input);
    print_endline "===="
    
  let sync_command
      (name : string)
      (arguments : string list)
      (input : string list) : string list =
    show_commands name arguments input;
    let (o, i, e) = async_command name arguments in
    output_lines input i;
    let out = input_lines o in
    let status = Unix.close_process_full (o, i, e) in
    begin match status with
      | Unix.WEXITED   x -> if x != 0 then raise (Shell_error (unlines out))
      | Unix.WSIGNALED x -> if x = Sys.sigint then raise Sys.Break
      | Unix.WSTOPPED  x -> if x = Sys.sigint then raise Sys.Break
    end;
    out
end

module ListSet = struct
  let cup cmp s1 s2 =
    let res = List.merge cmp s1 s2 in
    List.sort_uniq cmp res

  let sub cmp s1 s2 =
    let rec rep cmp s1 s2 res =
      match s1 with
      | [] -> res
      | h1 :: t1 ->
        match s2 with
        | [] -> List.rev s1 @ res
        | h2 :: t2 ->
          let r = cmp h1 h2 in
          if r < 0 then
            rep cmp t1 s2 (h1 :: res)
          else if r > 0 then
            rep cmp s1 t2 res
          else
            rep cmp t1 s2 res
    in
    List.rev @@ rep cmp s1 s2 []

  let cap cmp s1 s2 =
    let rec rep cmp s1 s2 res =
      match s1 with
      | [] -> res
      | h1 :: t1 ->
        match s2 with
        | [] -> res
        | h2 :: t2 ->
          let r = cmp h1 h2 in
          if r < 0 then
            rep cmp t1 s2 res
          else if r > 0 then
            rep cmp s1 t2 res
          else
            rep cmp t1 s2 (h1 :: res)
    in
    List.rev @@ rep cmp s1 s2 []
end
