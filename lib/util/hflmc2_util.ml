type process_status = Unix.process_status
let partition = List.partition
let partition_map t ~f =
  let rec loop t fst snd =
    match t with
    | [] -> List.rev fst, List.rev snd
    | x :: t ->
      (match f x with
       | `Fst y -> loop t (y :: fst) snd
       | `Snd y -> loop t fst (y :: snd))
  in
  loop t [] []
  
let contains_duplicates ls = (List.length @@ List.sort_uniq compare ls) <> List.length ls

let group_by f l1 =
  List.fold_left
    (fun acc e ->
      let key = f e in
      let mem = try Hashtbl.find acc key with Not_found -> [] in
      Hashtbl.replace acc key (e::mem);
      acc
    )
    (Hashtbl.create 100)
    l1

let list_of_hashtbl ht = Hashtbl.fold (fun k v acc -> (k, v)::acc) ht []

let list_product l1 l2 =
  List.map (fun e1 -> List.map (fun e2 -> (e1, e2)) l2) l1
  |> List.flatten

let rec merge_and_unify comp l1 l2 =
  match (l1, l2) with
    (_,[]) -> l1
  | ([], _)->l2
  | (x::l1',y::l2') -> 
        let c = comp x y in
         if c=0 then x::(merge_and_unify comp l1' l2')
         else if c<0 then x::(merge_and_unify comp l1' l2)
         else y::(merge_and_unify comp l1 l2');;
let merge_and_unify_list comp ll =
  List.fold_left
  (fun l1 l2 -> merge_and_unify comp l1 l2)
  [] ll

let upto m =
  let rec go m = if m = 0 then [0] else m :: (go (m - 1)) in    
  go m |> List.rev

let read_file file = Core.In_channel.(with_file file ~f:input_all)

let write_file file buf = Core.Out_channel.write_all file ~data:buf

let count_substring str sub =
  let sub_len = String.length sub in
  let len_diff = (String.length str) - sub_len
  and reg = Str.regexp_string sub in
  let rec aux i n =
    if i > len_diff then n else
      try
        let pos = Str.search_forward reg str i in
        aux (pos + sub_len) (succ n)
      with Not_found -> n
  in
  aux 0 0

module Parse = Parse

module Core = Core
open Core

module Pair = struct
  (* Bifunctor method *)
  let bimap  ~f (x, y) = (f x, f y)
  let first  ~f (x, y) = (f x, y)
  let second ~f (x, y) = (x, f y)
end

module List = struct
  include List
  let enumurate xs =
    List.zip_exn xs (List.init (List.length xs) ~f:(fun x -> x))
  let find_with_index ~f:(p : 'a -> bool) (xs : 'a list) =
    List.find_exn (enumurate xs) ~f:(fun (x,_) -> p x)
  let rec powerset = function
    | [] -> [[]]
    | x :: xs ->
       let ps = powerset xs in
       ps @ List.map ~f:(fun ss -> x :: ss) ps
  let rec powerset_with_limit n = function
    | [] -> if n >= 0 then [[]] else []
    | x :: xs ->
        let ps = powerset_with_limit n xs in
        let ps'= powerset_with_limit (n-1) xs in
        ps @ List.map ~f:(fun ss -> x :: ss) ps'
  let powerset ?limit xs = match limit with
    | None -> powerset xs
    | Some n -> powerset_with_limit n xs
  let singleton x = [x]
  let cartesian_products : 'a list list -> 'a list list =
    fun xss ->
      fold_right xss ~init:[[]] ~f:begin fun xs acc ->
        map (cartesian_product xs acc) ~f:begin fun (y,ys) -> y::ys end
      end
  let zipper_map ~f =
    function
    | [] -> []
    | x::xs ->
        let rec go xs y zs =
          f xs y zs ::
            match zs with
            | [] -> []
            | z::zs -> go (y::xs) z zs
        in go [] x xs
  let remove_duplicates : 'a list -> equal:('a -> 'a -> bool) -> 'a list =
    fun xs ~equal ->
      let cons_if_uniq x xs = if mem ~equal xs x then xs else x :: xs in
      List.fold_left xs ~init:[] ~f:begin fun xs x ->
        cons_if_uniq x xs
      end
  let subset xs ys =
    for_all xs ~f:begin fun x ->
      exists ys ~f:begin fun y ->
        x = y end end
  (* compareをリスペクトするtotal orderがあればmerge sortの
   * 要領でO(n log n)でできるがこれがボトルネックとなるとは思えないので
   * とりあえず O(n^2) で実装する
   *)
  let rec maximals
       : 'a list
      -> compare:('a -> 'a -> int option)
      -> 'a list =
    fun xs ~compare ->
      let remove_lt x ys =
        let is_maximal = ref true in
        let rec go x ys =
          match ys with
          | [] -> []
          | y::ys ->
              begin match compare x y with
              | Some n when n >= 0 ->
                  go x ys
              | Some _ ->
                  is_maximal := false;
                  y :: go y ys (* xでもよいがこの方が速い *)
              | None ->
                  y :: go x ys
              end
        in
        let ys' = go x ys in
        (!is_maximal, ys')
      in
      match xs with
      | [] -> []
      | x::xs ->
          let (is_maximal, ys) = remove_lt x xs in
          if is_maximal
          then x :: maximals ~compare ys
          else maximals ~compare ys
  let maximals' (<=) xs =
    let compare a b =
      let a_le_b = a <= b in
      let b_le_a = b <= a in
      match () with
      | _ when a_le_b && b_le_a -> Some 0
      | _ when a_le_b           -> Some (-1)
      | _ when b_le_a           -> Some 1
      | _                       -> None
    in
    maximals ~compare xs
end

module Unit = Unit

module Int = Int

module Bool = Bool

module Array = Array

module String   = String

module Map = struct  
  include Map
  module Make'(Key : Key) = struct
    
    include Make(Key)
    let replace : 'a t -> key:Key.t -> data:'a -> 'a t =
      fun map ~key ~data ->
        let map = remove map key in
        add_exn map ~key ~data
        
    let merge'_either : 'a t -> 'a t -> ('a t, (Key.t * 'a * 'a)) Either.t =
      fun m1 m2 ->
        let dup = ref None in
        try
          First
            (merge m1 m2
              ~f:begin fun ~key -> function
              | `Left x -> Some x
              | `Right x -> Some x
              | `Both (l, r) ->
                  dup := Some (key, l, r);
                  invalid_arg ""
              end)
        with Invalid_argument _ -> begin
          match !dup with
          | Some (key, l, r) -> Second (key, l, r)
          | None -> assert false
        end
            
    let merge' : 'a t -> 'a t -> 'a t =
      fun m1 m2 ->
        match merge'_either m1 m2 with
        | First r -> r
        | Second (key, _, _) -> invalid_arg @@ "merge: " ^ string_of_sexp (Key.sexp_of_t key)
  end
end
module IntMap   = Map.Make'(Int)
module StrMap   = Map.Make'(String)

module Set      = struct
  include Set
  module Make'(Elt : Elt) = struct
    include Make(Elt)
    let maximals' (<=) set =
      to_list set |> List.maximals' (<=) |> of_list
  end
end
module IntSet   = Set.Make'(Int)
module StrSet   = Set.Make'(String)

module Option   = Option

module Sexp     = Sexp

module Hashtbl  = Hashtbl

module Hash_set = Hash_set

module Arg      = Arg
module Command  = Command

module In_channel = In_channel
module Out_channel = Out_channel

module Void = struct
  type t = Void of { absurd : 'a. 'a }
  let absurd (Void void) = void.absurd
  let equal v _     = absurd v
  let compare v _   = absurd v
  let pp _ v        = absurd v
  let t_of_sexp _   = failwith "void_of_sexp"
  let sexp_of_t v   = absurd v
end

module Fn = struct
  include Fn

  exception Fatal of string
  exception Unsupported of string
  exception TODO of string
  let fatal s = raise (Fatal s)
  let unsupported ?(info="") () = raise (Unsupported info)
  let todo ?(info="") () = raise (TODO info)

  let neg i = -i
  let const x _ = x

  let print ?(tag="") pp x =
    match tag with
    | "" -> Format.printf "@[%a@]@." pp x
    | _ -> Format.printf "%s: @[%a@]@." tag pp x

  let on injection g x y = g (injection x) (injection y)

  let curry f x y = f (x, y)
  let uncurry f (x,y) = f x y

  let ( <<< ) f g x = f (g x)
  let ( >>> ) f g x = g (f x)
  let ( -$- ) f x y = f y x

  let read_file file = In_channel.(with_file file ~f:input_all)

  let assert_no_exn f =
    try f () with e -> print_endline (Exn.to_string e); assert false
(* 
  let pp_process_result fmt stat _ err =
    let show_process_status : process_status -> string = function
      | WEXITED code -> "WEXITED(" ^ (string_of_int code) ^ ")"
      | WSIGNALED code -> "WSIGNALED(" ^ (string_of_int code) ^ ")"
      | WSTOPPED code -> "WSTOPPED(" ^ (string_of_int code) ^ ")" in
    Format.pp_print_string fmt @@ "Process result:\n";
    (* Format.pp_print_string fmt @@ "out: " ^ out ^ "\n"; *)
    Format.pp_print_string fmt @@ "status: " ^ (show_process_status stat) ^ "\n";
    Format.pp_print_string fmt @@ "err: " ^ err ^ "\n"
    
  let run_command_ ?(timeout=20.0) cmd =
    Format.pp_print_string Format.std_formatter @@ "Run command \"" ^ (String.concat ~sep:" " @@ Array.to_list cmd) ^ "\"\n";
    Format.print_flush ();
    let f_out, fd_out = Unix.mkstemp "/tmp/run_command.stdout" in
    let f_err, fd_err = Unix.mkstemp "/tmp/run_command.stderr" in
    let process_status = Lwt_main.run @@
      Lwt_process.exec
        ~timeout
        ~stdout:(`FD_move fd_out)
        ~stderr:(`FD_move fd_err)
        ("", cmd)
    in
    let stdout = read_file f_out in
    let stderr = read_file f_err in
    Unix.remove f_out;
    Unix.remove f_err;
    pp_process_result Format.std_formatter process_status stdout stderr;
    (process_status, stdout, stderr) *)

  class counter = object
    val mutable cnt = 0
    method tick =
      let x = cnt in
      cnt <- x + 1;
      x
  end
  
  module Command : sig
    exception Shell_error of string

    type t_result = (unit, [ `Exit_non_zero of int | `Signal of Signal.t | `Timeout]) result
    
    val async_command : float -> string -> string list -> Unix.Process_channels.t

    val sync_command_full : float -> string -> string list -> string list -> (string -> unit) -> (string -> unit) -> t_result * string * string
    
    val sync_command  : float -> string -> string list -> string list -> t_result * string * string 

    val output_lines : string list -> Out_channel.t -> unit

    val input_lines : In_channel.t -> (string -> unit) -> string list
    
    val run_command : ?timeout:float -> string array -> t_result * string * string
  end = struct
    exception Shell_error of string

    type t_result = (unit, [ `Exit_non_zero of int | `Signal of Signal.t | `Timeout]) result
    
    let output_lines (output : string list) (chan : Out_channel.t) : unit =
      List.iter
        ~f:(fun line -> Out_channel.output_string chan (line ^ "\n"))
        output;
      Out_channel.flush chan

    let rec do_channel_lines (f : string -> 'a) (chan : In_channel.t) (read_line_handler : string -> unit) : 'a list =
      match In_channel.input_line chan with
      | None -> []
      | Some line -> begin
        read_line_handler line;
        f line :: do_channel_lines f chan read_line_handler
      end

    let input_lines = do_channel_lines (fun x -> x)

    let unlines : string list -> string = String.concat ~sep:"\n"

    let async_command (timeout : float) (name : string) (arguments : string list) :
      Unix.Process_channels.t =
      (* use sigkill ? *)
      Unix.open_process_full
        (Printf.sprintf "bash -c 'timeout %s %s %s'"
          (string_of_float timeout)
          name
          (String.concat ~sep:" " arguments))
        ~env:(Unix.environment ())

    let pp_process_result fmt status out err =
      let show_status status = match status with
      | Ok _ -> "Ok"
      | Error (`Exit_non_zero 124) -> "Timeout"
      | Error (`Exit_non_zero c) -> "Error (`Exit_non_zero " ^ string_of_int c ^ ")"
      | Error (`Signal _) -> "Error (`Signal )" in
      Format.pp_print_string fmt @@ "Process result:\n";
      Format.pp_print_string fmt @@ "out: " ^ out ^ "\n";
      Format.pp_print_string fmt @@ "status: " ^ (show_status status) ^ "\n";
      Format.pp_print_string fmt @@ "err:\n" ^ err ^ "\n\n"

    let sync_command_full (timeout : float) (name : string) (arguments : string list)
        (input : string list) (read_line_handler : string -> unit) (read_err_line_handler : string -> unit) : t_result * string * string =
      let pcs = async_command timeout name arguments in
      output_lines input pcs.stdin;
      let out = unlines @@ input_lines pcs.stdout read_line_handler in
      let err = unlines @@ input_lines pcs.stderr read_err_line_handler in
      let status = Unix.close_process_full pcs in
      pp_process_result Format.std_formatter status out err;
      match status with
      | Ok () -> (Ok (), out, err)
      | Error (`Exit_non_zero 124) -> (Error (`Timeout), out, err)
      | Error (`Exit_non_zero c) -> (Error (`Exit_non_zero c), out, err)
      | Error (`Signal x) ->
        if Signal.equal x Signal.int then raise Sys.Break else (Error (`Signal x), out, err)
    
    let sync_command timeout name arguments input = sync_command_full timeout name arguments input print_endline (fun _ -> ())
    
    let run_command ?(timeout=10.0) commands =
      Format.pp_print_string Format.std_formatter @@ "Run command (muapprox) \"" ^ (String.concat ~sep:" " @@ Array.to_list commands) ^ "\"\n";
      match Array.to_list commands with
      | [] -> failwith "run_command"
      | name::arguments -> sync_command timeout name arguments []
  end
end


let (>>>) = Fn.(>>>)
let (<<<) = Fn.(<<<)
let (-$-) = Fn.(-$-)

let char_of_sexp      = char_of_sexp
let sexp_of_char      = sexp_of_char
let bool_of_sexp      = bool_of_sexp
let sexp_of_bool      = sexp_of_bool
let sexp_of_exn       = sexp_of_exn
let float_of_sexp     = float_of_sexp
let sexp_of_float     = sexp_of_float
let int_of_sexp       = int_of_sexp
let sexp_of_int       = sexp_of_int
let int32_of_sexp     = int32_of_sexp
let sexp_of_int32     = sexp_of_int32
let int64_of_sexp     = int64_of_sexp
let sexp_of_int64     = sexp_of_int64
let list_of_sexp      = list_of_sexp
let sexp_of_list      = sexp_of_list
let nativeint_of_sexp = nativeint_of_sexp
let sexp_of_nativeint = sexp_of_nativeint
let option_of_sexp    = option_of_sexp
let sexp_of_option    = sexp_of_option
let sexp_of_ref       = sexp_of_ref
let string_of_sexp    = string_of_sexp
let sexp_of_string    = sexp_of_string
let bytes_of_sexp     = bytes_of_sexp
let sexp_of_bytes     = sexp_of_bytes
let unit_of_sexp      = unit_of_sexp
let sexp_of_unit      = sexp_of_unit

type ('a, 'b) result = Ok of 'a | Error of 'b

let show_list f ls = "[ " ^ (List.map ~f:f ls |> String.concat ~sep:"; \n") ^ " ]"
let show_pairs pr1 pr2 ls =
  show_list (fun (p1, p2) -> "(" ^ pr1 p1 ^ ", " ^ pr2 p2 ^ ")") ls
let print_list f ls = print_endline @@ show_list f ls
let fmt_string (outputter : Format.formatter -> 'a -> unit) ?margin (data : 'a): string =
  let buf = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buf in
  (match margin with Some m -> Format.pp_set_margin fmt m | None -> ());
  outputter fmt data;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let remove_elt f l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when f x -> go xs acc
    | x::xs -> go xs (x::acc)
  in go l []
  
let%expect_test "remove_elt" =
  let res = remove_elt ((<=)3) [5; 2; 3; 1; 6] in
  ignore [%expect.output];
  print_list string_of_int res;
  [%expect {|
    [ 2;
    1 ] |}]

let remove_duplicates f l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt (f x) xs) (x::acc)
  in go l []
  
let%expect_test "remove_duplicates" =
  let res = remove_duplicates (=) [5; 2; 3; 2; 2; 5; 1; 9] in
  ignore [%expect.output];
  print_list string_of_int res;
  [%expect {|
    [ 5;
    2;
    3;
    1;
    9 ] |}]

let move_first f ls =
  let l1, l2 = partition f ls in
  l1 @ l2
