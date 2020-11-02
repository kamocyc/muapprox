(***********************************************************************)
(*                                                                     *)
(*                        Caml examples                                *)
(*                                                                     *)
(*            Pierre Weis                                              *)
(*                                                                     *)
(*                        INRIA Rocquencourt                           *)
(*                                                                     *)
(*  Copyright (c) 1994-2011, INRIA                                     *)
(*  All rights reserved.                                               *)
(*                                                                     *)
(*  Distributed under the BSD license.                                 *)
(*                                                                     *)
(***********************************************************************)

(* $Id: soli.ml,v 1.5 2011-08-08 19:31:17 weis Exp $ *)

(** This program solves the famous game ``Le solitaire'', using a
   trivial brute force algorithm (exhaustive exploration of the possible
   games, until a solution is found).

   No graphics involved here: the results are just printed out as ASCII
   characters! *)

type peg =
   | Out
   | Empty
   | Peg
;;

let print_peg = function
  | Out -> print_string ""
  | Empty -> print_string " "
  | Peg -> print_string "$"
;;

let print_board board =
 for i = 0 to 8 do
   for j = 0 to 8 do
    print_peg @@board(i)(j)
   done;
   print_newline ()
 done
;;

type direction = { dx : int; dy : int }

type move = { x1 : int; y1 : int; x2 : int; y2 : int }

exception Found
;;

let rec solve counter m board moves =
  let dir i = List.nth
    [ {dx = 0; dy = 1}; {dx = 1; dy = 0};
       {dx = 0; dy = -1}; {dx = -1; dy = 0} ] i
  in
  counter := !counter + 1;
  if m = 31 then
    begin
      match board(4)(4) with
      | Peg -> true
      | Out | Empty -> false
    end
  else
    try
      if !counter mod 500 = 0 then begin
        print_int !counter; print_newline ()
      end;
      for i = 1 to 7 do
        for j = 1 to 7 do
          match board(i)(j) with
          | Out | Empty -> ()
          | Peg ->
            for k = 0 to 3 do
              let d1 = (dir(k)).dx in
              let d2 = (dir(k)).dy in
              let i1 = i + d1 in
              let i2 = i1 + d1 in
              let j1 = j + d2 in
              let j2 = j1 + d2 in
              match board(i1)(j1) with
              | Out | Empty -> ()
              | Peg ->
                begin match board(i2)(j2) with
                | Out | Peg -> ()
                | Empty ->
                    board(i)(j);
                    board(i1)(j1);
                    board(i2)(j2);
                    if solve counter (m + 1) board moves then begin
                      moves(m);
                      raise Found
                    end;
                    board(i)(j);
                    board(i1)(j1);
                    board(i2)(j2); ()
                end
            done
        done
      done;
      false with
    | Found -> true
;;

let solve_solitaire () =
  let board i j = List.nth (List.nth [
    [ Out; Out; Out; Out; Out; Out; Out; Out; Out];
    [ Out; Out; Out; Peg; Peg; Peg; Out; Out; Out];
    [ Out; Out; Out; Peg; Peg; Peg; Out; Out; Out];
    [ Out; Peg; Peg; Peg; Peg; Peg; Peg; Peg; Out];
    [ Out; Peg; Peg; Peg; Empty; Peg; Peg; Peg; Out];
    [ Out; Peg; Peg; Peg; Peg; Peg; Peg; Peg; Out];
    [ Out; Out; Out; Peg; Peg; Peg; Out; Out; Out];
    [ Out; Out; Out; Peg; Peg; Peg; Out; Out; Out];
    [ Out; Out; Out; Out; Out; Out; Out; Out; Out];
  ] i) j
  in
  let counter = ref 0 in
  let moves i = {x1 = 0; y1 = 0; x2 = 0; y2 = 0} in
  if solve counter 0 board moves then (print_string "\n"; print_board board)
;;

let main _ = if !Sys.interactive then () else solve_solitaire ()
;;
