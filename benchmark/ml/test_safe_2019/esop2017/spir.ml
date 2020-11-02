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

(* $Id: spir.ml,v 1.2 2011-08-08 19:31:17 weis Exp $ *)

open Graphics;;

(* Simple turtle graphics *)

type turtle_state =
  { mutable x : float;
    mutable y : float;
    mutable heading : float }
;;

let t = { x = 0.0; y = 0.0; heading = 0.0 };;

let round x =
  if x >= 0.0 then int_of_float(x +. 0.5) else -(int_of_float(0.5 -. x))
;;

let reset() =
  t.x <- float_of_int(size_x() / 2);
  t.y <- float_of_int(size_y() / 2);
  t.heading <- 0.0;
  moveto (round t.x) (round t.y)
;;

(* A table of flashy colors *)


(* The main drawing function *)

let rec spir dist angle angle_incr color =
  let forward d =
    t.x <- t.x +. cos(t.heading) *. d;
    t.y <- t.y +. sin(t.heading) *. d;
    lineto (round t.x) (round t.y)
  in
  let turn a =
    let pi180 = 4.0 *. atan 1.0 /. 180.0 in
    t.heading <- t.heading +. a *. pi180
  in
  let colors i =
    assert(0<=i && i < 16);
    List.nth
      [ 0xff0000; 0xff6000; 0xffc000; 0xdeff00;
        0x7eff00; 0x1eff00; 0x1eff00; 0x00ff42;
        0x00ffa2; 0x00fcff; 0x009cff; 0x003cff;
        0x2400ff; 0x8400ff; 0xe400ff; 0xff00ba ]i
  in
  if key_pressed() then () else
    begin
      set_color (colors(color));
      forward dist;
      turn angle;
      spir dist (angle +. angle_incr) angle_incr (Random.int 16)
    end
;;

(* The interaction loop *)

let message s =
  let (x, y) = current_point() in
  draw_string s;
  let (_, height) = text_size s in
  moveto x (y + height)
;;

let format f =
  Printf.sprintf "%6.2f" f
;;

let rec loop dist angle_incr =
  clear_graph();
  set_color 0x000000;
  moveto 0 0;
  message "   -           d, D             to decrease";
  message "   +           i, I             to increase";
  message (format dist ^ "      " ^ format angle_incr);
  message "Distance    Angle increment     'q' to quit";
  reset();
  spir dist 0.0 angle_incr 0;
  match read_key() with
  | '-' -> loop (dist -. 2.0) angle_incr
  | '+' -> loop (dist +. 2.0) angle_incr
  | 'd' -> loop dist (angle_incr -. 0.05)
  | 'D' -> loop dist (angle_incr -. 5.0)
  | 'i' -> loop dist (angle_incr +. 0.05)
  | 'I' -> loop dist (angle_incr +. 5.0)
  | 'q' -> ()
  | _ -> loop dist angle_incr
;;

let spir () =
  open_graph "";
  loop 5.0 1.9;
  close_graph()
;;

let main () =
  if !Sys.interactive then () else begin spir(); exit 0 end;;
