open OUnit
open Testutil
open Util

let int_compare a b =
  if a < b then
    -1
  else if a > b then
    1
  else
    0

let string_of_intlist lst =
  "[" ^ (String.concat "; " @@ List.map string_of_int lst) ^ "]"

(*** Run Tests ***)
let _ = run_test_tt_main begin
    "ListSet.cup" >::: gen_tests_with_exec
      ~printer: string_of_intlist
      (fun (a, b) ->
         ListSet.cup int_compare a b
      )
      [
        { name = "cup00"; input = ([], []); expected = []; };
        { name = "cup01"; input = ([4], [5; 6]); expected = [4; 5; 6]; };
        { name = "cup02"; input = ([1; 4; 8], [1; 8; 10]); expected = [1; 4; 8; 10]; };
        { name = "cup03"; input = ([1], []); expected = [1]; };
        { name = "cup04"; input = ([6], [6]); expected = [6]; };
        { name = "cup05"; input = ([1; 2; 3; 4; 5], [1; 2; 3; 4; 5]); expected = [1; 2; 3; 4; 5]; };
      ]
  end

let _ = run_test_tt_main begin
    "ListSet.sub" >::: gen_tests_with_exec
      ~printer: string_of_intlist
      (fun (a, b) ->
         ListSet.sub int_compare a b
      )
      [
        { name = "sub00"; input = ([], []); expected = []; };
        { name = "sub01"; input = ([4], [5; 6]); expected = [4]; };
        { name = "sub02"; input = ([1; 4; 8], [1; 8; 10]); expected = [4]; };
        { name = "sub03"; input = ([1], []); expected = [1]; };
        { name = "sub04"; input = ([6], [6]); expected = []; };
        { name = "sub05"; input = ([1; 2; 3; 4; 5], [1; 2; 3; 4; 5]); expected = []; };
      ]
  end

let _ = run_test_tt_main begin
    "ListSet.cap" >::: gen_tests_with_exec
      ~printer: string_of_intlist
      (fun (a, b) ->
         ListSet.cap int_compare a b
      )
      [
        { name = "cap00"; input = ([], []); expected = []; };
        { name = "cap01"; input = ([4], [5; 6]); expected = []; };
        { name = "cap02"; input = ([1; 4; 8], [1; 8; 10]); expected = [1; 8]; };
        { name = "cap03"; input = ([1], []); expected = []; };
        { name = "cap04"; input = ([6], [6]); expected = [6]; };
        { name = "cap05"; input = ([1; 2; 3; 4; 5], [1; 2; 3; 4; 5]); expected = [1; 2; 3; 4; 5]; };
        { name = "cap06"; input = ([], [1]); expected = []; };
      ]
  end
