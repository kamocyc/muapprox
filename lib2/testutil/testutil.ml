open OUnit

(* TODO: add string_of field *)
type 'a test = { name: string; actual: unit -> 'a; expected: 'a }
type 'a test_with_to_string = { name: string; actual: unit -> 'a; expected: 'a; to_string: 'a -> string }
type ('a, 'b) test_missing_exec = { name: string; input: 'a; expected: 'b }
type ('a, 'b) test_missing_exec_with_to_string = { name: string; input: 'a; expected: 'b }

let dummy_printer = fun _ -> ""
let dummy_pp_diff = fun _ _ -> ()

let gen_tests ?printer ?pp_diff tests =
  List.map
    (fun (test: 'a test) ->
       test.name >:: fun () ->
         let actual = test.actual () in
         assert_equal ?printer ?pp_diff test.expected actual
    ) tests

let gen_cases_with_exec exec tests =
  List.map
    (fun test ->
       { name = test.name; actual = (fun () -> exec test.input); expected = test.expected }
    ) tests

let gen_tests_with_exec ?printer ?pp_diff exec tests =
  gen_tests ?printer ?pp_diff @@ gen_cases_with_exec exec tests
