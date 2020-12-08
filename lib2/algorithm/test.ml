open OUnit
open Testutil
open DataStructure

(* union find *)
let mk_uf size edges =
  let uf = UnionFind.mk_size_uf ~size in
  List.iter (fun (u, v) -> UnionFind.unite u v uf) edges;
  uf

let uf_united_query size edges queries =
  let uf = mk_uf size edges in
  List.map (fun (u, v) -> UnionFind.is_united u v uf) queries

let uf_size_query size edges queries =
  let uf = mk_uf size edges in
  List.map (fun u -> UnionFind.get_data u uf) queries

let uf_united_tests =
  [
    { name = "test1"; actual = (fun () -> uf_united_query 6 [(0, 1); (1, 2); (2, 3); (4, 5)] [(0, 1); (0, 3); (1, 2); (2, 3); (2, 5); (0, 5); (5, 4); (1, 1)]); expected = [true; true; true; true; false; false; true; true]; };
    { name = "test2"; actual = (fun () -> uf_united_query 5 [(1, 0); (3, 2); (3, 0); (1, 0)] [(1, 3); (1, 4); (0, 2)]); expected = [true; false; true]; };
  ]

let uf_size_tests =
  [
    { name = "test1"; actual = (fun () -> uf_size_query 5 [(1, 0); (3, 2); (2, 1)] [0; 1; 2; 3; 4]); expected = [4; 4; 4; 4; 1]; };
  ]

(*** Run Tests ***)
let _ = run_test_tt_main begin
    "uf_is_united" >::: (gen_tests uf_united_tests)
  end

let _ = run_test_tt_main begin
    "uf_size" >::: (gen_tests uf_size_tests)
  end