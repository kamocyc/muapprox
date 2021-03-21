  
let split_with file separator =
  let buf = Hflmc2_util.read_file file in
  let re = Str.regexp @@ "^" ^ separator ^ "$" in
  let found_index =
    try
      Str.search_forward re buf 0
    with Not_found -> failwith @@ "split_with: not found " ^ separator in
  let before_text = String.sub buf 0 found_index in
  let found_index = found_index + String.length separator in
  let (extracted, after_text) =
    try
      let re = Str.regexp @@ "^%[A-Za-z_]+$" in
      let next_separator_index = Str.search_forward re buf (found_index + 1) in
      let extracted = String.sub buf found_index (next_separator_index - found_index) in
      let after_text = String.sub buf next_separator_index (String.length buf - next_separator_index) in
      (extracted, after_text)
    with Not_found ->
      let extracted = String.sub buf found_index (String.length buf - found_index) in
      (extracted, "") in
  let before_line_number = Hflmc2_util.count_substring before_text "\n" in
  let after_line_number = Hflmc2_util.count_substring after_text "\n" in
  let extracted_line_number = Hflmc2_util.count_substring extracted "\n" in
  (
    extracted, [(before_line_number + 1, before_line_number + extracted_line_number + 1)],
    before_text ^ "\n" ^ after_text, [(1, before_line_number + 1); (before_line_number + extracted_line_number + 1, before_line_number + extracted_line_number + after_line_number + 1)]
  )

let parse_file line_numbers file =
  Hflmc2_util.Parse.parse_file Lexer.token Parser.program line_numbers file
