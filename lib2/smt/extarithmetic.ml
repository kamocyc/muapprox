module Arithmetic = struct
  include (Z3.Arithmetic : module type of Z3.Arithmetic with module Integer := Z3.Arithmetic.Integer)

  module Integer = struct
    include Z3.Arithmetic.Integer
    let get_int expr =
      Big_int.int_of_big_int @@ get_big_int expr
  end
end
