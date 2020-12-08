
type tvar = Tvar of string (* term variable *)
type pvar = Pvar of string (* predicate variable *)

let tvar_count = ref 0
let mk_fresh_tvar () =
  incr tvar_count;
  Tvar ("tvar!" ^ string_of_int !tvar_count)

let parameter_cout = ref 0
let mk_fresh_parameter () =
  incr parameter_cout;
  Tvar ("paramvar!" ^ string_of_int !parameter_cout)

let head_arg_count = ref 0
let mk_fresh_head_arg () =
  incr head_arg_count;
  Tvar ("head_arg!" ^ string_of_int !head_arg_count)

let pvar_count = ref 0
let mk_fresh_pvar () =
  incr pvar_count;
  Pvar ("pvar!" ^ string_of_int !pvar_count)

let name_of_tvar = function Tvar name -> name
let name_of_pvar = function Pvar name -> name

let tvar_compare (Tvar var1) (Tvar var2) =
  String.compare var1 var2

let pvar_compare (Pvar var1) (Pvar var2) =
  String.compare var1 var2
