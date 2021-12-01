open Raw_program
open Program
open Hflmc2_syntax
open Itype
open Print_syntax

let to_uident v =
  let c = String.get v 0 in
  if c = '_' then failwith "to_uident: the initial character of identifier name should not be '_'";
  (Char.uppercase_ascii c |> String.make 1) ^ String.sub v 1 (String.length v - 1)
  
let replace_var_name_with_upper v func_names =
  let func_names = List.map (fun {Id.name} -> name) func_names in
  match List.find_opt ((=)v) func_names with
  | None -> Print_syntax.replace_var_name v
  | Some _ -> Print_syntax.replace_var_name v |> to_uident

let replace_var_name_with_upper_var v func_names =
  let {Id.name; id; ty} = v in
  let name = replace_var_name_with_upper name func_names in
  {Id.name; id; ty}

let to_forall args body =
  let rec go = function
    | [] -> body
    | arg::xs -> Hflz.Forall (arg, go xs) in
  go args
  
let to_hflz_from_function program func_names =
  let idMap = Hashtbl.create 10 in
  let rec get_forall_vars prog = match prog with
    | PUnit | PVar _ -> prog
    | PIf (p, p1, p2) -> PIf (p, get_forall_vars p1, get_forall_vars p2)
    | PEvent (p, p1) -> PEvent (p, get_forall_vars p1)
    | PNonDet (p1, p2, n, e) ->
      PNonDet (get_forall_vars p1, get_forall_vars p2, n, e)
    | PApp (p1, p2) -> PApp (get_forall_vars p1, get_forall_vars p2)
    | PAppInt (p1, ANonDet (_, e)) ->
      let id = Id.gen ~name:"forall_x" Type.TyInt in
      Hashtbl.add idMap id.id id;
      PAppInt (get_forall_vars p1, ANonDet (Some id.id, e))
    | PAppInt (p1, p2) -> PAppInt (get_forall_vars p1, p2)
  in
  let program = get_forall_vars program in
  let rec go_program program: 'a Hflz.t = match program with
    | PUnit -> Bool true
    | PVar v -> Var (replace_var_name_with_upper_var v func_names)
    | PIf (p, p1, p2) ->
      And (
        Or (
          Hflz.negate_formula (go_predicate p),
          go_program p1
        ),
        Or (
          go_predicate p,
          go_program p2
        )
      )
    | PEvent (_, p) -> go_program p
    | PNonDet (p1, p2, idn_opt, e) -> begin
      And (
        go_program p1,
        go_program p2
      )
      (* match e with
      | Some e when e = Trans_ltl.nondet_demonic_event ->
        Or (
          go_program p1,
          go_program p2
        )
      | Some e when e = Trans_ltl.nondet_angelic_event ->
        And (
          go_program p1,
          go_program p2
        )
      | Some _ | None -> assert false *)
    end
    | PApp (p1, p2) ->
      App (go_program p1, go_program p2)
    | PAppInt (p1, ANonDet (idn_opt, _)) -> begin
      match idn_opt with
      | Some idn ->
        let id = Hashtbl.find idMap idn in
        App (go_program p1, Arith (Var {id with ty=`Int}))
      | None -> assert false      
    end
    | PAppInt (p1, a) -> 
      App (go_program p1, Arith (go_arith a))
  and go_arith p : Arith.t  = match p with
    | AVar v -> Var (replace_var_name_with_upper_var v func_names)
    | AInt i -> Int i
    | ANonDet _ -> assert false
    | AOp (op, [arg1; arg2]) ->
      Op (op, [go_arith arg1; go_arith arg2])
    | AOp _ -> failwith "to_hflz: go_arith"
  and go_predicate p : 'a Hflz.t = match p with
    | Pred (op, [arg1; arg2]) -> Pred (op, [go_arith arg1; go_arith arg2])
    | Pred _ -> failwith "to_hflz: go_predicate"
    | And (p1, p2) -> And (go_predicate p1, go_predicate p2)
    | Or (p1, p2) -> Or (go_predicate p1, go_predicate p2)
    | Bool b -> Bool b
  in
  let forall_bounded_vars = Hashtbl.fold (fun k v acc -> v::acc) idMap [] in
  to_forall
    forall_bounded_vars
    (go_program program)

let to_abs' : 'ty Type.arg Id.t list -> ('ty2 Hflz.t -> 'ty2 Hflz.t) =
  fun args body ->
    let rec go = function
      | [] -> body
      | arg::xs -> Abs(arg, go xs) in
    go args
    
let to_hflz prog priority =
  let entry, funcs = prog in
  if List.length funcs <> List.length priority then failwith "to_hflz";
  let func_names = List.map (fun {var;_} -> var) funcs in
  let funcs = List.map (fun ({var; _} as p) ->
    match List.find_all (fun (v, pr) -> Id.eq v var) priority with
    | [pr] -> (snd pr, p)
    | [] -> failwith "to_hflz (2)"
    | _ -> failwith "to_hflz (3)") funcs
  in
  let funcs = List.sort (fun (pr, _) (pr', _) -> compare pr pr') funcs |> List.rev in
  let entry = to_hflz_from_function entry func_names in
  let rules =
    List.map (fun (pr, {var; args; body}) ->
      let fix = if pr mod 2 = 0 then Fixpoint.Greatest else Fixpoint.Least in
      {
        Hflz.var = replace_var_name_with_upper_var var func_names;
        fix;
        body =
          let args = List.map (fun a -> replace_var_name_with_upper_var a func_names) args in
          to_abs'
            args
            (to_hflz_from_function body func_names) 
      }
    ) funcs in
  let rules = Hflz.merge_entry_rule (entry, rules) in
  let rules, _ = Manipulate.Hflz_util.assign_unique_variable_id rules in
  Hflz.decompose_entry_rule rules
  