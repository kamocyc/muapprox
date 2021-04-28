open Hflmc2_syntax

module M = struct
  let init = IdMap.singleton
  let merge = IdMap.merge'
  let rec merges = function
    | [] -> failwith "merges"
    | [x] -> x
    | x::xs -> merge x (merges xs)
  let add = IdMap.add
  let find = IdMap.find
  let lookup = IdMap.lookup
  let remove = IdMap.remove
  let map = IdMap.map
  let empty = IdMap.empty
  let to_list x = IdMap.fold x ~init:[] ~f:(fun ~key:k ~data:v acc -> (k, v)::acc)  |> List.rev
end

let save_to_file file text =
  let oc = open_out file in
  output_string oc text;
  close_out oc

type 'var gen_t =
  | Int of unit Id.t * int
  | Var of unit Id.t * 'var
  | Op  of unit Id.t * Arith.op * 'var gen_t list
  [@@deriving eq,ord,show  { with_path = false }]

type tarith = [`Int] Id.t gen_t
  [@@deriving eq,ord,show  { with_path = false }]

type 'ty thflz =
  | Bool   of unit Id.t * bool
  | Var    of unit Id.t * 'ty Id.t
  | Or     of unit Id.t * 'ty thflz * 'ty thflz
  | And    of unit Id.t * 'ty thflz * 'ty thflz
  | Abs    of unit Id.t * 'ty Type.arg Id.t * 'ty thflz
  | Forall of unit Id.t * 'ty Type.arg Id.t * 'ty thflz
  | Exists of unit Id.t * 'ty Type.arg Id.t * 'ty thflz
  | App    of unit Id.t * 'ty thflz * 'ty thflz
  | Arith  of unit Id.t * tarith
  | Pred   of unit Id.t * Formula.pred * tarith list
  [@@deriving eq,ord,show  { with_path = false }]

type s_thflz = Type.simple_ty thflz
[@@deriving eq,ord,show  { with_path = false }]

type 'ty thes_rule = {var : 'ty Id.t; body : 'ty thflz; fix: Fixpoint.t}
[@@deriving eq,ord,show  { with_path = false }]

type 'ty thes_rules = 'ty thes_rule list
[@@deriving eq,ord,show  { with_path = false }]
type s_thes_rules = Type.simple_ty thes_rules
[@@deriving eq,ord,show  { with_path = false }]

module Print_temp = struct
  open Hflmc2_syntax.Print
    
  let pid : Stdlib__format.formatter -> int -> unit = fun fmt _i ->
    (* Fmt.pf fmt "<%d>" i *)
    Fmt.string fmt ""
  
  let p_id ppf id = Fmt.pf ppf "@[<h>%a@]" pid id.Id.id

  let rec gen_arith_ : 'avar t_with_prec -> 'avar gen_t t_with_prec =
    fun avar_ prec ppf a ->
      let show_op = function | (Op (sid, op',[a1;a2])) -> begin
        let op_prec = Prec.of_op op' in
        let prec_l = Prec.(succ_if (not @@ op_is_leftassoc op') op_prec) in
        let prec_r = Prec.(succ_if (not @@ op_is_rightassoc op') op_prec) in
        p_id ppf sid;
        show_paren (prec > op_prec) ppf "@[<1>%a@ @[<h>%a@]%a@ %a@]"
          (gen_arith_ avar_ prec_l) a1
          pid sid.Id.id
          op op'
          (gen_arith_ avar_ prec_r) a2
      end | _ -> assert false
      in
      match a with
      | Int (sid, n) ->
        p_id ppf sid;
        if n >= 0 then
          Fmt.int ppf n
        else
          (Fmt.string ppf "("; Fmt.int ppf n; Fmt.string ppf ")";)
      | Var (sid, x) -> p_id ppf sid; avar_ prec ppf x
      | Op (_, _, _) -> show_op a
      (* | _ -> assert false *)
      
  let gen_arith : 'avar t_with_prec -> 'avar gen_t t =
    fun avar_ ppf a -> gen_arith_ avar_ Prec.zero ppf a
  let arith_ : Prec.t -> tarith Fmt.t =
    fun prec ppf a -> gen_arith_ id_ prec ppf a
  
  let pred : Formula.pred t =
    fun ppf pred -> match pred with
      | Eq  -> Fmt.string ppf "="
      | Neq -> Fmt.string ppf "!="
      | Le  -> Fmt.string ppf "<="
      | Ge  -> Fmt.string ppf ">="
      | Lt  -> Fmt.string ppf "<"
      | Gt  -> Fmt.string ppf ">"
  let pred_ : Formula.pred t_with_prec =
    ignore_prec pred
  
  let rec hflz_ : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty thflz Fmt.t =
    fun format_ty_ prec ppf (phi : 'ty thflz) -> match phi with
      | Bool (sid, true) -> p_id ppf sid; Fmt.string ppf "true"
      | Bool (sid, false) -> p_id ppf sid; Fmt.string ppf "false"
      | Var (sid, x) -> p_id ppf sid; Fmt.pf ppf "%a" id x
      | Or(sid, phi1,phi2)  ->
          (* p_id ppf sid;  *)
          show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@ @[<h>%a@]|| %a@]"
            (hflz_ format_ty_ Prec.or_) phi1
            pid sid.id
            (hflz_ format_ty_ Prec.or_) phi2
      | And (sid, phi1,phi2)  ->
          (* p_id ppf sid;  *)
          show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@ @[<h>%a@]&& %a@]"
            (hflz_ format_ty_ Prec.and_) phi1
            pid sid.id
            (hflz_ format_ty_ Prec.and_) phi2
      | Abs (sid, x, psi) ->
          p_id ppf sid; 
          show_paren (prec > Prec.abs) ppf "@[<1>λ%a:%a.@,%a@]"
            id x
            (argty (format_ty_ Prec.(succ arrow))) x.ty
            (hflz_ format_ty_ Prec.abs) psi
      | Forall (sid, x, psi) ->
          p_id ppf sid; 
          show_paren (prec > Prec.abs) ppf "@[<1>∀%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | Exists (sid, x, psi) ->
          p_id ppf sid; 
          show_paren (prec > Prec.abs) ppf "@[<1>∃%a.@,%a@]"
            id x
            (hflz_ format_ty_ Prec.abs) psi
      | App (sid, psi1, psi2) ->
          p_id ppf sid; 
          show_paren (true) ppf "@[<1>%a@ %a@]"
            (hflz_ format_ty_ Prec.app) psi1
            (hflz_ format_ty_ Prec.(succ app)) psi2
      | Arith (sid, a) ->
        p_id ppf sid;
        arith_ prec ppf a
      | Pred (sid, pred', [f1; f2]) ->
          (* p_id ppf sid;  *)
          Fmt.pf ppf "@[<1>%a@ @[<h>%a@]%a@ %a@]"
            (arith_ prec) f1
            pid sid.id
            pred pred'
            (arith_ prec) f2
      | Pred _ -> assert false

  let hflz : (Prec.t -> 'ty Fmt.t) -> 'ty thflz Fmt.t =
    fun format_ty_ -> hflz_ format_ty_ Prec.zero

  let hflz_hes_rule : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule Fmt.t =
    fun format_ty_ ppf rule ->
      Fmt.pf ppf "@[<2>%s =%a@ %a@]"
        (Id.to_string rule.var)
        fixpoint rule.fix
        (hflz format_ty_) rule.body

  let hflz_hes : (Prec.t -> 'ty Fmt.t) -> 'ty thes_rule list Fmt.t =
    fun format_ty_ ppf rules ->
      Fmt.pf ppf "@[<v>%a@]"
        (Fmt.list (hflz_hes_rule format_ty_)) rules
  
  let print_hes rules = (Print.printf "%a\n" (hflz_hes (fun p fmt ty -> Print.simple_ty_ p fmt ty)) rules); Print.print_flush ();

end

let abbrev_variable_names (hes : Type.simple_ty Hflz.hes): Type.simple_ty Hflz.hes =
  (* let initial_id = Id.gen_id () in *)
  let initial_id = 0 in
  let hes = Hflz.merge_entry_rule hes in
  (* let hes = assign_unique_variable_id hes in *)
  let abbrev_name name =
    match String.index_opt name '_' with
    | None -> name
    | Some i ->
      String.sub name 0 i
  in
  let abbrev_name_id id =
    let name = (abbrev_name id.Id.name) ^ "_" ^ string_of_int (id.Id.id - initial_id) in
    { id with Id.name = name }
  in
  let rec go body = match body with
    | Hflz.Bool b -> Hflz.Bool b
    | Var v -> Var (abbrev_name_id v)
    | Or (p1, p2) -> Or (go p1, go p2)
    | And (p1, p2) -> And (go p1, go p2)
    | Abs (x, p) -> Abs (abbrev_name_id x, go p)
    | Forall (x, p) -> Forall (abbrev_name_id x, go p)
    | Exists (x, p) -> Exists (abbrev_name_id x, go p)
    | App (p1, p2) -> App (go p1, go p2)
    | Arith p -> Arith (go_arith p)
    | Pred (p, ps) -> Pred (p, List.map go_arith ps)
  and go_arith p = match p with
    | Arith.Int i -> Arith.Int i
    | Var v -> Var (abbrev_name_id v)
    | Op (e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun {Hflz.var; body; fix} ->
    let body = go body in
    {Hflz.var = abbrev_name_id var; body; fix}
  ) hes
  |> (fun xs ->
    let h = List.hd xs in
    let h = { h with var = { h.var with name = Hflz.dummy_entry_name } } in
    let tl = List.tl xs in
    Hflz.decompose_entry_rule (h::tl)
  )
  
let assign_id_to_subterm hes =
  let gen () = Id.gen () in
  let rec go (phi : Type.simple_ty Hflz.t) = match phi with
    | Bool b -> Bool (gen (), b)
    | Var v -> Var (gen (), v)
    | Or (p1, p2) -> Or (gen (), go p1, go p2)
    | And (p1, p2) -> And (gen (), go p1, go p2)
    | Abs (x, p) -> Abs (gen (), x, go p)
    | Forall (x, p) -> Forall (gen (), x, go p)
    | Exists (x, p) -> Exists (gen (), x, go p)
    | App (p1, p2) -> App (gen (), go p1, go p2)
    | Arith (a) -> Arith (gen (), go_arith a)
    | Pred (e, ps) -> Pred (gen (), e, List.map go_arith ps)
  and go_arith (phi : Arith.t) = match phi with
    | Int i -> Int (gen (), i)
    | Var v -> Var (gen (), v)
    | Op (e, ps) -> Op (gen (), e, List.map go_arith ps)
  in
  List.map
    (fun {Hflz.var; body; fix} ->
      let body = go body in
      {var; body; fix}
    )
    hes

type ctype = TInt | TBool | TUnit | TFunc of ctype * ctype | TAVar of unit Hflmc2_syntax.Id.t | TBVar of unit Hflmc2_syntax.Id.t
[@@deriving eq,ord,show  { with_path = false }]

let rec show_ctype = function
  | TInt -> "int"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TFunc (p1, p2) -> "(" ^ show_ctype p1 ^ "->" ^ show_ctype p2 ^ ")"
  | TAVar id -> "a_" ^ Hflmc2_syntax.Id.to_string id
  | TBVar id -> "b_" ^ Hflmc2_syntax.Id.to_string id

let rec to_ctype_from_ty ty = match ty with
  | Type.TyBool _ -> TBool
  | Type.TyArrow (x, ty) -> TFunc (to_ctype_from_argty x.Id.ty, to_ctype_from_ty ty)
and to_ctype_from_argty ty = match ty with
  | Type.TyInt -> TInt
  | Type.TySigma (ty) -> to_ctype_from_ty ty

let get_id (phi : Type.simple_ty thflz) = match phi with
  | Bool (id, _) -> id
  | Var (id, _) -> id
  | Or (id, _, _) -> id
  | And (id, _, _) -> id
  | Abs (id, _, _) -> id
  | Forall (id, _, _) -> id
  | Exists (id, _, _) -> id
  | App (id, _, _) -> id
  | Arith (id, _) -> id
  | Pred (id, _, _) -> id

let get_id_arith phi = match phi with
  | Int (id, _) -> id
  | Var (id, _) -> id
  | Op (id, _, _) -> id


let rec subst_ctype ctype subst =
  match ctype with
  | TAVar _ | TBVar _ -> begin
    match List.find_opt (fun (k, _) -> k = ctype) subst with
    | Some (_, v) -> v
    | None -> ctype
  end
  | TInt | TBool | TUnit -> ctype
  | TFunc (p1, p2) -> TFunc (subst_ctype p1 subst, subst_ctype p2 subst)

(* let is_occur id ty =
  let rec go (ty : ctype) = match ty with
    | TAVar v -> Id.eq v id
    | TInt | TBool | TUnit -> false
    | TFunc (p1, p2) -> go p1 || go p2 in
  go ty *)

let show_constraints con =
  let con = M.to_list con in
  Hflmc2_util.show_pairs
    (fun id -> "a_" ^ Id.to_string id)
    (fun l -> Hflmc2_util.show_pairs show_ctype show_ctype l)
    con
    
let compose_subst (ty1, ty) subst =
  let ty' = subst_ctype ty subst in
  (ty1, ty') :: subst

let remove_id_form_subterm (phi : Type.simple_ty thes_rules) =
  let rec go (phi : Type.simple_ty thflz): Type.simple_ty Hflz.t =
    match phi with
    | Bool (_, b) -> Bool b
    | Var (_, v) -> Var v
    | Or (_, p1, p2) -> Or (go p1, go p2)
    | And (_, p1, p2) -> And (go p1, go p2)
    | Abs (_, x, p) -> Abs (x, go p)
    | Forall (_, x, p) -> Forall (x, go p)
    | Exists (_, x, p) -> Exists (x, go p)
    | App (_, p1, p2) -> App (go p1, go p2)
    | Arith (_, p) -> Arith (go_arith p)
    | Pred (_, e, ps) -> Pred (e, List.map go_arith ps)
  and go_arith (phi : tarith) =
    match phi with
    | Int (_, i) -> Int i
    | Var (_, v) -> Var v
    | Op (_, e, ps) -> Op (e, List.map go_arith ps)
  in
  List.map (fun {var; body; fix} ->
    let body = go body in
    {Hflz.var; body; fix}
  ) phi
