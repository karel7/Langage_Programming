

module Smap = Map.Make(String)
type env_var = (typ, bool) Smap.t (* The boolean indicates whether the variable is mutable *)
type env_struct = struct_argument list Smap.t
type func = {args : argument list; return : typ}
type env_func = func Smap.t

type env = {evar : env_var; estruct : env_struct; efunc : env_func ; mutable current_return : typ option}

exception Type_Error of string

(*
type typ = Tnull
          | Tint
          | Tbool
          | Tstruct of ident
          | Tvec of typ
          | Tref of typ
          | Tmut of typ
*)


(* *********************** *)

let is_lvalue env = function
	| Evar id when Smap.mem id env.evar -> true
	|

let rec type_check env = function

	|Decl_fun df -> env.current_return <- df.return ;  
	|Decl_struct ds -> Smap.add ds.name ds.defs env.estruct

  | Inothing -> Tnull
  | Iexpr e -> type_check env e

  | ImutExAssign (id, e) -> let te = type_check env e in Smap.add id (te, true) env.evar

  | ImutStAssign of ident * ident * ((ident * expr) list )(* *********************** *)

  | IexAssign (id, e) -> let te = type_check env e in Smap.add id (te, false) env.evar
  | IstAssign of ident * ident * ((ident * expr) list )(* *********************** *)

  | Iwhile (expr, bl) -> type_check_condition env expr; type_check env bl
  | Ireturn e -> if type_check env e = env.current_return then Tnull else raise Type_Error "Incorrect return type"
  | IreturnNull -> if env.current_return = Tnull then Tnull else raise Type_Error "Incorrect (null) return type"
  | Icond cond -> type_check_if env cond

  | Econst _ -> Tint
  | Ebool _ -> Tbool
  | Evar id -> try Smap.find id env.evar with Not_found -> raise Type_Error "Unbound variable identifier"
  | Ebinop (b, e1, e2) -> type_check_binop b e1 e2
  | Eunop (u, e) -> type_check_unop env u e
  | Estruct of expr * ident
  | Elength e -> (match (type_check env e) with 
									|Tvec _ -> Tint
									| _ -> raise Type_Error "length method can only be used on vectors" )
  | Eindex (v, e) -> if not Smap.mem v then raise Type_Error "Unbound vector identifier";
		     if (type_check env e) <> Tint then raise Type_Error "Index should be integer";
		     (match Smap.find v with |Tvec t -> t | _ -> raise Type_Error "Indexation of non vector variable")
	| Ecall (id, l) -> let f = try Smap.find id env.efunc with Not_found -> raise Type_Error "Undeclared function" in 
											let lt = List.map (type_check env) l in
											let lty  = List.map (fun a -> a.types) f.args in
											try List.iter2 (fun a b -> if a <> b then raise Type_Error "Incorrect argument type") lt lty with Invalid_argument -> raise Type_Error "Too many/few arguments"
											; f.return

  | Eprint s -> Tnull
  | Evector (ident, l) -> if List.length l > 0 then (let lt = List.map (type_check env) l in
													if not (List.for_all (fun x -> x = List.hd lt) lt) then raise Type_Error "Non homogenous vector" else Tvec (List.hd lt)) else Tvec Tnull (************************************* *)
  | Eblock bl -> type_check_block env bl



and type_check_if env = function 
  | Cif (e, b1, b2) -> type_check_condition env e; let tb1 = type_check env b1 in
																										let tb2 = type_check env b2 in
																										if tb1 <> tb2 then raise Type_Error "different types in if alternatives" else tb1
  | CnestedIf (e, bl, c) -> type_check_condition env e; let tbl = type_check env bl in
																												let tc = type_check_if env c in 
																												if tbl <> tc then raise Type_Error "different types in if alternatives" else tbl

and type_check_condition env c = if (type_check env c) <> Tbool then raise Type_Error "condition should be boolean"

and type_check_unop env u e = let te = (type_check env e) in match u with
  | Uneg when te = Tint -> Tint (* -e *)
  | Unot when te = Tbool -> Tbool(* not e *)
  | Unstar -> (match te with | Tref ty -> ty | _ -> raise Type_Error "Dereferencing operator applied to non reference value" )
  | Unp (**********************)
  | Unmutp (**********************)
(*  | -> Type_Error "Incorrect unary operator" *)

and type_check_binop env b e1 e2 = 
  let te1 = type_check env e1 in
  let te2 = type_check env e2 in
	let nonint = te1 <> Tint || te2 <> Tint in
	match b with
  | Badd | Bsub | Bmul | Bdiv | Bmod -> if nonint then raise Type_Error "Non integer in arithmetic expression"; Tint
  | Beq | Bneq | Blt | Ble | Bgt | Bge -> if nonint then raise Type_Error "Comparison with non integer"; Tbool (* == != < <= > >= *)
  | Band | Bor -> if te1 <> Tbool || te2 <> Tbool then 
		  raise Type_Error "Logical operator should be applied to bool values"; Tbool

and type_check_block env = function
  | CFullBlock (l, exp) -> List.iter (type_check env) l ; type_check env exp
  | CBlock l -> List.iter (type_check env) l



