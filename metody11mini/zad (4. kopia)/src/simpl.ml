open RawAst

let binop_name (bop : RawAst.bop) =
  match bop with
  | Add  -> "add"
  | Sub  -> "sub"
  | Mult -> "mult"
  | Div  -> "div"
  | And  -> "and"
  | Or   -> "or"
  | Eq   -> "eq"
  | Neq  -> "neq"
  | Leq  -> "leq"
  | Lt   -> "lt"
  | Geq  -> "geq"
  | Gt   -> "gt"

exception Type_error of
  (Lexing.position * Lexing.position) * string

exception Small_type_error of
  string

module Env = struct
  module StrMap = Map.Make(String)
  type t = typ StrMap.t

  let initial = StrMap.empty

  let add_var env x tp =
    StrMap.add x tp env

  let lookup_var env x =
    StrMap.find_opt x env
end

let rec print_type (tau : typ) : string =
	match tau with 
	| TUnit -> "unit"
 	| TInt -> "int"
	| TBool -> "bool"
 	| TArrow (t1, t2) -> "("^(print_type t1)^" -> "^(print_type t2)^")"
	| TPair (t1, t2) -> "("^(print_type t1)^" * "^(print_type t2)^")"








let rec simplify env (e : RawAst.expr) : (Ast.expr * typ) = (* + check_types*)
try 
  match e.data with
  | Unit   -> (Unit, TUnit)
  | Int  n -> (Int n, TInt)
  | Bool b -> (Bool b, TBool)
  | Var  x -> (Var x,
	begin match Env.lookup_var env x with
	    | Some tp -> tp
	    | None    ->
	      raise (Type_error(e.pos,
		Printf.sprintf "Unbound variable %s" x))
	    end
   	)
  

  | Let(x, e1, e2) ->
	let s1 = simplify env e1 in let s2 = simplify (Env.add_var env x (snd s1)) e2 in 
      ( Let(x, fst s1, fst s2),
	 snd s2
	)

	
  | Binop(bop, e1, e2) ->
       let s1 = simplify env e1 and s2 = simplify env e2 in
      (App(App(Builtin(binop_name bop), fst s1),
        fst s2),
	begin match bop with
	| (Add | Sub | Mult | Div) ->
	    check_type (snd s1) TInt;
	    check_type (snd s2) TInt;
	    TInt
	  | (And | Or) ->
	    check_type (snd s1) TBool;
	    check_type (snd s2) TBool;
	    TBool
	  | (Leq | Lt | Geq | Gt) ->
	    check_type (snd s1) TInt;
	    check_type (snd s2) TInt;
	    TBool
	  | (Eq | Neq) ->
	    let tp = snd s1 in
	    check_type (snd s2) tp;
	    TBool



	end
	)
  


  | Pair(e1, e2) ->
     let  s1 = simplify env e1 and s2 = simplify env e2 in
      (Pair((fst s1), (fst s2)) , TPair((snd s1), (snd s2)) )
  | App(e1, e2) ->
	let  s1 = simplify env e1 and s2 = simplify env e2 in
     ( App(fst s1, fst s2) ,
	begin match snd s1 with
	    | TArrow(tp2, tp1) ->
	      check_type (snd s2) tp2;
	      tp1
	    | _ -> raise (Type_error(e.pos,
		"Not a function, cannot be applied"))
	    end


	 )
  | Fst e ->
	let s = simplify env e in
     ( App(Builtin "fst", fst s),
 begin match snd s with
    | TPair(tp1, _) -> tp1
    | _ -> raise (Type_error(e.pos,
        "Not a pair"))
    end
)
  | Snd e ->
let s = simplify env e in
     ( App(Builtin "snd", fst s),
 begin match snd s with
    | TPair(_, tp2) -> tp2
    | _ -> raise (Type_error(e.pos,
        "Not a pair"))
    end

     )
  | Fun(x, tp1, e) ->
	let s = simplify (Env.add_var env x tp1) e in
     ( Fun(x, fst s),
	let tp2 = snd s in
    TArrow(tp1, tp2)


	)
  | Funrec(f, x, tp1, tp2, e) ->
 let env = Env.add_var env x tp1 in
    let env = Env.add_var env f (TArrow(tp1, tp2)) in
let s = simplify env e in 
     ( Ast.Funrec(f, x, fst s),
	( check_type (snd s) tp2;
    TArrow(tp1, tp2))

	)
| If(b, e1, e2)  ->
	let syb = simplify env b and s1 = simplify env e1  and s2 = simplify env e2 in
      (If(fst syb, fst s1, fst s2)
	,
	    (check_type (snd syb) TBool;
	    let tp = snd s1 in
	    check_type (snd s2) tp;
	    tp)
	)

with Small_type_error(s) -> raise (Type_error(e.pos, s) )


and check_type tp' tp =
  if tp = tp' then ()
  else
    raise (Small_type_error(
        Printf.sprintf "expected type: %s, not: %s" (print_type tp) (print_type tp')  ))


let simplify_and_check e =
let (e , _) = simplify Env.initial e in e