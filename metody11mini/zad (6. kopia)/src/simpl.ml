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
  module MetOrd = struct
	type t = (typ * string)
	let compare = compare
  end
  module MetMap = Map.Make(MetOrd)
  type t = ((typ*int) StrMap.t) * ((typ*int) MetMap.t)

  let initial = (StrMap.empty, MetMap.empty)

  let add_var env x tp =
	let fresh = StrMap.cardinal (fst env) in 
   	  (StrMap.add x (tp,fresh) (fst env) , snd env)



  let lookup_var env x =
    match (StrMap.find_opt x (fst env)) with
	| Some (a,_) -> Some a
	| None -> None

  let lookup_var_int env x =
    match (StrMap.find_opt x (fst env)) with
	| Some (_,b) -> Some b
	| None -> None

  let add_method env x tp1 tp2 = 
	let fresh = (-1) - (MetMap.cardinal (snd env)) in 
	(fst env, MetMap.add (tp1, x) (tp2, fresh) (snd env) )

  let lookup_method env tp1 x  = 
     (MetMap.find_opt (tp1, x) (snd env)) 

  

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
  | Var  x -> 


	(Var (
begin match Env.lookup_var_int env x with
	    | Some ident -> ident
	    | None    ->
	      raise (Type_error(e.pos,
		Printf.sprintf "Unbound variable %s" x))
	    end
),
	begin match Env.lookup_var env x with
	    | Some tp -> tp
	    | None    ->
	      raise (Type_error(e.pos,
		Printf.sprintf "Unbound variable %s" x))
	    end
   	)
  

  | Let(x, e1, e2) ->
	let s1 = simplify env e1 in let env = (Env.add_var env x (snd s1)) in let s2 = simplify env e2 in 
	let x  = begin match Env.lookup_var_int env x with | Some x ->x | None -> failwith "!" end in
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
	let env = (Env.add_var env x tp1) in
	let s = simplify env e in
        let x =  begin match Env.lookup_var_int env x with | Some x ->x | None -> failwith "!" end in
     ( Fun(x, fst s),
	let tp2 = snd s in
    TArrow(tp1, tp2)


	)
  | Funrec(f, x, tp1, tp2, e) ->
 let env = Env.add_var env x tp1 in
    let x =  begin match Env.lookup_var_int env x with | Some x ->x | None -> failwith "!" end in
    let env = Env.add_var env f (TArrow(tp1, tp2)) in
let f =  begin match Env.lookup_var_int env f with | Some f ->f | None -> failwith "!" end in
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
| Dot (e1, n) -> let s1 = simplify env e1 in 
		let (tp2, num) = begin match Env.lookup_method env (snd s1) n with 
		| Some (tp2, num) -> (tp2, num)
 		| None -> raise (Small_type_error("Nie ma takiej metody!1!!!1111!!"))
		end in
		(App (Var num, (fst s1)) , tp2)

| Method (x, tp1, n, e1, e2) -> 
let env1 = Env.add_var env x tp1 in 
let s1 = simplify env1 e1 in 
let tp2 = snd s1 in 
let env2 = Env.add_method env n tp1 tp2 in
let num = begin match Env.lookup_method env2 tp1 n with | Some (_,num) -> num | None -> failwith "niemozliwe1" end in   
let x = begin match Env.lookup_var_int env1 x with | Some x -> x | None -> failwith "niemozliwe2" end in
let s2 = simplify env2 e2 in 
(Let ( num, Fun(x , (fst s1) ) , (fst s2) )  , snd s2 )	 



with Small_type_error(s) -> raise (Type_error(e.pos, s) )


and check_type tp' tp =
  if tp = tp' then ()
  else
    raise (Small_type_error(
        Printf.sprintf "expected type: %s, not: %s" (print_type tp) (print_type tp')  ))


let simplify_and_check e =
let (e , _) = simplify Env.initial e in e