open Ast

let parse (s : string) : expr =
  Parser.main Lexer.read (Lexing.from_string s)

module M = Map.Make(String)

module Loc = Int
module H = Map.Make(Loc)

let fresh h = H.cardinal h

type env = value M.t

and value =
  | VInt of int
  | VBool of bool
  | VUnit
  | VPair of value * value
  | VClosure of ident * expr * env
  | VRecClosure of ident * ident * expr * env
  | VRef of Loc.t

type heap = value H.t

let rec show_value v =
  match v with
  | VInt n -> string_of_int n
  | VBool v -> string_of_bool v
  | VUnit -> "()"
  | VPair (v1,v2) -> "(" ^ show_value v1 ^ ", " ^ show_value v2 ^ ")"
  | VClosure _ | VRecClosure _ -> "<fun>"
  | VRef _ -> "<ref>"



module type COMP2 = sig
    type 'a comp = heap -> 'a * heap
    val return : 'a -> 'a comp
    val bind : 'a comp -> ('a -> 'b comp) -> 'b comp
  end


module Comp2 = struct
	type 'a comp = heap -> 'a * heap
	let return v = fun h -> (v, h)
	let bind c f = fun h -> let (v, h) = c h in f v h
end

let (let* ) = Comp2.bind

(* value -> value ref *)
let refc (v : value) : Loc.t Comp2.comp =
  fun h ->
    let r = fresh h in
    (r, H.add r v h)

let derefc (l : Loc.t) : value Comp2.comp =
  fun h -> (H.find l h, h)

let assgn (l : Loc.t) (v : value) : unit Comp2.comp =
  fun h -> ((), H.add l v h)

let int_op op v1 v2 h =
  match v1, v2 with
  | VInt x, VInt y -> (VInt (op x y), h)
  | _ -> failwith "type error"

let cmp_op op v1 v2 h =
  match v1, v2 with
  | VInt x, VInt y -> (VBool (op x y), h)
  | _ -> failwith "type error"

let bool_op op v1 v2 h =
  match v1, v2 with
  | VBool x, VBool y -> (VBool (op x y), h)
  | _ -> failwith "type error"

let eval_op (op : bop) : value -> value -> value Comp2.comp =
  match op with
  | Add  -> int_op ( + )
  | Sub  -> int_op ( - )
  | Mult -> int_op ( * )
  | Div  -> int_op ( / )
  | And  -> bool_op ( && )
  | Or   -> bool_op ( || )
  | Eq   -> (fun v1 v2 h -> (VBool (v1 = v2), h))
  | Neq  -> (fun v1 v2 h -> (VBool (v1 <> v2), h))
  | Leq  -> cmp_op ( <= )
  | Lt   -> cmp_op ( < )
  | Geq  -> cmp_op ( >= )
  | Gt   -> cmp_op ( > )
  | Assgn -> (fun v1 v2 ->
      match v1 with
      | VRef r ->
        let* _ = assgn r v2 in
        Comp2.return VUnit
      | _ -> failwith "type error")

let rec eval_env (env : env) (e : expr) : value Comp2.comp =
  match e with
  | Int i -> Comp2.return (VInt i)
  | Bool b -> Comp2.return (VBool b)
  | Binop (op, e1, e2) ->
      Comp2.bind (eval_env env e1) (fun v1 -> (* let* v1 = eval_env env e1 in *)
      Comp2.bind (eval_env env e2) (fun v2 ->
      eval_op op v1 v2))
  | If (b, t, e) ->
      let* v = eval_env env b in
      (match v with
      | VBool true -> eval_env env t
      | VBool false -> eval_env env e
      | _ -> failwith "type error")
  | Var x ->
      let v =
        match M.find_opt x env with
        | Some v -> v
        | None -> failwith "unknown var"
      in
      Comp2.return v
  | Let (x, e1, e2) ->
      let* v1 = eval_env env e1 in
      eval_env (env |> M.add x v1) e2
  | Pair (e1, e2) ->
      let* v1 = eval_env env e1 in
      let* v2 = eval_env env e2 in
      Comp2.return (VPair (v1, v2))
  | Unit -> Comp2.return VUnit
  | Fst e ->
      let* v = eval_env env e in
      (match v with
        | VPair (v1, _) -> Comp2.return v1
        | _ -> failwith "Type error")
  | Snd e ->
      let* v = eval_env env e in
      (match v with
      | VPair (_, v2) -> Comp2.return v2
      | _ -> failwith "Type error")
  | Match (e1, x, y, e2) ->
      let* v1 = eval_env env e1 in
      (match v1 with
      | VPair (v1, v2) ->
        eval_env (env |> M.add x v1 |> M.add y v2) e2
      | _ -> failwith "Type error")
  | IsPair e ->
      let* v = eval_env env e in
      let v =
        match v with
        | VPair _ -> VBool true
        | _ -> VBool false
      in
      Comp2.return v
  | Fun (x, e) -> Comp2.return (VClosure (x, e, env))
  | Funrec (f, x, e) -> Comp2.return (VRecClosure (f, x, e, env))
  | App (e1, e2) ->
      let* v1 = eval_env env e1 in
      let* v2 = eval_env env e2 in
      (match v1 with
        | VClosure (x, body, clo_env) ->
            eval_env (M.add x v2 clo_env) body
        | VRecClosure (f, x, body, clo_env) as c ->
            eval_env (clo_env |> M.add x v2 |> M.add f c) body
        | _ -> failwith "not a function")
  | Ref e ->
      let* v = eval_env env e in
      let* r = refc v in
      Comp2.return (VRef r)
  | Deref e ->
      let* v = eval_env env e in
      (match v with
        | VRef r -> derefc r
        | _ -> failwith "not a reference")

let run c = fst (c H.empty)

let eval e = run (eval_env M.empty e)

let interp (s : string) : value =
  eval (parse s)
