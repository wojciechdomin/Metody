[@@@ocaml.warning "-8"]

module I = Interp

(* Składnia RPN *)

type cmd =
  | PushInt  of int
  | PushBool of bool
  | PushPair
  | PushUnit
  | Fst
  | Snd
  | IsPair
  | Binop    of Ast.bop
  | CndJmp   of prog * prog
  | PushVar of Ast.ident

and prog = cmd list

(* Kompilacja do RPN *)

let rec of_ast (expr : Ast.expr) : prog =
  match expr with
  | Ast.Int n ->
      [PushInt n]
  | Ast.Bool b ->
      [PushBool b]
  | Ast.Binop (op, e1, e2) ->
      of_ast e1 @ of_ast e2 @ [Binop op]
  | Ast.If (b, t, e) ->
      of_ast b @ [CndJmp (of_ast t, of_ast e)]
  | Ast.Pair (e1, e2) ->
      of_ast e1 @ of_ast e2 @ [PushPair]
  | Ast.Fst e ->
      of_ast e @ [Fst]
  | Ast.Snd e ->
      of_ast e @ [Snd]
  | Ast.Unit ->
      [PushUnit]
  | Ast.IsPair e ->
      of_ast e @ [IsPair]
  | Ast.Var x -> [PushVar x]
  | _ ->
      failwith "not implemented"

(* Ewaluator dla RPN *)

(* ewaluator nie jest elementem procesu kompilacji, ale
 * przydaje się do testowania i debugowania
 *)
let rec eval (s : I.value list) (p : prog) (env : I.env ) : I.value =
 ( match p, s with
  | [], [n] -> (fun _ -> n)
  | [], _   -> failwith "error!"
  | (PushInt n :: p'), _ ->
      eval (I.VInt n :: s) p'
  | (PushBool b :: p'), _ ->
      eval (I.VBool b :: s) p'
  | (Binop op :: p'), (v2 :: v1 :: s') ->
      eval (I.eval_op op v1 v2 :: s') p'
  | (CndJmp (t,_) :: p'), (I.VBool true :: s') ->
      eval s' (t @ p')
  | (CndJmp (_,e) :: p'), (I.VBool false :: s') ->
      eval s' (e @ p')
  | (PushPair :: p'), (v2 :: v1 :: s') ->
      eval (I.VPair (v1, v2) :: s') p'
  | (Fst :: p'), (I.VPair (v1,_) :: s') ->
      eval (v1 :: s') p'
  | (Snd :: p'), (I.VPair (_,v2) :: s') ->
      eval (v2 :: s') p'
  | (PushUnit :: p'), (s') ->
      eval (I.VUnit :: s') p'
  | (PushVar x :: p'), (s') ->
	eval ((I.M.find x env) :: s') p'


  | _ -> failwith "error!!"
 ) env

(*
test:

eval [] (of_ast (parse("2 + kochamwielblady + 10"))) ( M.add "kochamwielblady" (VInt 2) M.empty) ;;
- : value = Fun.Rpn.I.VInt 14
*)



(* Kompilacja RPN do podzbioru C *)

let lbl_cntr = ref 0 (* bleee!! *)

let fresh_lbl () =
  incr lbl_cntr;
  "lbl" ^ string_of_int !lbl_cntr

let emit_bop (op : Ast.bop) : string =
  Ast.(match op with
  | Add  -> "+"
  | Sub  -> "-"
  | Mult -> "*"
  | Div  -> "/"
  | And  -> "&&"
  | Or   -> "||"
  | Eq   -> "=="
  | Neq  -> "!="
  | Gt   -> ">"
  | Lt   -> "<"
  | Geq  -> ">="
  | Leq  -> "<=")

let emit_bop_res_tag (op : Ast.bop) : string =
  Ast.(match op with
  | Add | Sub | Mult | Div -> "INT"
  | _ -> "BOOL")

let emit_line (s : string) : string =
  "  " ^ s ^ ";\n"

let emit_lbl (s : string) : string =
  " " ^ s ^ ":\n"

(** allocate list of values, pop n elems from the stack*)
let alloc_pop (ss : string list) (to_pop : int) : string =
  (ss
   |> List.mapi (fun i s ->
        emit_line ("heap[heap_ptr+" ^ string_of_int i ^ "] = " ^ s))
   |> String.concat "") ^
  emit_line ("heap_ptr += " ^ string_of_int (List.length ss)) ^
  emit_line ("stack_ptr += " ^ string_of_int (1 - to_pop)) ^
  emit_line ("stack[stack_ptr] = heap_ptr - " ^ string_of_int (List.length ss - 1))

let show_cmd (c : cmd) : string =
  match c with
  | PushInt n -> emit_line ("// PushInt " ^ string_of_int n)
  | PushBool b -> emit_line ("// PushBool " ^ (if b then "true" else "false"))
  | Binop _op -> emit_line "// Binop"
  | PushPair -> emit_line "// PushPair"
  | CndJmp _ -> emit_line "// CndJmp"
  | Fst -> emit_line "// Fst"
  | Snd -> emit_line "// Snd"
  | PushUnit -> emit_line "// PushUnit"
  | IsPair -> emit_line "// IsPair"
  | PushVar x -> emit_line ("// PushInt " ^ x)

let rec emit_cmd (c : cmd) : string =
  show_cmd c ^
  match c with
  | PushInt n ->
      alloc_pop ["INT"; string_of_int n] 0
  | PushBool n ->
      alloc_pop ["BOOL"; if n then "1" else "0"] 0
  | PushPair ->
      alloc_pop ["PAIR"; "stack[stack_ptr-1]"; "stack[stack_ptr]"] 2
  | PushUnit ->
      alloc_pop ["UNIT"] 0
  | Fst ->
      emit_line "stack[stack_ptr] = heap[stack[stack_ptr]]"
  | Snd ->
      emit_line "stack[stack_ptr] = heap[stack[stack_ptr]+1]"
  | IsPair ->
      alloc_pop ["BOOL"; "heap[stack[stack_ptr] - 1] == PAIR"] 1
  | Binop op ->
      alloc_pop
        [emit_bop_res_tag op;
         ("heap[stack[stack_ptr-1]] " ^ emit_bop op ^ " heap[stack[stack_ptr]]")]
        2
  | CndJmp (t, e) ->
      let lbl_t = fresh_lbl () in
      let lbl_end = fresh_lbl () in
      emit_line ("if (heap[stack[stack_ptr]]) goto " ^ lbl_t) ^
      emit_line "stack_ptr--" ^
      emit e ^
      emit_line ("goto " ^ lbl_end) ^
      emit_lbl lbl_t ^
      emit_line "stack_ptr--" ^
      emit t ^
      emit_lbl lbl_end
  | _ -> failwith "not implemented!"

and emit (p : prog) : string =
  List.fold_left (fun res cmd -> res ^ emit_cmd cmd) "" p

let compile (s : string) : string =
  s
  |> Interp.parse
  |> of_ast
  |> emit
  |> Runtime.with_runtime



let stack_size (p : prog) : int = 
	let rec eval (s : unit list) (p : prog) (info : int*int) : int =
	  match p, s, info with
	  | [], [_], (a,b) -> (max a b)
	  | [], _  , (_,_) -> failwith "error!"
	  | (PushInt _ :: p'), _ , (a,b)->
	      eval (() :: s) p' (a+1, max (a+1) b)
	  | (PushBool _ :: p'), _ , (a,b)->
	      eval (() :: s) p' (a+1, max (a+1) b)
	  | (Binop _ :: p'), (() :: () :: s'), (a,b) ->
	      eval (() :: s') p' (a-2, max a b)
	  | (CndJmp (t,e) :: p'), (() :: s'), (a,b) -> 
	      max (eval s' (t @ p') (a-1, max a b)) (eval s' (e @ p') (a-1, max a b))
	  | (PushPair :: p'), (() :: () :: s') , (a,b)->
	      eval (() :: s') p' (a-1, max a b)
	  | (Fst :: p'), (() :: s') , (a,b)->
	      eval (() :: s') p' (a, max a b)
	  | (Snd :: p'), (() :: s') , (a,b)->
	      eval (() :: s') p' (a, max a b)
	  | (PushUnit :: p'), (s') , (a,b)->
	      eval (() :: s') p' (a+1, max (a+1) b)
	  | (PushVar _ :: p'), s', (a,b) -> 
		eval (() :: s') p' (a+1, max (a+1) b )

	  | _ -> failwith "error!!"
	in eval [] p (0,0)

(*

stack_size (of_ast (parse ("if x then y+x else z*(z+z)*z" ) ) );;
- : int = 3


*)
	



