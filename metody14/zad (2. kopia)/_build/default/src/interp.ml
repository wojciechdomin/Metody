open Ast

let parse (s : string) : prog =
  Parser.main Lexer.read (Lexing.from_string s)

type value =
  | VInt of int
  | VBool of bool

let show_value v =
  match v with
  | VInt n -> string_of_int n
  | VBool v -> string_of_bool v

(* Pamięć *)

module H = struct 

type t = ((value Map.Make(String).t ) list) * (value Map.Make(String).t) (*loc * glob *)
module StringMap = Map.Make(String)

let empty = ((StringMap.empty) :: [], StringMap.empty)



let rec find_loc l hs =
  match hs with 
  | [] -> None
  | h :: hs -> 
  begin match StringMap.find_opt l h with 
  | None -> find_loc l hs
  | Some c -> Some c
  end


let find l h = 
  match find_loc l (fst h) with 
  | None -> 
  begin match StringMap.find_opt l (snd h) with 
  | None -> failwith "brak!"
  | Some c -> c
  end
  | Some c -> c 

let is_loc l h = 
  let rec is_loc l h =
  match h with 
  | [] -> false
  | h :: hh -> 
  begin match StringMap.find_opt l h with 
  | None -> is_loc l hh
  | Some _ -> true
  end
  in is_loc l (fst h)  

let add l v h = 
  if is_loc l h then 
  let rec loc_add l v h =
  match h with 
  | [] -> failwith "!1"
  | h :: hh ->
  begin match StringMap.find_opt l h with 
  | None -> h :: loc_add l v hh
  | Some _ -> (StringMap.add l v h) :: hh
  end 
  in ( (loc_add l v (fst h), snd h))
  else ((fst h, StringMap.add l v (snd h)))




let loc_add l v (h : t) : t = 
 ((match fst h with 
  | [] -> failwith "!2"
  | h :: hh -> 
  (StringMap.add l v h) :: hh)
  , snd h)

let restore h = 
  ((match fst h with | [] -> failwith "!3" | _ :: h -> h) , snd h)

let add_level h =
  ( StringMap.empty :: (fst h),snd h)



end


type heap =  H.t

type 'a comp = heap -> 'a * heap

let return (v : 'a) : 'a comp =
  fun h -> (v, h)

let bind (c : 'a comp) (f : 'a -> 'b comp) : 'b comp =
  fun h -> let (v, h) = c h in f v h

let (let* ) = bind

let deref (l : ident) : value comp =
  fun h -> (H.find l h, h)

let loc_assgn (l : ident) (v : value) : unit comp =
  fun h -> ((), H.loc_add l v h)

let assgn (l : ident) (v : value) : unit comp =
  fun h -> ((), H.add l v h)



let rec fold_m2 (f : 'a -> unit comp) (xs : 'a list)
  : unit comp =
  match xs with
  | [] -> return ()
  | x :: xs' ->
      let* _ = f x in
      fold_m2 f xs'

let fold_m (f : 'a -> unit comp) (xs : 'a list) : unit comp =
  fun h -> ( () , H.restore (snd (fold_m2 f xs (   (H.add_level h)  )  )) )

(* interpreter *)

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

let eval_op (op : bop) : value -> value -> value comp =
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

let rec eval_expr (e : expr) : value comp =
  match e with
  | Int i -> return (VInt i)
  | Bool b -> return (VBool b)
  | Binop (op, e1, e2) ->
     let* v1 = eval_expr e1 in
     let* v2 = eval_expr e2 in
     eval_op op v1 v2
  | Var x -> deref x

let rec eval_stmt (s : stmt) : unit comp =
  match s with
  | Skip -> return ()
  | Assign (x, e) ->
      let* r = eval_expr e in
      assgn x r
  | LocAssign (x, e) ->
      let* r = eval_expr e in
      loc_assgn x r
  | If (b, e1, e2) ->
      let* vb = eval_expr b in
      (match vb with
      | VBool true -> eval_stmt e1
      | VBool false -> eval_stmt e2
      | _ -> failwith "type error")
  | While (b, e) ->
      let* vb = eval_expr b in
      (match vb with
      | VBool true ->
          let* _ = eval_stmt e in
          eval_stmt s
      | VBool false -> return ()
      | _ -> failwith "type error")
  | Print e ->
      let* r = eval_expr e in
      print_string (show_value r);
      print_newline ();
      return ()
  | Block ss -> fold_m eval_stmt ss

let eval_prog (p : prog) : unit comp =
  fold_m eval_stmt p

let interp (s : string) : unit =
  ignore (eval_prog (parse s) H.empty)
