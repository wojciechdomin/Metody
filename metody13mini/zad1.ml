let drukuj_zasade_indukcji typ = 
let nazwa = fst typ and definicja = snd typ in
let rec procesuj definicja =
let rec koniunkt lista n = 
match lista with 
| [] -> ""
| h :: [] -> "(x" ^ string_of_int n  ^ " : " ^ h ^ ")"
| h :: t  -> "(x" ^ string_of_int n  ^ "  : " ^ h ^ ") " ^ koniunkt t (n+1)  
in
let rec argumenty lista n = 
match lista with 
| [] -> ""
| _ :: [] -> "x" ^ string_of_int n  
| _ :: t  -> "x" ^ string_of_int n ^ " " ^ argumenty t (n+1)  
in match definicja with
| [] -> ""
| Ctor (nazwa,[]) :: [] -> "P(" ^ nazwa ^ ")" 
| Ctor (nazwa,lista) :: [] -> "forall " ^ koniunkt lista 0 ^ " =>  P(" ^ nazwa ^ argumenty lista 0 ^ ")"
| Ctor (nazwa,[]) :: reszta -> "P(" ^ nazwa ^ ") && " ^ procesuj reszta
| Ctor (nazwa,lista) :: reszta -> "forall " ^ koniunkt lista 0 ^ " =>  P(" ^ nazwa ^ argumenty lista 0 ^ ")" ^ " && " ^ procesuj reszta
in "(" ^ procesuj definicja ^ " ) => " ^ " forall (x : "^ nazwa ^ ") P (x)";;
