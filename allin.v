Require Import List.
Import ListNotations.

Print map.

Lemma zad1 : forall {A B C : Type} (xs : list A)  (f : B -> C) 
(g : A -> B), 
(map f (map g xs)) = (map (fun x => f(g x) ) xs).
Proof.
intros A B C.
induction xs.
+ trivial.
+ simpl. intros f g. rewrite IHxs. trivial.
Qed.

Print app.

Locate "++".

Lemma append_nil_r {A : Type} (xs : list A) :
  xs ++ nil = xs.
Proof.
  induction xs.
  + reflexivity.
  + simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma append_nil_l {A : Type} (xs : list A) :
  nil  ++ xs = xs.
Proof.
trivial.
Qed.

Lemma append_assoc {A : Type}
  (xs ys zs : list A) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
  induction xs; simpl; [ trivial | ].
  rewrite IHxs.
  reflexivity.
Qed.

Lemma zad2help : 
forall {A : Type} (xs : list A) (ys : list A),
rev (xs ++ ys) = (rev ys) ++ (rev xs).
Proof.
intro A.
induction xs.
+ 
   simpl. intro ys. rewrite append_nil_r.
   reflexivity.
+ intro ys.
  simpl.  rewrite IHxs. 
  rewrite append_assoc. reflexivity.
  Qed.

Lemma zad2 : forall {A : Type} (xs : list A),
rev (rev xs) = xs.
Proof.
intro A.
induction xs.
+ trivial.
+ simpl. rewrite zad2help. simpl. 
rewrite IHxs. reflexivity.
Qed.

Print rev_append .

Lemma zad3help : forall {A : Type} (xs : list A)
(ys : list A),
rev_append xs ys = (rev_append xs []) ++ ys.
Proof.
intro A.

induction xs.
+ intro ys. trivial.
+ intro ys. simpl. 
rewrite IHxs. 
set (lhs := (rev_append xs [] ++ a :: ys)).
rewrite IHxs. 
unfold lhs.
rewrite append_assoc.
simpl. reflexivity.
Qed.




Lemma zad3help2 :
forall {A : Type} (xs : list A),
rev' xs = rev_append xs [].
Proof.
trivial.
Qed.


Lemma zad3help3 : 
forall {A : Type} (xs : list A) (a : A),
rev_append (xs ++ [a]) [] =
[a] ++ rev_append (xs) [].
Proof.
intro A.
induction xs.
+ intro a. auto.
+ intro b. simpl. rewrite zad3help.
rewrite IHxs. rewrite append_assoc.
set (lhs := [b] ++ rev_append xs [] ++ [a]).
rewrite zad3help.
unfold lhs.
trivial.
Qed.

Lemma zad3 : forall {A : Type} (xs : list A),
rev' (rev' xs) = xs.
Proof.
intro A.
induction xs.
+ trivial.
+ 
rewrite zad3help2.
rewrite zad3help2. simpl.
replace (rev_append xs [a]) with
(rev_append xs [] ++ [a]).
rewrite zad3help3. simpl.
replace ( rev_append (rev_append xs []) [] )
with (rev'(rev'(xs))).
rewrite IHxs.
trivial.
rewrite zad3help2. rewrite zad3help2.
trivial.
set (lhs := (rev_append xs [] ++ [a])).
rewrite zad3help. 
unfold lhs.
trivial.
Qed.

(*Zad 4*)

Definition Pierce {P : Prop} 
(f : ~~P -> P) : ((~P -> P) -> P) := 
fun g => (
f (fun np => np (g np))
).


(*Zad 5*)

Inductive nnf ( v : Set ) : Set :=
| NNFLit ( b : bool ) ( x : v )
| NNFConj ( f1 f2 : nnf v )
| NNFDisj ( f1 f2 : nnf v )
.

(* ppc = propositional calculus = rachunek zdań*)
Inductive ppc (v : Set)  :=
| Lit  (x : v)
| Conj (f1 : ppc v) (f2 : ppc v)
| Disj (f1 f2 : ppc v)
| Neg (f1 : ppc v)
| Imp (f1 f2 : ppc v)
.

Fixpoint T {v : Set} (phi : ppc v) : (nnf v) :=
match phi with
| Conj _ f1 f2 => NNFConj v (T f1) (T f2)  
| Neg _ f1 => F f1
| Lit _ x => NNFLit v (true) x
| Disj _ f1 f2 => NNFDisj v (T f1) (T f2)  
| Imp _ f1 f2 => NNFDisj v (F f1) (T f2)

end
with
F {v :Set} (phi : ppc v) : (nnf v) :=
match phi with
| Lit _ x => NNFLit v (false) x
| Conj _ f1 f2 => NNFDisj v (F f1) (F f2)  
| Disj _ f1 f2 => NNFConj v (F f1) (F f2)  
| Neg _ f1 => T f1
| Imp _ f1 f2 => NNFConj v (T f1) (F f2)
end.



(*Zad 6*)
(* Jeśli P zachodzi dla drzewa pustego
oraz dla wszystkich (l r : typ drzew o el. typu A)
oraz (x : A) jeśli P(l) i P(r) to P(Node(l,x,r))  
*)

Inductive tree :=
  | Leaf
  | Node (l : tree)  (x : nat)  (r : tree).

Definition swap_tree (t : tree) := 
match t with
| Leaf => Leaf
| Node l x r => Node r x l
end.

Lemma swap_tree_is_involution :
forall (t : tree), swap_tree (swap_tree t) = t.
Proof.
induction t. 
(*Tu Coq sformuluje zasade dla nas zasade indukcji*)
(*no prawie, bo to zasada konkretnie dla tego
lematu*)
+ trivial.
+ destruct t1. destruct t2. 
  - trivial.
  - trivial.
  - trivial.          
Qed.

(* "Matematyka jest sztuką mówienia 
'trywialnie' tak długo, aż druga strona się zgodzi"
-Arystoteles *)








