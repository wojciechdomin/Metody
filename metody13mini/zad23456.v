Require Import Utf8.
Require Import List.
Require Import Arith.
Require Import FunInd.

Import ListNotations.

Print gt.
Compute gt 2 5.

Print lt_dec.






Fixpoint is_sorted  (xs : list nat) : Prop :=
  match xs with 
  | [] => True 
  | x1 :: xs => 
    (match xs with 
    | [] => True
    | x2 :: xs' => if  gt_dec x1 x2 then False else
    is_sorted xs 
    end)
     
  end.

Fixpoint insert el xs :=
match xs with 
| h :: t => if gt_dec el h then h :: insert el t
 else el :: xs
| [] => el :: [] 
end.

Fixpoint insert_sort xs :=
match xs with 
| [] => []
| h :: t => insert h (insert_sort t)
end.
  
Compute insert_sort ([1;3;4;6;7;2;2;0;0;0;0;0]).

Lemma lemat1 : forall (a n : nat) (xs : list nat),
(is_sorted (a :: n :: xs) -> n >= a).
Proof.
intro. intro. intro.
simpl. destruct (gt_dec a n).
+ tauto.
+ intro. apply not_gt. assumption.
 
Qed.

Lemma lemat2 : forall (a n : nat) (xs : list nat),
is_sorted (a :: n :: xs) -> is_sorted (n :: xs).
Proof.
intros a n xs.
simpl.
destruct (gt_dec a n).
+ tauto.
+ intro. assumption.
Qed.




Lemma insert_sort_help1 :
forall   (xs :list nat ) (a : nat),
is_sorted xs -> is_sorted (insert a xs).
Proof.

induction xs.
+ auto. 
+ intro b.
  destruct xs.
  - simpl. destruct (gt_dec b a).
     * simpl.  
     intro.
     destruct (gt_dec a b).
     ++ apply Nat.lt_asymm with (n := a) (m := b).
       assumption.
       assumption.
     ++ tauto.
     * simpl. destruct (gt_dec b a).
       ++ intro. apply n in g.
        assumption.
       ++ intro. assumption.
   - intro. unfold insert.
   destruct (gt_dec b a).
   destruct (gt_dec b n).
   * replace (n
      :: (fix insert
            (el : nat) (xs0 : list nat) {struct
             xs0} : list nat :=
            match xs0 with
            | [] => [el]
            | h :: t =>
                if gt_dec el h
                then h :: insert el t
                else el :: xs0
            end) b xs) with (insert b (n::xs)).
      ++ simpl.
          destruct (gt_dec b n).
          destruct (gt_dec a n).
          --  apply lemat1 in H.
              apply (le_not_lt a n H g2).
          -- replace (n :: insert b xs) with 
              (insert b (n::xs)).
              ** apply IHxs.
              apply lemat2 in H.
              assumption.
              ** simpl.
              destruct (gt_dec b n).
              +++  reflexivity.
              +++ apply n1 in g0.
                  Search (False -> _).
                  apply except.
                  assumption.
           -- destruct (gt_dec a b).
              apply Nat.lt_asymm with (n := a) (m:= b).
              assumption.
              assumption.
              apply n0 in g0.
              apply except.
              assumption.
          ++ simpl. replace (fix insert
      (el : nat) (xs0 : list nat) {struct xs0} :
        list nat :=
      match xs0 with
      | [] => [el]
      | h :: t =>
          if gt_dec el h
          then h :: insert el t
          else el :: xs0
       end) with insert.
       -- destruct (gt_dec b n).
        trivial.
        apply n0 in g0. apply except. assumption.
       --     
        unfold insert.
         reflexivity.
     * simpl.
     destruct (gt_dec a b).
         destruct (gt_dec b n).
     ++ apply Nat.lt_asymm with (n :=a) (m :=b).
     assumption.
     assumption.
     ++ apply Nat.lt_asymm with (n :=a) (m :=b).
     assumption.
     assumption.
     ++     destruct (gt_dec b n).
        -- apply n0 in g0. assumption.
        -- destruct xs.
        tauto.
        destruct  (gt_dec n n3).
        ** apply lemat2 in H.
            apply lemat1 in H.
             apply gt_not_le in H.
             assumption.
             assumption.
        ** apply lemat2 in H.
        apply lemat2 in H.
        assumption.
     * simpl.
     destruct  (gt_dec b a).
     ++ apply n0 in g .
       assumption.
     ++ destruct (gt_dec a n).
        -- apply lemat1 in H.
            Search ( (_ > _) -> _).  
            apply gt_not_le in H.
            assumption.
            assumption.
        -- destruct xs.
          ** auto.
          ** destruct (gt_dec n n3).
            +++  apply lemat2 in H.
            apply lemat1 in H.
            apply gt_not_le in H.
            assumption.
            assumption.
            +++  apply lemat2 in H.
             apply lemat2 in H.
             assumption.
     
 Qed.
 
 
 
Theorem insert_sort_dziala : 
forall (xs : list nat), is_sorted (insert_sort (xs)).
Proof.
induction xs.
+ simpl. trivial.
+ simpl. set (ys := (insert_sort xs)).
 apply insert_sort_help1.
 unfold ys.
 assumption.
 Qed.


Print insert_sort_help1. 
 Extraction insert.
 Extraction insert_sort.



Inductive R : list nat -> list nat -> Prop :=
| case_nil  : R [] []
| case_cons : forall (x : nat) (xs ys : list nat),
            R xs ys -> R (x :: xs) (x :: ys)
| case_swap : forall (x y : nat) (xs : list nat),
            R (x :: y :: xs) (y :: x :: xs)
| case_trans: forall (xs ys zs : list nat),
    R xs ys -> R ys zs -> R xs zs 
.



Lemma my_theorem : R [] [].
Proof.
exact (case_nil).
Qed.

Lemma my_theorem2 : R [1] [1].
Proof.
exact (case_cons 1 [] [] (case_nil)).
Qed.

Lemma my_theorem3 : R [1] [1].
Proof.
apply case_cons.
apply case_nil.
Qed.

Lemma my_theorem4: R [3;2;1] [1;2;3].
Proof.
apply (case_trans [3; 2; 1] [2;3;1] [1; 2; 3]) .
+ apply case_swap.
+ apply (case_trans [2; 3; 1] [2;1;3] [1; 2; 3]).
  - apply case_cons.
    apply case_swap.
  - apply case_swap.
Qed.

Require Import Relation_Definitions.
Require Export Coq.Classes.RelationClasses.







Instance R_is_equivalence_relation : Equivalence R.
Proof.
split.
+ unfold Reflexive.
  induction x.
  - apply case_nil.
  - apply case_cons.
    apply IHx.
+ unfold Symmetric.
  
  intros.
  induction H.
  - apply case_nil.
  - apply case_cons.
    apply IHR.
  - apply case_swap.
  - apply (case_trans zs ys xs).
    * apply IHR2.
    * apply IHR1.
+ unfold Transitive.
  apply case_trans.
Qed.

Lemma insert_bangla : 
forall (ys xs  : list nat) (a : nat) ,
R ys xs -> R (insert a ys) (a :: xs).
Proof.

induction ys.
+ intro xs. intro a. intro.
inversion H.
- simpl. apply R_is_equivalence_relation.
- simpl. apply case_cons. apply H.
+ intro xs. intro b.  intro.
  simpl.
  destruct (gt_dec b a).
  - inversion H.
    * apply (case_trans 
      (a :: insert b ys) 
      (a:: b  :: ys0)
      (b :: a :: ys0)
      ).
      ++ apply case_cons.
         apply (IHys ys0 b H3).
      ++ apply case_swap.    
    * apply (case_trans
    (a :: insert b (y :: xs0))
    (b :: a :: y :: xs0)
     (b :: y :: a :: xs0)
     ).
     ++ apply (case_trans
     (a :: insert b (y :: xs0))
     (a :: b :: y :: xs0)
     (b :: a :: y :: xs0)
     ).
     -- apply case_cons.
      rewrite H2.     
      apply (IHys ys b).
      apply R_is_equivalence_relation.
     -- apply case_swap.
   ++ apply case_cons. apply case_swap.
  * apply (case_trans 
  (a :: insert b ys) 
  (a :: b :: ys)
  (b :: xs)
  ).
  ++ apply case_cons. apply IHys. 
     apply R_is_equivalence_relation.
  ++ apply (case_trans
  (a :: b :: ys) (b :: a :: ys) (b :: xs)
  ).
  -- apply case_swap.
  -- apply case_cons. apply H.
  - apply case_cons. apply H.
Qed.

Theorem insert_sort_returns_perm : 
forall (xs : list nat), R (insert_sort xs) xs.
Proof.
induction xs.
+ simpl. apply case_nil.
+ simpl.  apply (insert_bangla
(insert_sort xs) xs a).
apply IHxs. 
    
Qed.


(*zad 6*)

Print R_ind.

Inductive P : list nat -> list nat -> Prop :=
| case_weird  : P [3] [2]
.

Lemma bum :
forall (xs ys : list nat), R xs ys ->  P ys xs.
(* nieprawda ale to tylko w celu
pokazania reguły indukcji*)
Proof.
intros xs ys.
intro H.
induction H.
+ trivial. admit. (* P [] []*)
+ 
(*forall xs ys, R xs ys -> P ys xs
       -> P (x :: ys) (x :: xs) *) 
       admit.
+ (*forall x y xs, P (y :: x :: xs) (x :: y :: xs)*)
admit.
+ (*forall xs ys zs, 
R xs ys ->
R ys zs ->
P ys xs ->
P zs ys ->
P zs xs
*)
admit.
Admitted.

  
  
 



