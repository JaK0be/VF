Require Import ZArith.

Require Import List.

Set Implicit Arguments.

Open Scope Z_scope.
Inductive Sorted : list Z -> Prop := 
  | sorted0 : Sorted nil 
  | sorted1 : forall z:Z, Sorted (z :: nil) 
  | sorted2 : forall (z1 z2:Z) (l:list Z), 
        z1 <= z2 -> Sorted (z2 :: l) -> Sorted (z1 :: z2 :: l). 
Close Scope Z_scope.

Fixpoint count (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat     (* %nat to force the interpretation in nat, since have we open Z_scope *)
  | (z' :: l') =>
      match Z.eq_dec z z' with
      | left _ => S (count z l')
      | right _ => count z l'
      end
  end.

Definition Perm (l1 l2:list Z) : Prop :=
                                 forall z, count z l1 = count z l2.

Lemma Perm_cons : forall a l1 l2, Perm l1 l2 -> Perm (a::l1) (a::l2).
Proof.
  intros.
  unfold Perm. intro. simpl. elim (Z.eq_dec z a).
  - intros. rewrite Nat.succ_inj_wd. unfold Perm in H. apply H.
  - intros. unfold Perm in H; apply H.
Qed.


Lemma Perm_cons_cons : forall x y l, Perm (x::y::l) (y::x::l).
Proof.
  intros.
  unfold Perm.
  intros. simpl. elim (Z.eq_dec z x).
  - intros. elim (Z.eq_dec z y).
    + intros; reflexivity.
    + intros; reflexivity.
  - intros; elim (Z.eq_dec z y).
    + intros; reflexivity.
    + intros; reflexivity.
Qed.

(* ------------ *)

Require Import Recdef.

Function merge (p:list Z*list Z)
{measure (fun p=>(length (fst p))+(length (snd p)))} : list Z :=
  match p with
  | (nil,l) => l
  | (l,nil) => l
  | (x::xs,y::ys) => if Z_lt_ge_dec x y
                     then x::(merge (xs,y::ys))
                     else y::(merge (x::xs,ys))
  end.
  intros.
  simpl; auto with arith.
  intros. simpl. omega.
  Qed.


Theorem merge_correct : forall (p:list Z*list Z), Perm (merge p) ((fst p) ++ (snd p)) /\ Sorted (merge p).
Proof.
  Admitted.

(* Garante que o resultado é igual ao comprimento da lista *)
Definition comprimentoLista (A : Type) (l : list A) (res : nat) : Prop :=
            forall n:nat, n < res <-> exists a:A, nth_error l n = Some a.

Theorem comprimentoLista_correct : forall (A:Type) (l : list A), { n:nat | comprimentoLista l n }.
Proof.
  intros. unfold comprimentoLista. induction l.
  - exists 0. split.
    + intros. contradict H. omega.
    + intros. destruct H. contradict H. induction n.
      * simpl. discriminate.
      * simpl; discriminate.
  - destruct IHl. exists (S x). intros. induction n.
    + simpl. split.
      * intros. exists a; reflexivity.
      * intros. omega.
    + simpl; split.
      * intros. destruct i with n. apply H0. omega.
      * intros. destruct i with n. Search (S _ < S _). apply lt_n_S. exact (H1 H).
Qed.

Definition soma (A:Type) (l : list (A*nat)) (res : nat) : Prop :=
            res = fold_right (fun x y:nat => x+y) 0 (map (fun p => snd p) l).

Theorem soma_correct : forall (A:Type) (l : list(A*nat)), { n: nat | soma l n}.
Proof.
  unfold soma. intros. induction l.
  - simpl. exists 0. reflexivity.
  - simpl. destruct IHl. exists ((snd a) + x). subst. reflexivity.
Qed.

(* Set Extraction AccessOpaque.*)
Require Extraction. 

Extraction Language Haskell.

Recursive Extraction comprimentoLista_correct.

Recursive Extraction soma_correct.