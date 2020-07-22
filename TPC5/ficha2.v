Require Import List.

Set Implicit Arguments.

Print List.

Fixpoint sum (l : list nat) : nat :=
match l with
  | nil => 0
  | cons h tail => 
    let n:= sum tail in h + n
end.


Eval compute in sum(cons 5 (cons 5 (cons 5 nil))).

Print "++".
Print rev.
Print length.
Print map.

Lemma ex3_1 : forall (l1 : list nat) (l2 : list nat), sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  induction l1.
  - intro. simpl. reflexivity.
  - simpl. intro. rewrite IHl1. rewrite PeanoNat.Nat.add_assoc. reflexivity.
Qed.

Lemma ex3_2 : forall (A:Type) (l:list A), length (rev l) = length l.
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite app_length. simpl. rewrite IHl. rewrite PeanoNat.Nat.add_comm. reflexivity.
Qed.

Lemma ex3_3 : forall (A B:Type) (f:A->B) (l1 l2:list A), (map f l1)++(map f l2) = map f (l1++l2).
Proof.
  induction l1.
  - induction l2.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - induction l2.
    + simpl. rewrite <- IHl1. simpl. reflexivity.
    + simpl. rewrite <- IHl1. simpl. reflexivity.
Qed.

Lemma ex3_4 : forall (A B:Type) (f:A->B) (l:list A), rev (map f l) = map f (rev l).
Proof.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. rewrite map_app. simpl. reflexivity.
Qed.



Print In.

Inductive In (A:Type) (y:A) : list A -> Prop :=
| InHead : forall xs:list A, In y (cons y xs)
| InTail : forall (x:A) (xs:list A), In y xs -> In y (cons x xs).

Print In.

Lemma ex4_1_aux : forall (A:Type) (x:A) (l1 l2: list A), (In x l1 \/ In x l2) -> In x (l1 ++ l2).
Proof.
  intros.
  destruct H as [H|H].
  - induction H.
    + rewrite <- app_comm_cons. apply InHead.
    + rewrite <- app_comm_cons. apply InTail. assumption.
  - induction l1.
    + simpl. assumption.
    + rewrite <- app_comm_cons. apply InTail. assumption.
Qed.

Lemma ex4_1 : forall (A:Type) (x:A) (l:list A), In x l -> In x (rev l).
Proof.
  intros.
  induction H.
  - simpl.
    apply ex4_1_aux.
    right.
    apply InHead.
  - simpl.
    apply ex4_1_aux.
    left.
    assumption.
Qed.

Lemma ex4_2 : forall (A B:Type) (y:B) (f:A->B) (l:list A), In y (map f l) -> exists x, In x l /\ y = f x.
Proof.
  intros.
  induction l.
  - simpl in H. inversion H.
  - simpl in H. inversion H.
    * exists a. split.
      + apply InHead.
      + reflexivity.
    * cut (exists x:A, In x l /\ y = f x).
      + intro. destruct H3. exists x0. destruct H3 as [H3 H4]; split.
        -- constructor; assumption.
        -- assumption.
      + exact (IHl H1).
Qed.

Lemma ex4_3 : forall (A:Type) (x:A) (l :list A), In x l -> exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  + exists nil. exists xs. simpl. reflexivity.
  + destruct IHIn as [I1 H1]. destruct H1 as [I2 H1]. exists (x0::I1). exists I2. rewrite <-app_comm_cons. rewrite H1; reflexivity.
Qed.


Inductive Prefix (A:Type) : list A -> list A -> Prop :=
| PreNil : forall l:list A, Prefix nil l
| PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).

Lemma ex5_1 : forall (A:Type) (l1 l2:list A), Prefix l1 l2 -> length l1 <= length l2.
Proof.
  intros.
  induction H.
  - simpl. intuition.
  - simpl. rewrite <- PeanoNat.Nat.succ_le_mono. assumption.
Qed.

Lemma ex5_2 : forall l1 l2, Prefix l1 l2 -> sum l1 <= sum l2.
Proof.
  intros.
  induction H.
  - simpl; intuition.
  - simpl. apply Plus.plus_le_compat_l. assumption.
Qed.

Lemma ex5_3 : forall (A:Type) (l1 l2:list A) (x:A), (In x l1) /\ (Prefix l1 l2) -> In x l2.
Proof.
  intros.
  destruct H as [H1 H2].
  induction H2.
  + induction l.
    - assumption.
    - apply InTail. assumption.
  + inversion H1.
    - constructor.
    - constructor. apply IHPrefix. assumption.
Qed.


Inductive SubList (A:Type) : list A -> list A -> Prop :=
| SLnil : forall l:list A, SubList nil l
| SLcons1 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList (x::l1) (x::l2)
| SLcons2 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList l1 (x::l2).

Lemma ex6_1 : forall (A:Type)(l1 l2 l3 l4:list A), SubList l1 l2 -> SubList l3 l4 -> SubList (l1++l3) (l2++l4).
Proof.
  intros.
  induction H.
  - simpl. induction l.
    + simpl; assumption.
    + rewrite <- app_comm_cons. constructor. assumption.
  - rewrite <- app_comm_cons; constructor; assumption.
  - rewrite <- app_comm_cons; constructor; assumption.
Qed.

Lemma ex6_2 : forall (A:Type) (l1 l2:list A), SubList l1 l2 -> SubList (rev l1) (rev l2).
Proof.
Admitted.

Lemma ex6_3 : forall (A:Type) (x:A) (l1 l2:list A), Prefix l1 l2 -> SubList l1 l2.
Proof.
  intros.
  induction H.
  - apply SLnil.
  - apply SLcons1. assumption.
Qed.

Lemma ex6_4 : forall (A:Type) (x:A) (l1 l2:list A), SubList l1 l2 -> In x l1 -> In x l2.
Proof.
  intros.
  induction H.
  - induction l.
    + assumption.
    + apply InTail. assumption.
  - inversion H0. 
    + apply InHead. 
    + apply InTail. apply IHSubList. assumption.
  - apply InTail. apply IHSubList; assumption.
Qed.