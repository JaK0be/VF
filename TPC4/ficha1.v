(* =============================================================== *)
(* =================== Lógica Proposicional ====================== *)
(* =============================================================== *)

Section LP.

Variables A B C :Prop.

Check A.
Check B.
Check C.

Lemma ex1 : (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  intro.
  destruct H as [H1|H2].
  - destruct H1 as [H2|H3].
    left;assumption.
    right;left;assumption.
  - right;right;assumption.
Qed.

Lemma ex2 : (B -> C) -> A \/ B -> A \/ C.
Proof.
  intros.
  destruct H0 as [H0|H1].
  - left.
    assumption.
  - right; apply H;assumption.
Qed.

Lemma ex3 : (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  split.
  - destruct H as [H1 H2].
    destruct H1 as [H1 H3].
    assumption.
  - destruct H as [H1 H2].
    split.
    * destruct H1 as [H1 H3].
      assumption.
    * assumption.
Qed.

Lemma ex4 : A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
  intro.
  split.
  - destruct H as [H1|H2].
    * left.
      assumption.
    * right.
      destruct H2 as [H2 H3].
      assumption.
  - destruct H as [H1|H2].
    * left; assumption. 
    * right; destruct H2 as [H2 H3];assumption.
Qed.

Lemma ex5 : (A /\ B) \/ (A /\ C) <-> A /\ (B \/ C).
Proof.
  split.
  - intro.
    destruct H as [H1|H2].
    * destruct H1 as [H1 H2].
      split.
      + assumption.
      + left; assumption.
    * destruct H2 as [H1 H2].
      split.
      + assumption.
      + right; assumption.
  - intro.
    destruct H as [H1 H2].
    destruct H2 as [H2|H3].
    * left. split.
      + assumption.
      + assumption.
    * right. split.
      + assumption.
      + assumption.
Qed.

Lemma ex6 : (A \/ B) /\ (A \/ C) <-> A \/ (B /\ C).
Proof.
  split.
  - intro.
    destruct H as [H1 H2].
    destruct H1 as [H1|H3].
    + left. assumption.
    + destruct H2 as [H2|H4].
      * left. assumption.
      * right. split.
        -- assumption.
        -- assumption.
  - intro.
    destruct H as [H1|H2].
    * split.
      + left. assumption.
      + left. assumption.
    * destruct H2 as [H4 H5].
      split.
      + right; assumption.
      + right; assumption.
Qed.

End LP.

(* =============================================================== *)
(* ====================  Lógica Primeira Ordem =================== *)
(* =============================================================== *)

Section LPO.

Variable X :Set.
Variable x y :X. 
Variables P Q R : X -> Prop.

Lemma ex7 : (forall x, P x /\ Q x )-> ((exists x, P x) /\ (exists x, Q x)).
Proof.
  intros.
  split.
  - exists x. apply H.
  - exists x. apply H. 
Qed.

Variables G : X -> X -> Prop.

Lemma ex8 : (exists x, forall y, G x y) -> forall y, exists x, G x y.
Proof.
  intros.
  destruct H as [x0 H1].
  exists x0.
  apply H1.
Qed.

Lemma ex9 : (exists x, P x) -> (forall x, forall y, P x -> Q y) -> (forall y, Q y).
Proof.
  intros.
  destruct H as [x0 H1].
  firstorder. (*apply H0 - Não percebi o porquê de esta transformação não funcionar, apesar de ter P x0, dizia que não conseguia encontrar um x *)
Qed.

Lemma ex10 : (forall x, Q x -> R x) -> (exists x, P x /\ Q x) -> exists x, P x /\ R x.
Proof.
  intro.
  intro.
  destruct H0 as [x0 H1].
  destruct H1 as [H2 H3].
  exists x0.
  split.
  - exact H2.
  - apply H. exact H3. 
Qed.

Lemma ex11 : (forall x, P x -> Q x) -> (exists x, P x) -> exists y, Q y.
Proof.
  intros.
  destruct H0 as [z H1].
  exists z.
  apply H.
  assumption.
Qed.

Lemma ex12 : (exists x, P x) \/ (exists x, Q x) <-> (exists x, P x \/ Q x).
Proof.
  split.
  - intro.
    destruct H as [H1|H2].
    * destruct H1 as [x0 H3].
      exists x0.
      left. assumption.
    * destruct H2 as [x0 H4].
      exists x0.
      right. assumption.
  - intro.
    destruct H as [x0 H1].
    destruct H1 as [H2|H3].
    * left; exists x0; assumption.
    * right; exists x0; assumption.
Qed.

End LPO.

(* =============================================================== *)
(* =======================  Lógica Clássica ====================== *)
(* =============================================================== *)

Section LC.


Variable X :Set.
Variable x :X.
Variable A B : Prop.
Variable P : X -> Prop.


Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.


Lemma ex13 : ((A -> B) -> A) -> A.
Proof.
  intro H.
  destruct excluded_middle with A.
  - exact H0.
  - apply H.
    intro.
    contradiction.
Qed. 

Lemma ex14: ~~A -> A.
Proof.
  intro.
  destruct excluded_middle with A.
  - exact H0.
  - contradiction.
Qed.

Lemma ex15 : ~(forall x, P x) -> (exists x, ~P x).
Proof.
  intro H.
  destruct excluded_middle with (exists x, ~ P x).
  - exact H0.
  - destruct H.
    intro x0.
    destruct excluded_middle with (P x0).
    * assumption.
    * destruct H0.
      exists x0.
      assumption.
Qed.

End LC.
  