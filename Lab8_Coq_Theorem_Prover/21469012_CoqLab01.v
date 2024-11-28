Section CoqLab01.
Context (A B C D : Prop).

Lemma q1 : (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros H1 H2.
  intro HA.
  apply H2.
  apply H1.
  exact HA.
Qed.

Lemma q2 : A -> A.
Proof.
  intro HA.
  exact HA.
Qed.

Lemma q3 : A -> (B -> A).
Proof.
  intro HA.
  intro HB.
  exact HA.
Qed.

Lemma q4 : (A -> B -> C) -> B -> A -> C.
Proof.
  intros H1 HB HA.
  apply H1.
  exact HA.
  exact HB.
Qed.

Lemma q6 : (A -> A -> B) -> A -> B.
Proof.
  intros H1 HA.
  apply H1.
  exact HA.
  exact HA.
Qed.

Lemma q7 : (A -> B) -> A -> A -> B.
Proof.
  intros H1 HA1 HA2.
  apply H1.
  exact HA1.
Qed.

Lemma q8 : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D.
Proof.
  intros H1 H2 H3 HA.
  apply H3.
  apply H1.
  exact HA.
  apply H2.
  exact HA.
Qed.
Require Import Classical.
Lemma q9 : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  apply NNPP.
  intro H.
  apply H.
Admitted.
End CoqLab01.
