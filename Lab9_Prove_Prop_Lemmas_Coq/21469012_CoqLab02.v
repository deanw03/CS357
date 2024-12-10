Section CoqLab02.

Context (A B C : Prop).

(***************************************************)
(* And / Or *)

Lemma q1 : (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  intros H.
  destruct H as [[HA HB] HC].
  split.
  - exact HA.
  - split.
    + exact HB.
    + exact HC.
Qed.

Lemma q2 : ((A /\ B) -> C) -> (A -> (B -> C)).
Proof.
  intros H HA HB.
  apply H.
  split.
  - exact HA.
  - exact HB.
Qed.

Lemma q3 : (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
  intros H.
  destruct H as [HAB | HC].
  - destruct HAB as [HA | HB].
    + left. exact HA.
    + right. left. exact HB.
  - right. right. exact HC.
Qed.

Lemma q4 : ((A \/ B) -> C) -> (A -> (B -> C)).
Proof.
  intros H HA HB.
  apply H.
  left. exact HA.
Qed.

(***************************************************)
(* Negation *)

Lemma q5 : (~A \/ B) -> (A -> B).
Proof.
  intros H HA.
  destruct H as [HNA | HB].
  - exfalso. apply HNA. exact HA.
  - exact HB.
Qed.

Lemma q6 : (A -> B) -> (~B -> ~A).
Proof.
  intros H HNB HA.
  apply HNB.
  apply H. exact HA.
Qed.

Lemma q7 : ~(A /\ ~A).
Proof.
  intros H.
  destruct H as [HA HNA].
  apply HNA. exact HA.
Qed.

(***************************************************)
(* De Morgan’s Laws *)

Hypothesis LEM : forall P : Prop, P \/ ~P.

Lemma q8 : ~(A \/ B) -> ~A /\ ~B.
Proof.
  intros H.
  split.
  - intros HA. apply H. left. exact HA.
  - intros HB. apply H. right. exact HB.
Qed.

Lemma q9 : ~A /\ ~B -> ~(A \/ B).
Proof.
  intros [HNA HNB].
  intros H.
  destruct H as [HA | HB].
  - apply HNA. exact HA.
  - apply HNB. exact HB.
Qed.

Lemma q10 : ~A \/ ~B -> ~(A /\ B).
Proof.
  intros H [HA HB].
  destruct H as [HNA | HNB].
  - apply HNA. exact HA.
  - apply HNB. exact HB.\
Qed.



Lemma q11 : ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros H.
  destruct (LEM A) as [HA | HNA].
  - destruct (LEM B) as [HB | HNB].
    + exfalso. apply H. split; assumption.
    + right. exact HNB.
  - left. exact HNA.
Qed.
End CoqLab02.