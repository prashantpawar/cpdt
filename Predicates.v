Require Import List.
Require Import CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Print unit.

Print True.


(* Propositional Logic *)
Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
  Proof.
    apply I.
  Qed.

  Theorem obvious' : True.
  Proof.
    constructor.
  Qed.

  Print False.

  Theorem False_imp : False -> 2 + 2 = 5.
  Proof.
    destruct 1.
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
  Proof.
    intro.
    elimtype False.
    crush.
  Qed.

  Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
  Proof.
    unfold not.
    crush.
  Qed.

  Print and.

  Theorem and_comm : P /\ Q -> Q /\ P.
  Proof.
    destruct 1.
    split.
    assumption.
    assumption.
  Qed.

  Print or.

  Theorem or_comm : P \/ Q -> Q \/ P.
  Proof.
    destruct 1.
    right; assumption.
    left; assumption.
  Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
  Proof.
    tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
  Proof.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
  Proof.
    Hint Rewrite app_length.
    crush.
  Qed.

End Propositional.


































