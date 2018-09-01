Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

Require Import Bool Arith.

(* Exercises *)

Module exercise1.

(* 1. Define an inductive type truth with three constructors, Yes, No and Maybe. Yes stands for certain truth, No for certain falsehood, and Maybe for an unknown situation. Define "not", "and", and "or" for this replacement boolean algebra. Prove that your implementation of "and" is commutative and distributes over your implementation of "or". *)

Inductive ynm : Set :=
 | Yes : ynm
 | No : ynm
 | Maybe : ynm.

Definition not_ynm (y : ynm) : ynm :=
  match y with
    | Yes => No
    | No => Yes
    | Maybe => Maybe
  end.

Definition and_ynm (y1 y2 : ynm) : ynm :=
  match y1 with
    | Yes => y2
    | No => No
    | Maybe => match y2 with
                | No => No
                | _ => Maybe
               end
  end.

Definition or_ynm (y1 y2 : ynm) : ynm :=
  match y1 with
    | Yes => Yes
    | No => y2
    | Maybe => match y2 with
                | Yes => Yes
                | _ => Maybe
               end
  end.

Theorem and_ynm_comm : forall y1 y2 : ynm,
  and_ynm y1 y2 = and_ynm y2 y1.
Proof.
  induction y1, y2; crush.
Qed.

Theorem or_distributes_over_and : forall P Q R,
  or_ynm P (and_ynm Q R) = and_ynm (or_ynm P Q) (or_ynm P R).
Proof.
  induction P, Q, R; crush.
Qed.

End exercise1.


Module exercise2.

(* 2. Define an inductive type slist that implements lists with support for constant-time concatenation. This type should be polymorphic in a choice of type for data values in lists. The type slist should have three constructors, for empty lists, singleton lists, and concatenation. Define a function flatten that converts slists to lists. (You will want ot run Require Import List. to bring list definitions into scope.) Finally, prove that flatten distributes over concatenation, where the two sides of your qualified equality will use slist and list version of concatenation, as appropriate. Recall from Chapter 2 that the infix operator ++ is syntatic sugar for the list concatenation function app. *)

Inductive slist (T : Set) : Set :=
 | sNil : slist T
 | sSingl : T -> slist T
 | sConcat : slist T -> slist T -> slist T.

Fixpoint flatten T (sl : slist T) : list T :=
  match sl with
    | sNil => []
    | sSingl t => [t]
    | sConcat sl1 sl2 => flatten (sl1) ++ flatten (sl2)
  end.


Theorem flatten_distributes_over_concat : forall T (sl1 sl2 : slist T),
  flatten (sConcat sl1 sl2) = (flatten sl1) ++ (flatten sl2).
Proof.
  induction sl1; crush.
Qed.

End exercise2.

Module exercise3.

(* 3. Modify the first example language of Chapter 2 to include variables, where variables are represented with nat. Extend the syntax and semantics of expressions to accommodate the change. Your new expDenote function should take as a new extra first argument a value of type var → nat, where var is a synonym for naturals-as-variables, and the function assigns a value to each variable. Define a constant folding function which does a bottom-up pass over an expression, at each stage replacing every binary operation on constants with an equivalent constant. Prove that constant folding preserves the meanings of expressions. *)

Inductive binop : Set := Plus | Times.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

Inductive var : Set :=
  | vi : nat -> var.

Inductive exp : Set :=
  | Const : nat -> exp
  | Assign : var -> exp
  | Binop : binop -> exp -> exp -> exp.

Fixpoint expDenote (V : var -> nat) (e : exp) : nat :=
  match e with
    | Const n => n
    | Assign vn => V vn
    | Binop b e1 e2 => (binopDenote b) (expDenote V e1) (expDenote V e2)
  end.

Definition replaceConstant (b : binop) (e1 e2 : exp) : exp :=
  match e1 with
    | Const n1 => match e2 with
                    | Const n2 => Const ((binopDenote b) n1 n2)
                    | _ => Binop b e1 e2
                  end
    | _ => Binop b e1 e2
  end.

Fixpoint fold (e : exp) : exp :=
  match e with
    | Const n => Const n
    | Assign vn => Assign vn
    | Binop b e1 e2 => replaceConstant b (fold e1) (fold e2)
  end.

Eval simpl in fold (Const 42).

Eval simpl in fold (Binop Plus (Const 2) (Const 2)).

Eval simpl in fold (Binop Times (Binop Plus (Const 2) (Const 4)) (Const 7)).

Theorem fold_preserves_meaning : forall G e,
  expDenote G (fold e) = expDenote G e.
Proof.
  induction e; crush.
  - destruct (fold e1); destruct (fold e2); crush.
Qed.

End exercise3.























