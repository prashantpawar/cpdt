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

Module exercise4.

(* 4. Reimplement the second example language of Chapter 2 to use mutually inductive types instead of dependent types. That is, define two separate (non-dependent) induc- tive types nat exp and bool exp for expressions of the two different types, rather than a single indexed type. To keep things simple, you may consider only the binary opera- tors that take naturals as operands. Add natural number variables to the language, as in the last exercise, and add an “if” expression form taking as arguments one boolean expression and two natural number expressions. Define semantics and constant-folding functions for this new language. Your constant folding should simplify not just binary operations (returning naturals or booleans) with known arguments, but also “if” ex- pressions with known values for their test expressions but possibly undetermined “then” and “else” cases. Prove that constant-folding a natural number expression preserves its meaning. *)

Inductive var : Set :=
  | vi : nat -> var.

Inductive nat_exp : Set :=
 | NConst : nat -> nat_exp
 | NPlus : nat_exp -> nat_exp -> nat_exp
 | NTimes : nat_exp -> nat_exp -> nat_exp
 | NVar : var -> nat_exp
 | NIf : bool_exp -> nat_exp -> nat_exp -> nat_exp

with bool_exp : Set :=
 | BConst : bool -> bool_exp
 | BEq : nat_exp -> nat_exp -> bool_exp
 | BLt : nat_exp -> nat_exp -> bool_exp.

Fixpoint nexpDenote (V : var -> nat) (e : nat_exp) : nat :=
  match e with
    | NConst n => n
    | NPlus ne1 ne2 => plus (nexpDenote V ne1) (nexpDenote V ne2)
    | NTimes n1 n2 => mult (nexpDenote V n1) (nexpDenote V n2)
    | NVar v => V v
    | NIf b neT neF => match (bexpDenote V b) with
                          | true => nexpDenote V neT
                          | false => nexpDenote V neF
                       end
  end

with bexpDenote (V : var -> nat) (be : bool_exp) : bool :=
  match be with
    | BConst b => b
    | BEq ne1 ne2 => beq_nat (nexpDenote V ne1) (nexpDenote V ne2)
    | BLt ne1 ne2 => Nat.leb (nexpDenote V ne1) (nexpDenote V ne2)
  end.

Definition replaceConstantInN (ne_op : nat_exp -> nat_exp -> nat_exp) (n_op : nat -> nat -> nat) (ne1 ne2 : nat_exp) :=
  match ne1 with
    | NConst n1 => match ne2 with
                    | NConst n2 => NConst (n_op n1 n2)
                    | _ => ne_op ne1 ne2
                  end
    | _ => ne_op ne1 ne2
  end.

Definition replaceConstantInB (be_op : nat_exp -> nat_exp -> bool_exp) (b_op : nat -> nat -> bool) (ne1 ne2 : nat_exp) :=
  match ne1 with
    | NConst n1 => match ne2 with
                    | NConst n2 => BConst (b_op n1 n2)
                    | _ => be_op ne1 ne2
                  end
    | _ => be_op ne1 ne2
  end.

Fixpoint nfold (e : nat_exp) : nat_exp :=
  match e with
    | NConst n => NConst n
    | NPlus ne1 ne2 => replaceConstantInN NPlus plus (nfold ne1) (nfold ne2)
    | NTimes ne1 ne2 => replaceConstantInN NTimes mult (nfold ne1) (nfold ne2)
    | NVar v => NVar v
    | NIf b ne1 ne2 => 
        match (bfold b) with
          | BConst b => if b then (nfold ne1) else (nfold ne2)
          | _ => NIf (bfold b) (nfold ne1) (nfold ne2)
        end
  end
with bfold (e : bool_exp) : bool_exp :=
  match e with
    | BConst b => BConst b
    | BEq ne1 ne2 => replaceConstantInB BEq beq_nat (nfold ne1) (nfold ne2)
    | BLt ne1 ne2 => replaceConstantInB BLt Nat.leb (nfold ne1) (nfold ne2)
  end.

Eval simpl in nfold (NConst 42).

Eval simpl in nfold (NPlus (NConst 2) (NConst 2)).

Eval simpl in nfold (NIf (BEq (NPlus (NConst 2) (NConst 4)) (NConst 7)) (NConst 1) (NConst 0)).

Print nat_exp_ind.

Scheme nat_exp_mut := Induction for nat_exp Sort Prop
with bool_exp_mut := Induction for bool_exp Sort Prop.

Print nat_exp_mut.

Theorem nfold_is_correct : forall V e,
  nexpDenote V (nfold e) = nexpDenote V e.
Proof.
  intros V.
  apply (nat_exp_mut
          (fun ne : nat_exp => nexpDenote V (nfold ne) = nexpDenote V ne)
          (fun be : bool_exp => bexpDenote V (bfold be) = bexpDenote V be));
    try (crush).
    - destruct (nfold n); destruct (nfold n0); crush.
    - destruct (nfold n); destruct (nfold n0); crush.
    - destruct (bfold b); crush.
      + rewrite <- H0; rewrite <- H1; destruct (bexpDenote V b); crush.
    - destruct (nfold n); destruct (nfold n0); crush.
    - destruct (nfold n); destruct (nfold n0); crush.
Qed.

End exercise4.


Module exercise5.

(* 5. Define mutually inductive types of even and odd natural numbers, such that any nat- ural number is isomorphic to a value of one of the two types. (This problem does not ask you to prove that correspondence, though some interpretations of the task may be interesting exercises.) Write a function that computes the sum of two even numbers, such that the function type guarantees that the output is even as well. Prove that this function is commutative. *)


Inductive even : Set :=
  | Zero : even
  | Seven : odd -> even
with odd : Set :=
  | Sodd : even -> odd.

(* Scheme odd_mut := Induction for odd Sort Prop
with even_mut := Induction for even Sort Prop. *)

Scheme even_mut := Induction for even Sort Prop
with odd_mut := Induction for odd Sort Prop.

Eval simpl in Seven (Sodd Zero).
Eval simpl in Seven (Sodd (Seven (Sodd Zero))).

Fixpoint sum_even (e1 e2 : even) : even :=
  match e1 with
    | Zero => e2
    | Seven o1 => match e2 with
                   | Zero => e1
                   | Seven o2 => Seven (Sodd (sum_odd o1 o2))
                  end
  end
with sum_odd (o1 o2 : odd) : even :=
  match o1 with
    | Sodd e1 => match o2 with
                   | Sodd e2 => Seven (Sodd (sum_even e1 e2))
                 end
  end.

Fixpoint efold (e : even) : nat :=
  match e with
    | Zero => 0
    | Seven o => S (ofold o)
  end
with ofold (o : odd) : nat :=
  match o with
    | Sodd e => S (efold e)
  end.

Eval simpl in efold (Seven (Sodd Zero)). (* 2 *)
Eval simpl in efold (Seven (Sodd (Seven (Sodd Zero)))). (* 4 *)

Eval simpl in efold (sum_even (Seven (Sodd Zero)) (Seven (Sodd (Seven (Sodd Zero))))). (* 2 + 4 = 6 *)

Eval simpl in ofold (Sodd Zero). (* 1 *)
Eval simpl in ofold (Sodd (Seven (Sodd Zero))). (* 3 *)
Eval simpl in efold (sum_odd (Sodd Zero) (Sodd (Seven (Sodd Zero)))). (* 1 + 3 = 4 *)

Theorem sum_even_is_correct : forall e1 e2,
  efold (sum_even e1 e2) = plus (efold e1) (efold e2).
Proof.
  apply (even_mut
    (fun e1 : even => forall e2 : even,
      efold (sum_even e1 e2) = plus (efold e1) (efold e2))
    (fun o1 : odd => forall o2 : odd,
      efold (sum_odd o1 o2) = plus (ofold o1) (ofold o2))); crush.
  - destruct e2; crush.
  - destruct o2; crush.
Qed.

Theorem sum_of_two_even_is_even : forall (e1 e2 : even),
  sum_even e1 (Seven (Sodd e2)) = Seven (Sodd (sum_even e1 e2)).
Proof.
  intros.
  apply (even_mut
    (fun e1 : even => forall e2 : even,
      sum_even e1 (Seven (Sodd e2)) = Seven (Sodd (sum_even e1 e2)))
    (fun o1 : odd => forall o2 : odd,
      sum_odd o1 (Sodd (Seven o2)) = Seven (Sodd (sum_odd o1 o2)))); crush.
  - rewrite <- H. destruct e0; crush. destruct o; induction e; crush.
  - rewrite <- H. destruct e; destruct o2; crush.
Qed.

Theorem sum_even_comm : forall e1 e2,
  sum_even e1 e2 = sum_even e2 e1.
Proof.
  apply (even_mut
    (fun e1 : even => forall e2 : even,
      sum_even e1 e2 = sum_even e2 e1)
    (fun o1 : odd => forall o2 : odd,
      sum_odd o1 o2 = sum_odd o2 o1)); crush.
  - induction e2; crush.
  - induction e2; crush.
  - induction o2; crush.
Qed.

End exercise5.

Module exercise6.

(* 6. Using a reflexive inductive definition, define a type nat tree of infinitary trees, with natural numbers at their leaves and a countable infinity of new trees branching out of each internal node. Define a function increment that increments the number in every leaf of a nat tree. Define a function leapfrog over a natural i and a tree nt. leapfrog should recurse into the ith child of nt, the i+1st child of that node, the i+2nd child of the next node, and so on, until reaching a leaf, in which case leapfrog should return the number at that leaf. Prove that the result of any call to leapfrog is incremented by one by calling increment on the tree. *)

Inductive nat_tree : Set :=
  | NLeaf : nat -> nat_tree
  | NNode : (nat -> nat_tree) -> nat_tree.

Eval simpl in (NLeaf 4).

Fixpoint increment (ntr : nat_tree) : nat_tree :=
  match ntr with
    | NLeaf n => NLeaf (n + 1)
    | NNode f => NNode (fun n => increment (f n))
  end.

Eval simpl in increment (NLeaf 4).

Fixpoint leapfrog (i : nat) (nt : nat_tree) : nat :=
  match nt with
  | NLeaf n => n
  | NNode f => leapfrog (i + 1) (f i)
  end.

Theorem leapfrog_incremented : forall tr n,
  leapfrog n (increment tr) = leapfrog n tr + 1.
Proof.
  induction tr; crush.
Qed.

End exercise6.

Module exercise7.

(* 7. Define a type of trees of trees of trees of (repeat to infinity). That is, define an inductive type trexp, whose members are either base cases containing natural numbers or binary trees of trexps. Base your definition on a parameterized binary tree type btree that you will also define, so that trexp is defined as a nested inductive type. Define a function total that sums all of the naturals at the leaves of a trexp. Define a function increment that increments every leaf of a trexp by one. Prove that, for all tr, total (increment tr) ≥ total tr. On the way to finishing this proof, you will probably want to prove a lemma and add it as a hint using the syntax Hint Resolve name of lemma. *)

Inductive btree (T : Set) : Set :=
  | Leaf : T -> btree T
  | Node : btree T -> btree T -> btree T.

Arguments Leaf {T} _.
Arguments Node {T} _ _.

Inductive trexp : Set :=
  | BaseN : nat -> trexp
  | Btree : btree trexp -> trexp.

Fixpoint total (t : trexp) : nat :=
  match t with
  | BaseN n => n
  | Btree bt => (fix btotal (bt : btree trexp) : nat :=
                  match bt with
                  | Leaf t => total t
                  | Node l r => (btotal l) + (btotal r)
                  end
                 ) bt
  end.

Fixpoint increment (t : trexp) : trexp :=
  match t with
  | BaseN n => BaseN (n + 1)
  | Btree bt => Btree ((fix bincrement (bt : btree trexp) : btree trexp :=
                  match bt with
                  | Leaf t => Leaf (increment t)
                  | Node l r => Node (bincrement l) (bincrement r)
                  end) bt)
  end.
 
Print trexp_ind.
Check trexp_ind.

Section trexp_ind'.
  Variable P : trexp -> Prop.

  Hypothesis BaseN_case : forall (n : nat), P (BaseN n).
  Hypothesis Btree_case_leaf : forall (t : trexp), 
    P t -> P (Btree (Leaf t)).
  Hypothesis Btree_case_node : forall (bl br : btree trexp),
    P (Btree bl) -> P (Btree br) -> P (Btree (Node bl br)).

  Fixpoint trexp_ind' (t : trexp) : P t :=
    match t with
    | BaseN n => BaseN_case n
    | Btree bt => (fix btrexp_ind' (bt : btree trexp) : P (Btree bt) := 
                    match bt with
                    | Leaf tr => Btree_case_leaf (trexp_ind' tr) 
                    | Node bl br => Btree_case_node (btrexp_ind' bl) (btrexp_ind' br)
                  end) bt
    end.
End trexp_ind'.

Theorem total_tree : forall tr,
  total (increment tr) >= total tr.
Proof.
  induction tr using trexp_ind'; crush.
Qed.


















































