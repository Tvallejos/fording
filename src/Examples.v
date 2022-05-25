From MetaCoq.Fording Require Import Fording Testing.
From MetaCoq.Template Require Import utils. 

Inductive nonzero (A : Type) : nat -> Prop := 
  C m :  nonzero A (S m). 

Inductive nzexpected (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nzexpected A n.

(* MetaCoq Run (printInductive "nzexpected"). *)
MetaCoq Run (build_ind nonzero).
MetaCoq Run (cmp_inds "nonzero'" "nzexpected").

Inductive nList (A : Type) : nat -> Type :=
| nnil : nList A 0
| ncons : A -> forall m : nat, nList A m ->
              nList A (S m).

(* Inductive teq (A : Type) (n : nat) : Type :=
    | nileq : n = 0 -> teq A n 
    | conseq : A -> forall m : nat, teq A m ->
                    n = S m -> teq A n. *)

Inductive teq' (A : Type) (n : nat) : Type :=
    | nileq' : n = 0 -> teq' A n 
    | conseq' m : A -> teq' A m ->
                    n = S m -> teq' A n.

Inductive nList' (A : Type) : nat -> Type :=
| nnil' : nList' A 0
| ncons' m : A -> nList' A m ->
              nList' A (S m).

Inductive zList (A : Type) : nat -> Type :=
| znil : zList A 0.

Inductive zLexpected (A : Type) (n : nat) : Type :=
| znilexpected : n = 0 -> zLexpected A n.

MetaCoq Run (printInductive "zLexpected").
MetaCoq Run (build_ind zList).
MetaCoq Run (cmp_inds "zList'" "zLexpected").



                    
(* MetaCoq Run (build_ind teq).
MetaCoq Run (cmp_inds "nList'" "teq"). *)