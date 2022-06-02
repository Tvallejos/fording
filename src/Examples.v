From MetaCoq.Fording Require Import Fording Testing.
From MetaCoq.Template Require Import utils. 

Inductive nonzero (A : Type) : nat -> Prop := 
  C m :  nonzero A (S m). 

Inductive nzexpected (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nzexpected A n.

Inductive nzexpected2 (A : Type) (n : nat) : Prop := 
  C2'' : forall m : nat,  n = S m -> nzexpected2 A n.

MetaCoq Run (printInductive "nonzero").
MetaCoq Run (build_ind nonzero).

About C.
About C'.
About C''.
About C2''.
MetaCoq Run (cmp_inds "nonzero'" "nzexpected").
MetaCoq Run (cmp_inds "nonzero'" "nzexpected2").


Inductive zList (A : Type) : nat -> Type :=
| znil : zList A 0.

Inductive zLexpected (A : Type) (n : nat) : Type :=
| znilexpected : n = 0 -> zLexpected A n.

MetaCoq Run (build_ind zList).
MetaCoq Run (cmp_inds "zList'" "zLexpected").

About znil'.
About znilexpected.

Inductive nList (A : Type) : nat -> Type :=
| nnil : nList A 0
| ncons : A -> forall m : nat, nList A m ->
              nList A (S m).

(* Inductive teq (A : Type) (n : nat) : Type :=
    | nileq : n = 0 -> teq A n 
    | conseq : A -> forall m : nat, teq A m ->
                    n = S m -> teq A n. *)

(* Inductive teq' (A : Type) (n : nat) : Type :=
    | nileq' : n = 0 -> teq' A n 
    | conseq' m : A -> teq' A m ->
                    n = S m -> teq' A n. *)

Inductive teqexpected (A : Type) (n : nat) : Type :=
    | nilteqexpected : n = 0 -> teqexpected A n 
    | consteqexpected : A -> forall m : nat, teqexpected A m ->
                    n = S m -> teqexpected A n.

(* Inductive teqexpected (A : Type) (n : nat) : Type :=
    | nilteqexpected : n = 0 -> teqexpected A n 
    | consteqexpected : A -> forall m : nat, teqexpected A m ->
                                                      n = S m -> teqexpected A n. *)

MetaCoq Run (printInductive "teqexpected").
MetaCoq Run (build_ind nList').
MetaCoq Run (cmp_inds "nList''" "teq'").

                    
(* MetaCoq Run (build_ind teq).
MetaCoq Run (cmp_inds "nList'" "teq"). *)