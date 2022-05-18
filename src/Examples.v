From MetaCoq.Fording Require Import Fording Testing.
From MetaCoq.Template Require Import utils. 

Inductive nonzero (A : Type) : nat -> Prop := C m :  nonzero A (S m). 
Inductive nzexpected (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nzexpected A n.

MetaCoq Run (build_ind nonzero).
MetaCoq Run (cmp_inds "nonzero'" "nzexpected").

Inductive nList (A : Type) : nat -> Type :=
| nnil : nList A 0
| ncons : A -> forall m : nat, nList A m ->
              nList A (S m).

Inductive teq (A : Type) (n : nat) : Type :=
    | nileq : n = 0 -> teq A n 
    | conseq : A -> forall m : nat, teq A m 
                    -> forall (e : n = S m), teq A n.

MetaCoq Run (build_ind nList).
MetaCoq Run (cmp_inds "nList'" "teq").