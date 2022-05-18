From MetaCoq.Fording Require Import Fording Testing.
From MetaCoq.Template Require Import utils. 

Inductive nonzero (A : Type) : nat -> Prop := C m :  nonzero A (S m). 
Inductive nzexpected (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nzexpected A n.

MetaCoq Run (build_ind nonzero).
MetaCoq Run (cmp_inds "nonzero'" "nzexpected").


