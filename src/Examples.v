From MetaCoq.Fording Require Import Fording Testing.
From MetaCoq.Template Require Import utils All. 
(* From MetaCoq.PCUIC Require Import Bidirectional.BDTyping. *)

Inductive nonzero (A : Type) : nat -> Prop := 
  C m :  nonzero A (S m). 


Inductive nzexpected (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nzexpected A n.


Inductive nzexpected2 (A : Type) (n : nat) : Prop := 
  C2'' : forall m : nat,  n = S m -> nzexpected2 A n.


MetaCoq Run (build_ind nonzero).
MetaCoq Run (cmp_inds "nonzero'" "nzexpected").
MetaCoq Run (cmp_inds "nonzero'" "nzexpected2").


Inductive zList (A : Type) : nat -> Type :=
| znil : zList A 0.


Inductive zLexpected (A : Type) (n : nat) : Type :=
| znilexpected : n = 0 -> zLexpected A n.


MetaCoq Run (build_ind zList).
MetaCoq Run (cmp_inds "zList'" "zLexpected").


Inductive nList (A : Type) : nat -> Type :=
| nnil : nList A 0
| ncons : A -> forall m : nat, nList A m ->
              nList A (S m).


Inductive teqexpected (A : Type) (n : nat) : Type :=
    | nilteqexpected : n = 0 -> teqexpected A n 
    | consteqexpected : A -> forall m : nat, teqexpected A m ->
                    n = S m -> teqexpected A n.


MetaCoq Run (build_ind nList).
MetaCoq Run (cmp_inds "nList'" "teqexpected").


Inductive my_le (n:nat) : nat -> Prop :=
| my_le_n: my_le n n 
| my_le_S: forall m, my_le n m -> my_le n (S m).


Inductive le_expected (n m : nat) : Prop :=
| le_expected_n: n = m -> le_expected n m 
| le_expected_S: forall x, le n x -> m = S x -> le_expected n m.


MetaCoq Run (build_ind my_le).
MetaCoq Run (cmp_inds "my_le'" "le_expected").


Inductive List_3idx (A : Type) : string -> bool -> nat -> Type :=
| tweidxnil : List_3idx A "" true (S (S 0)).


Inductive three_idx_ex (A : Type) (s :string) (b :bool) (m : nat) : Type :=
    | nil_o_ex : s = "" -> b = true -> m = S (S 0) -> three_idx_ex A s b m.


MetaCoq Run (build_ind List_3idx).
MetaCoq Run (cmp_inds "List_3idx'" "three_idx_ex").


Inductive List_cons (A : Type) : nat -> nat -> Type :=
| jcons : A -> forall o p: nat, List_cons A o p ->
              List_cons A (S o) (S (S p)).


Inductive cons_ex (A : Type) (n m : nat) : Type :=
    | jcons_size_ex : A -> forall m' m'' : nat, cons_ex A m' m'' ->
                    n = S m' -> m = S (S m'') -> cons_ex A n m.
                    

MetaCoq Run (build_ind List_cons).
MetaCoq Run (cmp_inds "List_cons'" "cons_ex").


Inductive List_2size (A : Type) : nat -> nat -> Type :=
| n2nil : List_2size A 0 0
| n2cons : A -> forall o p: nat, List_2size A o p ->
              List_2size A (S o) (S (S p)).


Inductive size_ex (A : Type) (n m : nat) : Type :=
    | nil_size_ex' : n = 0 -> m = 0 -> size_ex A n m 
    | cons_size_ex : A -> forall m' m'' : nat, size_ex A m' m'' ->
                    n = S m' -> m = S (S m'') -> size_ex A n m.


MetaCoq Run (build_ind List_2size).
MetaCoq Run (cmp_inds "List_2size'" "size_ex").


Inductive zero : nat -> Prop :=
 | ezero : zero 0 
 with one : nat -> Prop :=
 | eone : forall n, zero n -> one (S n).


Inductive zero_expected (n : nat) : Prop :=
 | zero_ex : n = 0 -> zero_expected n 
 with one_expected (n : nat) : Prop :=
 | one_ex : forall m, zero_expected m -> n = S m -> one_expected n.


MetaCoq Run (build_ind zero).
MetaCoq Run (cmp_inds "zero'" "zero_expected").


Inductive even : nat -> Prop :=
 | evenO : even 0 
 | evenS : forall n, odd n -> even (S n)
 with odd : nat -> Prop :=
 | oddS : forall n, even n -> odd (S n).


Inductive even_expected (n : nat) : Prop :=
 | even_O_ex : n = 0 -> even_expected n 
 | evenS_ex : forall m, odd m -> n = S m -> even_expected n
 with odd_expected (n : nat) : Prop :=
 | oddS_ex : forall m, even_expected m -> n = S m -> odd_expected n.


MetaCoq Run (build_ind even).
MetaCoq Run (cmp_inds "even'" "even_expected").
