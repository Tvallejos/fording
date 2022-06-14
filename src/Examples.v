From MetaCoq.Fording Require Import Fording Testing.
From MetaCoq.Template Require Import utils. 

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

MetaCoq Run (printInductive "zLexpected").
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
                    
MetaCoq Run (printInductive "cons_ex").
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

Inductive even : nat -> Prop :=
 | evenO : even 0 
 | evenS : forall n, odd n -> even (S n)
 with odd : nat -> Prop :=
 | oddS : forall n, even n -> odd (S n).

 Inductive even2 : nat -> Prop :=
| even_O : even2 0
| even_S : forall n, odd n -> even2 (S n)
with odd2 : nat -> Prop :=
| odd_S : forall n, even n -> odd2 (S n).

Inductive even_expected (n : nat) : Prop :=
 | even_O_ex : n = 0 -> even_expected n 
 | evenS_ex : forall m, odd m -> n = S m -> even_expected n
 with odd_expected (n : nat) : Prop :=
 | oddS_ex : forall m, even_expected m -> n = S m -> odd_expected n.

(* Inductive tmp_fst (n : nat) (b : bool) : Prop :=
 | tmpO : n = 0 -> b = true -> tmp n B
 | tmpS : forall m : nat,
            forall b : bool, tmp_snd m b -> n = S m ->
            b = true -> tmp_fst n b
            with
  tmp_snd :  *)



MetaCoq Run (printInductive "even_expected").
MetaCoq Run (build_ind even).
(* Inductive even3 : nat -> Prop :=
  | zero_is_even : even3 O
  | S_of_odd_is_even : (forall n:nat, odd n -> even3 (S n))
with odd3 : nat -> Prop :=
  | S_of_even_is_odd : (forall n:nat, even n -> odd3 (S n)). *)

(*  Inductive tree(A:Set) : Set :=
  | node : A -> forest A -> tree A
with forest (A: Set) : Set :=
  | nochild : forest A 
  | addchild : tree A -> forest A -> forest A.

Inductive tree2 : Set :=
| node2 : forest2 -> tree2
with forest2 : Set :=
| emptyf : forest2
| consf : tree2 -> forest2 -> forest2. *)

(*   Inductive value (nvalue : nat) : Type :=
  | var_value : fin (nvalue) -> value (nvalue)
  | u : value (nvalue)
  | pair : value (nvalue) -> value (nvalue) -> value (nvalue)
  | inj : bool -> value (nvalue) -> value (nvalue)
  | thunk : comp (nvalue) -> value (nvalue)
 with comp (nvalue : nat) : Type :=
  | cu : comp (nvalue)
  | force : value (nvalue) -> comp (nvalue)
  | lambda : comp (S nvalue) -> comp (nvalue)
  | app : comp (nvalue) -> value (nvalue) -> comp (nvalue)
  | tuple : comp (nvalue) -> comp (nvalue) -> comp (nvalue)
  | ret : value (nvalue) -> comp (nvalue)
  | letin : comp (nvalue) -> comp (S nvalue) -> comp (nvalue)
  | proj : bool -> comp (nvalue) -> comp (nvalue)
  | caseZ : value (nvalue) -> comp (nvalue)
  | caseS : value (nvalue) -> comp (S nvalue) -> comp (S nvalue) -> comp (nvalue)
  | caseP : value (nvalue) -> comp (S (S nvalue)) -> comp (nvalue). *)