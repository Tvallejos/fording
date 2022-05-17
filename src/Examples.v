From MetaCoq.Fording Require Import Fording.
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import utils All. 

Inductive nonzero (A : Type) : nat -> Prop := C m :  nonzero A (S m). 
Inductive nzexpected (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nzexpected A n.

MetaCoq Run (build_ind nonzero).


Definition get_ind (q : qualid) : TemplateMonad mutual_inductive_body := 
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind))
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

(* Definition eqb_inds_renaming (ind ind' : mutual_inductive_body) : bool :=
  let (f,np,par,bd,u,var) := ind in
  let (f',np',par',bd,u',var') := ind in
  eqb f f' && eqb np np' &&
  eqb par par' && eqb bd bd &&
  eqb u u' && eqb var var'.

Definition cmp_inds (q q': qualid) : TemplateMonad bool :=
  ind <- get_ind q ;; 
  ind' <- get_ind q' ;;
  tmReturn (eqb_inds_renaming ind ind').
   *)


(* Ltac Print_example input actual expected :=
  idtac "==========================================";
  idtac "================= Input ==================";
  idtac "==========================================";
  idtac input. *)
  
  Goal True.
  idtac "==========================================";
  idtac "================= Input ==================";
  idtac "==========================================".
 Print nonzero.
  idtac "==========================================";
  idtac "============= Actual result ==============";
  idtac "==========================================".
Print nonzero'.
  idtac "==========================================";
  idtac "============= Expected result ==============";
  idtac "==========================================".
Print nzexpected.
Abort.

(* Notation "f,n" := f. Print nn. f. *)

(* Definition f (a b c : Type):=
  let (show) := a in
  let (show) := b in
  let (show) := c in
  show. *)
(* Print_example nonzero. *)
