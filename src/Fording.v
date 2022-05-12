From MetaCoq.Template Require Import Checker utils All.
Export ListNotations MCMonadNotation.
Require Export List String.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICToTemplate TemplateToPCUIC.

Existing Instance config.default_checker_flags.
Existing Instance default_fuel.  
Open Scope string_scope.

Class TslIdent := { tsl_ident : ident -> ident }.

Instance prime_tsl_ident : TslIdent := {| tsl_ident := fun id => id ^ "'" |}.
Definition name : ident -> ident := fun id => substring 0 1 id.
(* Instance prime'_tsl_ident : TslIdent := {| tsl_ident' := fun id => substring 0 1 id |}. *)

Definition make_plugin {X} (f : global_env_ext -> context -> term -> term) (x : X) {Y} : TemplateMonad Y :=
  tmBind (tmQuoteRec x) (fun '(Sigma, q_x) =>
                         let sig' := (TemplateToPCUIC.trans_global (Sigma, Monomorphic_ctx ContextSet.empty)) in 
                           tmUnquoteTyped Y 
                           (PCUICToTemplate.trans (f 
                            sig'
                             []
                            (TemplateToPCUIC.trans sig' q_x)))).

Definition try_infer `{config.checker_flags} `{Fuel} (Σ : global_env_ext) Γ t :=
  match infer' (PCUICToTemplate.trans_global Σ) (PCUICToTemplate.trans_local Γ) (PCUICToTemplate.trans t) with 
  | Checked res => TemplateToPCUIC.trans Σ res 
  | TypeError _ => tApp t (tVar "try_infer error")end.

(* Polymorphic Inductive eq_poly {A : Type} (x : A) : A -> Prop :=
  eq_refl_poly : eq_poly x x. *)

(* Definition tEq ctx:= TemplateToPCUIC.trans ctx <% @eq_poly %>. *)
Definition tEq ctx:= TemplateToPCUIC.trans ctx <% @eq %>.

(* 
returns 
the new type of a constructor,
number of times a var was abstracted,
list equalitytypes declarations
*)

Definition abstract_eqnsbkp (Σ : global_env_ext) (Γ : context) (t : term) : term * context :=
  let fix abstract_eqnsbkp (Γ : context) (ty : term) n :=
      match ty with
      | tProd na A B =>
        let (ty' , ctx) := (abstract_eqnsbkp (Γ ,, vass na A) B 0) in
        ((tProd na A ty'), ctx)
      | tApp L R => (* is there an invariant over L? is it always imm arg? *)
        let type_of_x := try_infer Σ Γ (lift (2 * n) 0 R) in (* every var is lifted by 2 * n *)
        let eqn := mkApps (tEq Σ) [type_of_x; tRel 0; lift (1 + 2 * n) 0 R] in
        (* 
        TODO COLLECT INDICES
        namedx is a new indice, its type should be collected *)
        let namedx := (mkBindAnn (nNamed "x") Relevant) in (* give a better name by inspecting the type *)
        let nanon := (mkBindAnn nAnon Relevant) in 
        let (body, ctx) := (abstract_eqnsbkp (Γ,, vass namedx type_of_x ,, vass nanon eqn) L (S n)) in
        (tProd namedx type_of_x
              (tProd nanon eqn 
                body), ctx)
(*                 t), (S bodyn.2),ctx) *)
      | _ => (ty,Γ)
(*       | B => (mkApps B (map (fun m => tRel (1 + 2 * m)) (seq 0 n)),n,Γ) (* why do we need the app of 1 + 2n? *)  *)
      end
  in let (ty',ctx) := abstract_eqnsbkp Γ t 0 in 
  (ty',ctx).

Definition abstract_eqns (Σ : global_env_ext) (Γ : context) (iter : nat) (t : term) : term * context :=
  let fix abstract_eqns (Γ : context) (ty : term) n :=
      match ty with
      | tProd na A B =>
        let (ty' , ctx) := (abstract_eqns (Γ ,, vass na A) B 0) in
        ((tProd na A ty'), ctx)
      | tApp L R => (* is there an invariant over L? is it always imm arg? *)
        let type_of_x := try_infer Σ Γ ty in (* every var is lifted by 2 * n *)
        let eqn := mkApps (tEq Σ) [type_of_x; tRel (2 * n + 1); ty] in
        (* 
        TODO COLLECT INDICES
        namedx is a new indice, its type should be collected *)
        let namedx := (mkBindAnn (nNamed "x") Relevant) in (* give a better name by inspecting the type *)
        let nanon := (mkBindAnn nAnon Relevant) in 
        ((tProd namedx type_of_x
              (tProd nanon eqn 
                (tRel (2 * n + 1)))), (Γ ,, vass namedx type_of_x ,, vass nanon eqn))
(*                 t), (S bodyn.2),ctx) *)
      | _ => (ty,Γ)
(*       | B => (mkApps B (map (fun m => tRel (1 + 2 * m)) (seq 0 n)),n,Γ) (* why do we need the app of 1 + 2n? *)  *)
      end
  in let (ty',ctx) := abstract_eqns Γ t iter in 
  (ty',ctx).

Definition split_at_n {A : Type} (l : list A) (n : nat) : (list A * list A) :=
  let args := firstn n l in
  let params := skipn n l in
  (params,args).

Definition compute_args (inds : list (term * context)) (Σ : global_env_ext) (Γ : context) (ninds : nat): context * context :=
  let ctxs := flat_map
                (fun ind=> let (_,ctx) := ind : (term * context) in ctx)
                inds in
  let (pars,args) := split_at_n ctxs ninds in
  (pars,args).

Fixpoint range (n : nat) : list nat :=
  match n with
  | O => [O]
  | S n' => n' :: range n'
  end.

Definition gen_term_from_args (args : context) : term :=
  let meq := #|args| in
  let npars := meq / 2 in 
  let fix gen_term_from_args (args : context) :=
  let nap := 
    (npars+meq+1) in
(*     1000 in *)
    match args with
(*     | nil => mkApps (tRel nap) (map (fun n=> tRel (n+meq+1)) (range (npars))) *)
    | nil => mkApps (tRel nap) (map (fun n=> tRel (n+meq)) (rev (seq 0 (npars + 1))))
    | h :: t => let (na,_,ty) := h in
                tProd na ty (gen_term_from_args t)
    end in
  gen_term_from_args args.

Fixpoint build_type (t:term) (args : context) : term := 
  match t with
  | tProd na A B => tProd na A (build_type B args)
  | tApp L R => gen_term_from_args args
  | _ => t
  end.

Definition build_cstr (Σ : global_env_ext) (Γ : context) (iter : nat) (cstr : constructor_body) : constructor_body :=
  let inds := map (abstract_eqns Σ Γ iter) (cstr_indices cstr) in
  let (_,args) := compute_args inds Σ Γ (2 * #|inds|) in
  let type := build_type cstr.(cstr_type) (rev args) in
  {|
    cstr_name:= tsl_ident (cstr_name cstr) ;
    cstr_args := args;
    cstr_indices := []; (* update index *)
    cstr_type := type;
    cstr_arity := #|args|
  |}.

(* Notation "<%% x %%>" := (TemplateToPCUIC.trans [] <% x %>) (only parsing). *)

Definition change_name (name : aname) : aname := 
  let (bind,relev) := name in
  let newName := "n" in
  let newBind :=  (match bind with 
                  | nAnon => nNamed newName
                  | _ => bind end) 
                  in
  {| binder_name := newBind ; binder_relevance := relev|}.
                
Fixpoint replace_anon_names (t : term) : term :=
  match t with 
  | tProd na A B => tProd (change_name na) A (replace_anon_names B)
  | _ => t 
  end. 

Polymorphic Definition build_bodies (Σ : global_env_ext) (Γ : context) (bodies : list one_inductive_body)
 (i0 : nat) : list one_inductive_body :=
        mapi (fun (i : nat) (ind : one_inductive_body) => 
(*           let ctors := map (build_cstr Σ Γ) ind.(ind_ctors) in
                        if Nat.eqb i i0 then
(*                             let n := #|ind_bodies mind| in
                          let typ := try_remove_n_lambdas n ctor in *)
(*                             let rmold := filter (fun ctr => ind_name) *)
(*                             ctors ++ [new_cstr mind newidc typ] *)
                          ctors 
                        else ctors; *)
          {| 
          ind_name := tsl_ident (ind_name ind);
          ind_indices := [];
          ind_type  := replace_anon_names ind.(ind_type) ; 
          ind_ctors :=  mapi (build_cstr Σ Γ ) (ind_ctors ind) ;
          (* just proj below *)
          ind_sort := ind.(ind_sort);
          ind_kelim := ind.(ind_kelim) ;
          ind_projs := ind.(ind_projs);
          ind_relevance := ind.(ind_relevance) |})
          bodies.

Fixpoint give_names_to_anon (inds : context) : context :=
  match inds with
  | nil => nil
  | cons h t => let h' :=  {| decl_name := change_name (decl_name h); 
                              decl_body := h.(decl_body); 
                              decl_type := h.(decl_type) |} 
                in h' :: (give_names_to_anon t)
  end.

Polymorphic Definition build_mind (Σ : global_env_ext) (Γ : context) (mind : mutual_inductive_body) (ind0 : inductive): mutual_inductive_body
  := 
  (* this will not work for mutual inductive defs *)
  let inds :=  (match (head (ind_bodies mind)) with None => [] | Some b =>  ind_indices b end) in
  let inds' := give_names_to_anon inds in
  let params' := app inds' mind.(ind_params) in
  let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars := mind.(ind_npars) + #|inds'|;
        ind_params :=  params' ;
        ind_universes := mind.(ind_universes) ; (* how to infer universes? *) (* infer it later usign mkInductive'*)
        ind_variance := mind.(ind_variance);
        ind_bodies :=  
        build_bodies Σ (app params' Γ) (mind.(ind_bodies)) i0 (* params' *)
      |}.

(* Definition replace_ (decl : Env.mutual_inductive_body) (ind0 : inductive) (old idc : ident) (type : term) :=
  let decl' := TemplateToPCUIC.trans_minductive_body [] decl in
  let ind' := replace_ctor decl' ind0 old idc type in
  let ind'' := PCUICToTemplate.trans_minductive_body ind' in
  ind''. *)

(* Axiom todo : forall A : Type, A. *)

Polymorphic Definition get_ctx {A : Type} (x : A) : TemplateMonad unit :=
     p <-  tmQuoteRec x ;;
     let (genv,tm) :=  (p : Env.program) in
     let Σ := TemplateToPCUIC.trans_global (genv,Monomorphic_ctx ContextSet.empty) : global_env_ext in 
     tmPrint Σ.

Polymorphic Definition build_ind {A : Type} (x : A)
  : TemplateMonad unit
  := 
     p <-  tmQuoteRec x ;;
     let (genv,tm) :=  (p : Env.program) in
     let Σ := TemplateToPCUIC.trans_global (genv,Monomorphic_ctx ContextSet.empty) : global_env_ext in 
     let tm' := TemplateToPCUIC.trans Σ tm in
     match tm' with
     | tInd ind0 _ => tmPrint ind0 ;;
           decl <- tmQuoteInductive (inductive_mind ind0) ;;
           let decl' := (TemplateToPCUIC.trans_minductive_body Σ decl) : mutual_inductive_body in
           tmPrint Σ ;;
           tmMkInductive' (PCUICToTemplate.trans_minductive_body (build_mind Σ [] decl' ind0)) 
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.
  
Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

(* Inductive nonzero (A : Type) : nat -> Prop := C n :  nonzero A (S n). *)
Inductive nonzero (A : Type) : nat -> Prop := C m :  nonzero A (S m). 
Inductive nezet (A : Type) (n : nat) : Prop := 
  C'' m : n = S m -> nezet A n.

Inductive teq (A : Type) (n : nat) : Type :=
    | nileq : n = 0 -> teq A n 
    | conseq : A -> forall m : nat, teq A m 
                    -> forall (e : n = S m), teq A n.
