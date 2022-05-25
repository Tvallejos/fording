(* From MetaCoq.Template Require Import Checker utils All. *)
From MetaCoq.Template Require Import Checker utils All. 
Export ListNotations MCMonadNotation.
(* Require Export List String. *)
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICToTemplate TemplateToPCUIC.

Existing Instance config.default_checker_flags.
Existing Instance default_fuel.  
Open Scope string_scope.

Class TslIdent := { tsl_ident : ident -> ident }.

Instance prime_tsl_ident : TslIdent := {| tsl_ident := fun id => id ^ "'" |}.
(* Definition name : ident -> ident := fun id => substring 0 1 id. *)
(* Instance prime'_tsl_ident : TslIdent := {| tsl_ident' := fun id => substring 0 1 id |}. *)

Definition make_plugin {X} (f : PCUICProgram.global_env_map -> context -> term -> term) (x : X) {Y} : TemplateMonad Y :=
  tmBind (tmQuoteRec x) (fun '(Sigma, q_x) =>
                         let sig' := (TemplateToPCUIC.trans_global_env Sigma) in 
                           tmUnquoteTyped Y 
                           (PCUICToTemplate.trans (f 
                                                  sig'
                                                  []
                                                  (TemplateToPCUIC.trans sig' q_x)))).

Definition try_infer `{config.checker_flags} `{Fuel} (Σ : PCUICProgram.global_env_ext_map) Γ t :=
  let gee := PCUICProgram.global_env_ext_map_global_env_ext Σ in
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let err := "try_infer_error" : string in
  match infer' (PCUICToTemplate.trans_global gee) (PCUICToTemplate.trans_local Γ) (PCUICToTemplate.trans t) with 
  | Checked res => TemplateToPCUIC.trans gem res
  | TypeError _ => tApp t (tVar err)
  end.

(* Polymorphic Inductive eq_poly {A : Type} (x : A) : A -> Prop :=
  eq_refl_poly : eq_poly x x. *)

(* Definition tEq ctx:= TemplateToPCUIC.trans ctx <% @eq_poly %>. *)
Definition tEq ctx:= TemplateToPCUIC.trans ctx <% @eq %>.

(* 
returns 
the type of an index eqn abstraction,
new context (with the new equalities)
*)
Definition abstract_eqns (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (iter : nat) (t : term) : (term * context * nat) :=
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let fix abstract_eqns (Γ : context) (ty : term) n :=
      match ty with
      | tProd na A B =>
        let (tyc , n) := (abstract_eqns (Γ ,, vass na A) B 0) : (term * context) * nat in
        ((tProd na A tyc.1 ), tyc.2 , n)
      | tApp L R => 
        let type_of_x := try_infer Σ Γ ty in 
        let eqn := mkApps (tEq gem) [type_of_x; tRel (n + 1); ty] in
        let namedx := (mkBindAnn (nNamed "x") Relevant) in (* MAYBE: give a better name by inspecting the type *)
        let nanon := (mkBindAnn nAnon Relevant) in 
        ((tProd namedx type_of_x
              (tProd nanon eqn 
                (tRel (n + 1)))), (Γ ,, vass namedx type_of_x ,, vass nanon eqn),S (S n))
      | _ => 
        let type_of_x := try_infer Σ Γ ty in 
        let nanon := mkBindAnn nAnon Relevant in
        let eqn := mkApps (tEq gem) [type_of_x; tRel n; ty] in
        ((tProd nanon type_of_x ty),Γ,, vass nanon eqn, S n)
      end
  in let (ty',ctx) := abstract_eqns Γ t iter in 
  (ty',ctx).

(* Definition abstract_eqns (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (iter : nat) (t : term) : term * context :=
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let fix abstract_eqns (Γ : context) (ty : term) n :=
      match ty with
      | tProd na A B =>
        let (ty' , ctx) := (abstract_eqns (Γ ,, vass na A) B 0) in
        ((tProd na A ty'), ctx)
      | tApp L R => 
        let type_of_x := try_infer Σ Γ ty in 
        let eqn := mkApps (tEq gem) [type_of_x; tRel (2 * n + 1); ty] in
        let namedx := (mkBindAnn (nNamed "x") Relevant) in (* MAYBE: give a better name by inspecting the type *)
        let nanon := (mkBindAnn nAnon Relevant) in 
        ((tProd namedx type_of_x
              (tProd nanon eqn 
                (tRel (2 * n + 1)))), (Γ ,, vass namedx type_of_x ,, vass nanon eqn))
      | _ => 
        let type_of_x := try_infer Σ Γ ty in 
        let eqn := mkApps (tEq gem) [type_of_x; tRel (2 * n); ty] in
        ((tProd (mkBindAnn nAnon Relevant) type_of_x ty),Γ)
      end
  in let (ty',ctx) := abstract_eqns Γ t iter in 
  (ty',ctx). *)

Definition split_at_n {A : Type} (l : list A) (n : nat) : (list A * list A) :=
  let args := firstn n l in
  let params := skipn n l in
  (params,args).

Definition compute_args (inds : list (term * context)) (nnewvars : nat): context * context :=
  (* FIXME ELIM DUP MAYBE CHANGE ABS EQUATIONS *)
  let ctxs := flat_map
                (fun ind=> let (_,ctx) := ind : (term * context) in ctx)
                inds in
  let (pars,args) := split_at_n ctxs nnewvars in
  (pars,args).

(*   FIXME *)
Fixpoint mkTProds (vars : context) (n : nat) (t : term) :=
  match n,vars with
  | O, nil => t
  | S n', v :: vs => let (na,_,ty) := v in tProd na ty (mkTProds vs n' t)
  | _,_ => t (* shouldnt happen *)
  end.

  Definition gen_term_from_args (params args : context) (nnewvars nparams : nat): term := 
(*   let meq := #|args| in *)
  let fix gen_term_from_args (args : context) :=
  let nap := 
    (nparams+nnewvars) in
    match args with
    | nil => mkApps (tRel nap) (map (fun n=> tRel (n+nnewvars)) (rev (seq 0 nparams)))
    | h :: t => let (na,_,ty) := h in
                tProd na ty (gen_term_from_args t)
    end in
  mkTProds params nparams (gen_term_from_args args).

  (* need to handle more cases? *)
Definition build_type (t:term) (params args : context) (nargs nparams: nat): term := 
  gen_term_from_args params args nargs nparams.
(*   match t with
  | tProd na A B => tProd na A (build_type B args nargs nparams)
  | tApp L R => gen_term_from_args args nargs nparams
  | _ => t
  end. *)

Definition build_cstr (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (nparams iter : nat) (cstr : constructor_body) : constructor_body :=
  let inds := map (abstract_eqns Σ Γ iter) (cstr_indices cstr) in
  (* IT DEPENDS ON THE TYPE OF THE IDX *)
(*   let (_,args) := compute_args inds (2 * #|inds|) in *)
  let nnewvars := list_sum (map (fun i => i.2) inds) in
  let (params,args) := compute_args (map (fun i => i.1) inds) (nnewvars + nparams)  in
  let type := build_type cstr.(cstr_type) (rev params) (rev args) nnewvars nparams in
  {|
    cstr_name:= tsl_ident (cstr_name cstr) ;
    cstr_args := (firstn nnewvars args) ; 
    cstr_indices := []; 
    cstr_type := type;
    cstr_arity := nnewvars
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

Polymorphic Definition build_bodies (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (bodies : list one_inductive_body)
 (i0 : nat) (nparams : nat) : list one_inductive_body :=
        mapi (fun (i : nat) (ind : one_inductive_body) => 
        (* I should be used when its mind definition *)
          {| 
          ind_name := tsl_ident (ind_name ind);
          ind_indices := [];
          ind_type  := replace_anon_names ind.(ind_type) ; 
          ind_ctors :=  mapi (build_cstr Σ Γ nparams) (ind_ctors ind) ;
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

Polymorphic Definition build_mind (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (mind : mutual_inductive_body) (ind0 : inductive): mutual_inductive_body
  := 
  (* FIXME: case for mindefs *)
  let inds :=  (match (head (ind_bodies mind)) with None => [] | Some b =>  ind_indices b end) in
  let inds' := give_names_to_anon inds in
  let params' := app inds' mind.(ind_params) in
  let nparams := mind.(ind_npars) + #|inds'| in
  let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars :=  nparams;
        ind_params :=  params' ;
        ind_universes := mind.(ind_universes) ; (* how to infer universes? *) (* infer it later usign mkInductive'*)
        ind_variance := mind.(ind_variance);
        ind_bodies :=  
        build_bodies Σ (app params' Γ) (mind.(ind_bodies)) i0 nparams (* params' *)
      |}.

(* Axiom todo : forall A : Type, A. *)

(* function for debugging purpuses *)
Polymorphic Definition get_ctx {A : Type} (x : A) : TemplateMonad unit :=
     p <-  tmQuoteRec x ;;
     let (genv,tm) :=  (p : Env.program) in
     let genv' := TemplateToPCUIC.trans_global_env genv : PCUICProgram.global_env_map in
     let genv'' := PCUICProgram.trans_env_env genv' in
     let gem := PCUICProgram.build_global_env_map genv'' in 
     let gem' := PCUICProgram.global_env_ext_map_global_env_map (genv',Monomorphic_ctx) in
(*      let Σ := (TemplateToPCUIC.trans_global gem') in  *)
     tmPrint gem'.

Polymorphic Definition build_ind {A : Type} (x : A)
  : TemplateMonad unit
  := 
     p <-  tmQuoteRec x ;;
     let (genv,tm) :=  (p : Env.program) in
     let Σ := TemplateToPCUIC.trans_global (genv,Monomorphic_ctx) : PCUICProgram.global_env_ext_map in 
     let sig := PCUICProgram.global_env_ext_map_global_env_map Σ in
     let tm' := TemplateToPCUIC.trans sig tm in
     match tm' with
     | tInd ind0 _ => 
           decl <- tmQuoteInductive (inductive_mind ind0) ;;
           let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in 
           let decl' := (TemplateToPCUIC.trans_minductive_body gem decl) : mutual_inductive_body in
(*            tmPrint Σ ;; *)
(*            tmPrint decl' ;; *)
           declred <- tmEval cbv decl' ;;
           tmPrint declred ;;
          let mind := build_mind Σ [] decl' ind0 in
           tmMsg "==================== ind0" ;;
           tmPrint ind0 ;;
(*            tmMsg "==================== tmind" ;; *)
          let tmind := (PCUICToTemplate.trans_minductive_body mind) in
           mind <- tmEval cbv mind ;; 
(*            tmPrint tmind ;;
           tmMsg "==================== " ;;*)
           tmMsg "==================== mind" ;;
           tmPrint mind ;; 
(*            tmMkInductive' (PCUICToTemplate.trans_minductive_body mind)  *)
           tmMkInductive' tmind
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.
  
Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.
