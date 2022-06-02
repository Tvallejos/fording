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
Definition abstract_eqns (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (npars arity idx_num : nat) (t : term) : term :=
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let abstract_eqns (Γ : context) (ty : term) :=
      match ty with
      | tApp L R => 
        let type_of_x := try_infer Σ Γ (lift idx_num 0 ty) in 
        let eqn := mkApps (tEq gem) [type_of_x; tRel (arity+idx_num) ; tApp L (lift (idx_num) 0 R)] in
        eqn
(*          (Γ ,, vass namedx type_of_x ,, vass nanon eqn, 2) *)
      | _ => 
        let type_of_x := try_infer Σ Γ (lift idx_num 0 ty) in 
        let eqn := mkApps (tEq gem) [type_of_x; tRel idx_num; ty] in
        eqn
      end
  in abstract_eqns Γ t.
  

(* Definition abstract_eqns (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (npars arity idx_num : nat) (t : term) : (context * nat) :=
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let abstract_eqns (Γ : context) (ty : term) :=
      match ty with
      | tApp L R => 
        let type_of_x := try_infer Σ Γ (lift idx_num 0 ty) in 
        let eqn := mkApps (tEq gem) [type_of_x; tRel (arity+idx_num) ; tApp L (lift (idx_num) 0 R)] in
(*         let namedx := (mkBindAnn (nNamed "new_name_abeq") Relevant) in  *)
        (* MAYBE: give a better name by inspecting the type *)
        let nanon := (mkBindAnn nAnon Relevant) in 
         (Γ ,, vass nanon eqn, 1)
(*          (Γ ,, vass namedx type_of_x ,, vass nanon eqn, 2) *)
      | _ => 
        let type_of_x := try_infer Σ Γ (lift idx_num 0 ty) in 
        let nanon := mkBindAnn nAnon Relevant in
        let eqn := mkApps (tEq gem) [type_of_x; tRel idx_num; ty] in
        (Γ,, vass nanon eqn, S idx_num)
      end
  in let (ty',ctx) := abstract_eqns Γ t in 
  (ty',ctx). *)

Definition split_at_n {A : Type} (l : list A) (n : nat) : (list A * list A) :=
  let args := firstn n l in
  let params := skipn n l in
  (params,args).

Definition compute_args (inds : list context) (nnewvars : nat): context * context :=
  (* FIXME ELIM DUP MAYBE CHANGE ABS EQUATIONS *)
  let ctxs := flat_map
                (fun ind=> let ctx := ind : context in ctx)
                inds in
  let (pars,args) := split_at_n ctxs nnewvars in
  (pars,args).

(*   FIXME *)
(* Fixpoint mkTProds (vars : context) (n : nat) (t : term) :=
  match n,vars with
  | O, nil => t
  | S n', v :: vs => let (na,_,ty) := v in tProd na ty (mkTProds vs n' t)
  | _,_ => t (* shouldnt happen *)
  end. *)

Fixpoint mkTProds (vars : context) (t : term) :=
  match vars with
  | nil => t
  | v :: vs => let (na,_,ty) := v in tProd na ty (mkTProds vs t)
  end.


  Definition gen_term_from_args (args : context) (nnewvars nparams : nat) : term := 
(*   let meq := #|args| in *)
  let fix gen_term_from_args (args : context) :=
  let nap := nparams+nnewvars in
    match args with
    | nil => mkApps (tRel (nap+1)) (map (fun n=> tRel n) (rev (seq (nap-nparams+1) nap)))
(*     | nil => mkApps (tRel (nap+1)) (map (fun n=> tRel (n+(nnewvars+1))) (rev (seq (nap-nparams) nap))) *)
    | h :: t => let (na,_,ty) := h in
                tProd na ty (gen_term_from_args t)
    end in
  gen_term_from_args args.

  (* need to handle more cases? *)
Definition build_type (t:term) (args : context) (nnewvars nparams : nat) : term := 
  gen_term_from_args args nnewvars nparams.
(*   match t with
  | tProd na A B => tProd na A (build_type B args nargs nparams)
  | tApp L R => gen_term_from_args args nargs nparams
  | _ => t
  end. *)
About fold_left.
Definition build_cstr (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (nparams iter : nat) (cstr : constructor_body) : constructor_body :=
  let ctx := (app (cstr_args cstr) Γ) in
  let inds := mapi (abstract_eqns Σ ctx nparams (cstr_arity cstr)) (cstr_indices cstr) in
  (* TODO IS ARITY GOOD?*)
  (* IT DEPENDS ON THE TYPE OF THE IDX *)
(*   let (_,args) := compute_args inds (2 * #|inds|) in *)
(*   let nnewvars := list_sum (map (fun i => i.2) inds) in *)
  let nnewvars := #|inds| in
(*   let (params,args) := compute_args (map (fun i => i.1) inds) (nnewvars + nparams)  in *)
(*   let (params,args) := compute_args inds nparams in *)
  let nanon := (mkBindAnn nAnon Relevant) in 
  let args := fold_left (fun g eq=> g ,, vass nanon eq) inds ctx in 
  let type := build_type cstr.(cstr_type) (rev args) #|inds| nparams in 
  let new_arity :=cstr.(cstr_arity) + nnewvars in
(*   (nnewvars + #|(cstr_args cstr)|) nparams in *)
  {|
    cstr_name:= tsl_ident (cstr_name cstr) ;
    (* TODO: when more than 1 index should be ctx + fold app of terms *)
(*     cstr_args := (flat_map (fun i => i.1) inds) ; *)
    cstr_args := firstn new_arity args ;
    cstr_indices := []; 
    cstr_type := type;
    cstr_arity := new_arity
  |}.

(* Notation "<%% x %%>" := (TemplateToPCUIC.trans [] <% x %>) (only parsing). *)

Definition change_name (name : aname) : aname := 
  let (bind,relev) := name in
  let newName := "new_name_change_name" in
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
        (* 'i' should be used when its mind definition *)
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
  (* TODO: case for mindefs *)
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
