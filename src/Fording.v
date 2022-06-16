From MetaCoq.Template Require Import Checker utils All. 
Export ListNotations MCMonadNotation.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICToTemplate TemplateToPCUIC.

Open Scope string_scope.
Class TslIdent := { tsl_ident : ident -> ident }. 
Instance prime_tsl_ident : TslIdent := {| tsl_ident := fun id => id ^ "'" |}. 
Definition tEq ctx:= TemplateToPCUIC.trans ctx <% @eq %>.


Fixpoint lookup_ctx_type (n : nat) (Γ : context) :=
  match n, Γ with
  | O, h :: t => let (_,_,ty) := h in ty
  | S n', h :: t => lookup_ctx_type n' t
  | _,_ => (tVar "lookup_ctx_type_error")
  end.


(* 
returns 
the type of an index eqn abstraction,
new context (with the new equalities)
*)
Definition abstract_eqns (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (idx_num arity nnewvars : nat) (t : term) : term :=
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let type_of_x := lookup_ctx_type (arity+nnewvars-1-idx_num) Γ in
  let eqn := mkApps (tEq gem) [type_of_x; tRel (arity+nnewvars-1); lift idx_num 0 t ] in
  eqn.


Definition split_at_n {A : Type} (l : list A) (n : nat) : (list A * list A) :=
  let args := firstn n l in
  let params := skipn n l in
  (params,args).


Fixpoint mkTProds (vars : context) (t : term) :=
  match vars with
  | nil => t
  | v :: vs => let (na,_,ty) := v in tProd na ty (mkTProds vs t)
  end.


Definition build_type (args : context) (nnewvars nparams nbodies body_num : nat) : term := 
  let nap := #|args| in
  let fix build_type (args : context) :=
    match args with
    | nil => mkApps (tRel (nap+(nbodies-body_num-1))) (map (fun n=> tRel n) (rev (seq (nap-nparams) nparams)))
    | h :: t => let (na,_,ty) := h in
                tProd na ty (build_type t)
    end in
  build_type args.


Definition lift_decl (n from : nat) (decl : context_decl ) : context_decl :=
  let (na, bdy, ty) := decl in 
  {| decl_name := na; decl_body := bdy; decl_type := (lift n from ty)|}.

  
Fixpoint lift_ctx (n from : nat) (ctx: list context_decl) : list context_decl :=
  match ctx with
  | nil => nil
  | d :: ds => lift_decl n from d :: lift_ctx n (from+1) ds
  end.


Definition build_cstr (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (nparams nbodies body_num iter : nat) (cstr : constructor_body) : constructor_body :=
  let cstr_inds := (cstr_indices cstr) in
  let nnewvars := #|cstr_inds| in
  let ctx := (app (rev (lift_ctx nnewvars 0 (rev (cstr_args cstr)))) Γ) in
  let inds := mapi (fun i ind => abstract_eqns Σ ctx i (cstr_arity cstr) nnewvars ind) cstr_inds in
  let nanon := (mkBindAnn nAnon Relevant) in 
  let new_ctx := fold_left (fun g eq=> g ,, vass nanon eq) inds ctx in 
  let type := build_type (rev new_ctx) nnewvars nparams nbodies body_num in 
  let new_arity :=cstr.(cstr_arity) + nnewvars in
  {|
    cstr_name:= tsl_ident (cstr_name cstr) ;
    cstr_args := firstn new_arity new_ctx;
    cstr_indices := []; 
    cstr_type := type;
    cstr_arity := new_arity
  |}.


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


Definition build_bodies (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (bodies : list one_inductive_body)
 (i0 : nat) (nparams : nat) : list one_inductive_body :=
 let nbodies := #|bodies| in
        mapi (fun (body_num : nat) (ind : one_inductive_body) => 
          {| 
          ind_name := tsl_ident (ind_name ind);
          ind_indices := [];
          ind_type  := replace_anon_names ind.(ind_type) ; 
          ind_ctors :=  mapi (build_cstr Σ Γ nparams nbodies body_num) (ind_ctors ind) ;
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


Definition build_mind (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (mind : mutual_inductive_body) (ind0 : inductive): mutual_inductive_body
  := 
  let inds :=  (match (head (ind_bodies mind)) with None => [] | Some b =>  ind_indices b end) in
  let inds' := give_names_to_anon inds in
  let params' := app inds' mind.(ind_params) in
  let nparams := mind.(ind_npars) + #|inds'| in
  (* here we assume that every inductive body has the same indexes *)
  let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars :=  nparams;
        ind_params :=  params' ;
        ind_universes := mind.(ind_universes) ; 
        ind_variance := mind.(ind_variance);
        ind_bodies :=  
        build_bodies Σ (app params' Γ) (mind.(ind_bodies)) i0 nparams 
      |}.


Definition build_ind {A : Type} (x : A)
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
           declred <- tmEval cbv decl' ;;
          let mind := build_mind Σ [] decl' ind0 in
          let tmind := (PCUICToTemplate.trans_minductive_body mind) in
           tmMkInductive' tmind
      | _ => tmPrint tm ;; tmFail " is not an inductive" 
     end.
  

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.
