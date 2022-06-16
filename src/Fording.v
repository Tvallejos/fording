From MetaCoq.Template Require Import Checker utils All. 
Export ListNotations MCMonadNotation.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICToTemplate TemplateToPCUIC.

Open Scope string_scope.
Class TslIdent := { tsl_ident : ident -> ident }. 
Instance prime_tsl_ident : TslIdent := {| tsl_ident := fun id => id ^ "'" |}. 
Definition tEq ctx:= TemplateToPCUIC.trans ctx <% @eq %>.


(*
  Returns the type of the nth identifier in the context
*)
Fixpoint lookup_ctx_type (n : nat) (Γ : context) : term :=
  match n, Γ with
  | O, h :: t => let (_,_,ty) := h in ty
  | S n', h :: t => lookup_ctx_type n' t
  | _,_ => (tVar "lookup_ctx_type_error")
  end.


(* 
  Introduces an equality between the nth new parameter and the index (t)
*)
Definition abstract_eqns (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (idx_num arity nnewvars : nat) (t : term) : term :=
  let gem := PCUICProgram.global_env_ext_map_global_env_map Σ in
  let type_of_x := lookup_ctx_type (arity+nnewvars-1-idx_num) Γ in
  let eqn := mkApps (tEq gem) [type_of_x; tRel (arity+nnewvars-1); lift idx_num 0 t ] in
  eqn.


(*
  It builds the type of a constructor given the parameters
*)
Definition build_type (args : context) (nparams nbodies body_num : nat) : term := 
  let nap := #|args| in
  let fix build_type (args : context) :=
    match args with
    | nil => mkApps (tRel (nap+(nbodies-body_num-1))) (map (fun n=> tRel n) (rev (seq (nap-nparams) nparams)))
    | h :: t => let (na,_,ty) := h in
                tProd na ty (build_type t)
    end in
  build_type args.

(*
  Lifts a context declaration by the specification of lifting a term
*)
Definition lift_decl (n k : nat) (decl : context_decl ) : context_decl :=
  let (na, bdy, ty) := decl in 
  {| decl_name := na; decl_body := bdy; decl_type := (lift n k ty)|}.

  
(*
  Lifts a context by the specification of lifting a term
*)
Fixpoint lift_ctx (n k : nat) (ctx: list context_decl) : list context_decl :=
  match ctx with
  | nil => nil
  | d :: ds => lift_decl n k d :: lift_ctx n (k+1) ds
  end.


(*
  Builds a new constructor based on a previous one by moving indexes to parameters
*)
Definition build_cstr (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (nparams nbodies body_num iter : nat) (cstr : constructor_body) : constructor_body :=
  let cstr_inds := (cstr_indices cstr) in (* list of indexes *)
  let nnewvars := #|cstr_inds| in (* add this amount of identifiers *)
  let ctx := (app (rev (lift_ctx nnewvars 0 (rev (cstr_args cstr)))) Γ) in 
  (* build the current context using the parameters and previous args, 
     lift the context taking into account the equalities that are going to be added *)
  let inds := mapi (fun i ind => abstract_eqns Σ ctx i (cstr_arity cstr) nnewvars ind) cstr_inds in 
  (* compute the equalities of every index *)
  let new_ctx := fold_left (fun g eq=> g ,, vass (mkBindAnn nAnon Relevant) eq) inds ctx in 
  (* add the equalities to the context *)
  let type := build_type (rev new_ctx) nparams nbodies body_num in 
  (* build the new type of the constructor *)
  let new_arity :=cstr.(cstr_arity) + nnewvars in
  (* compute the new arity *)
  {|
    cstr_name:= tsl_ident (cstr_name cstr) ;
    cstr_args := firstn new_arity new_ctx;
    cstr_indices := []; 
    cstr_type := type;
    cstr_arity := new_arity
  |}.


(*
  Gives a name to the new parameters
*)
Definition change_name (name : aname) : aname := 
  let (bind,relev) := name in
  let newName := "new_name_change_name" in
  let newBind :=  (match bind with 
                  | nAnon => nNamed newName
                  | _ => bind end) 
                  in
  {| binder_name := newBind ; binder_relevance := relev|}.
                

(*
  Gives a name to every index in the term
*)
Fixpoint replace_anon_names (t : term) : term :=
  match t with 
  | tProd na A B => tProd (change_name na) A (replace_anon_names B)
  | _ => t 
  end. 


(*
  Builds a new body based on a previous one by generalizing every constructor 
*)
Definition build_bodies (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (bodies : list one_inductive_body)
 (i0 : nat) (nparams : nat) : list one_inductive_body :=
 let nbodies := #|bodies| in
        mapi (fun (body_num : nat) (ind : one_inductive_body) => 
          {| 
          ind_name := tsl_ident (ind_name ind);
          ind_indices := [];
          ind_type  := replace_anon_names ind.(ind_type) ; 
          (* give name to indexes *)
          ind_ctors :=  mapi (build_cstr Σ Γ nparams nbodies body_num) (ind_ctors ind) ;
          (* build every constructor by inserting equations before every index *)
          (* just proj below *)
          ind_sort := ind.(ind_sort);
          ind_kelim := ind.(ind_kelim) ;
          ind_projs := ind.(ind_projs);
          ind_relevance := ind.(ind_relevance) |})
          bodies.


(*
  Gives a name to every index in the context, namely indexes
*)
Fixpoint give_names_to_anon (inds : context) : context :=
  match inds with
  | nil => nil
  | cons h t => let h' :=  {| decl_name := change_name (decl_name h); 
                              decl_body := h.(decl_body); 
                              decl_type := h.(decl_type) |} 
                in h' :: (give_names_to_anon t)
  end.


(*
  Builds a new mutually inductive definition based on a previous one 
  by fording each body 
*)
Definition build_mind (Σ : PCUICProgram.global_env_ext_map) (Γ : context) (mind : mutual_inductive_body) (ind0 : inductive): mutual_inductive_body
  := 
  let inds :=  (match (head (ind_bodies mind)) with None => [] | Some b =>  ind_indices b end) in
  (* here we assume that every inductive body has the same indexes *)
  let inds' := give_names_to_anon inds in
  (* gives a name to indexes *)
  let params' := app inds' mind.(ind_params) in
  (* parameters now include the indexes (now with name) *)
  let nparams := mind.(ind_npars) + #|inds'| in
  let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars :=  nparams;
        ind_params :=  params' ;
        ind_universes := mind.(ind_universes) ; 
        ind_variance := mind.(ind_variance);
        ind_bodies :=  
        build_bodies Σ (app params' Γ) (mind.(ind_bodies)) i0 nparams 
      |}.


(*
  Builds a forded inductive definition by quoting the input
*)
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
