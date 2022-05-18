
From MetaCoq.Fording Require Import Fording.
From MetaCoq.Template Require Import utils All. 
From MetaCoq.SafeChecker Require Import PCUICEqualityDec.

Definition get_ind (q : qualid) : TemplateMonad mutual_inductive_body := 
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind))
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition eq_ (A :Type) (t t':A) : bool :=
  true.

Definition gen : (Universe.t -> Universe.t -> bool) ->  
  global_reference ->
  nat -> list Level.t -> list Level.t -> bool :=
  fun _ _ _ _ _ => true.

Definition eqb_term (t t': PCUICAst.term) : bool :=
  eqb_term_upto_univ_napp (eq_ Universe.t) (eq_ Universe.t) gen 0 t t'.

Definition eqb_name (n m : aname) : bool :=
  let (na,rel) := n in 
  let (ma,rel') := m in
  let eqname := match na, ma with
                | nAnon,nAnon => true
                | nNamed n',nNamed m' => true 
                | _, _ => false end in
  eqname && eqb rel rel'.

Definition eqb_opt_term (ot ot': option PCUICAst.term) : bool :=
  match ot,ot' with
  | None,None => true
  | Some t,Some t' => eqb_term t t'
  | _,_ => false end.

Definition eqb_context_decl_upto_names (x y: PCUICAst.PCUICEnvironment.context_decl) :=
  let (na,bd,ty) := x in 
  let (na',bd',ty') := y in
  eqb_name na na' &&
  eqb_opt_term bd bd' &&
  eqb_term ty ty'. 

  
Definition eqb_kelim (kelim kelim': allowed_eliminations) : bool := 
  eqb kelim kelim'.

Definition eqb_ctor (ctor ctor' : PCUICAst.PCUICEnvironment.constructor_body) : bool :=
  let (_,args,indices,type,arity) := ctor in
  let (_,args',indices',type',arity') := ctor in
  forallb2 eqb_context_decl_upto_names args args' &&
  forallb2 eqb_term indices indices' &&
  eqb_term type type &&
  eqb arity arity.

Definition eqb_proj (proj proj': PCUICAst.PCUICEnvironment.projection_body) : bool := 
  eqb proj proj'.

Definition eqb_relevance (relevance relevance': relevance) : bool := true.

Definition eqb_body (body body': PCUICAst.PCUICEnvironment.one_inductive_body) : bool :=
  let (_,indices,sort,type,kelim,ctors,projs,relevance) := body in 
  let (_,indices',sort',type',kelim',ctors',projs',relevance') := body' in 
  forallb2 eqb_context_decl_upto_names indices indices' &&
  eq_ Universe.t sort sort' &&
  eqb_term type type'                &&
  eqb_kelim kelim kelim'             &&
  forallb2 eqb_ctor ctors ctors'     &&
  forallb2 eqb_proj projs projs'       &&
  eqb_relevance relevance relevance'. 

Definition eqb_universes (u v : universes_decl) : bool :=
  true.

Definition eqb_variance (u v : option (list Variance.t)) : bool :=
  true.

Definition eqb_ind (ind ind': mutual_inductive_body) (Σ : PCUICProgram.global_env_map) : bool :=
  let mind := TemplateToPCUIC.trans_minductive_body Σ ind in
  let mind' := TemplateToPCUIC.trans_minductive_body Σ ind' in
  let (f,npars,params,bodies,universes,variance) := mind in 
  let (f',npars',params',bodies',universes',variance') := mind' in 
  eqb f f' &&
  eqb npars npars' &&
  forallb2 eqb_context_decl_upto_names params params' &&
  forallb2 eqb_body bodies bodies' &&
  eqb_universes universes universes' &&
  eqb_variance variance variance'.

Definition gem_of_genv (genv : global_env) : PCUICProgram.global_env_map :=
  TemplateToPCUIC.trans_global_env genv.

Definition string_of_bool (b : bool) : string :=
  match b with
  | false => "false"
  | true => "true"
  end.

Definition cmp_inds (q q': qualid) : TemplateMonad bool :=
  p <-  tmQuoteRec q ;;
  let (gev,_) := p : program in
  let Σ := gem_of_genv(gev) in
  ind <- get_ind q ;; 
  ind' <- get_ind q' ;;
  cmp <- tmEval cbv (eqb_ind ind ind' Σ) ;;
  tmMsg (q ^ " == " ^ q' ^ " = " ^ string_of_bool cmp) ;;
(*   tmReturn cmp. *)
  if cmp then
    tmReturn cmp
    else tmFail (q ^ "!=" ^ q').