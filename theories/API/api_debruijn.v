
(* Plan:
--------------------------------
1. core
2. fold_functions
3. debug functions
--------------------------------
4. Access the inductive type
5. Add inductive types to states
--------------------------------
6. Acces the context
7. Add terms to states
--------------------------------
8. interface to create terms
9. interface to decide properties

*)



(* 1. Core  *)
From PluginNestedElim Require Export core.
(*
- state : Type
- init_state : state
- add_pdecl : state_pdecl -> state -> state
- weaken : state -> term -> term
- weaken_decl : state -> context_decl -> context_decl
- weaken_context : state -> context -> context
- state_to_terms : state -> term
*)



(* 2. General Purposed Fold Functions *)
From PluginNestedElim Require Export fold_functions.
(*
- fold_right_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_left_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_right_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B
- fold_left_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B

=> 2 / 3 / 4 variants
*)



(* 3.Functions to help debug *)
From PluginNestedElim Require Export debug_functions.
(*
- show_state : state -> string
- state_to_term : state -> term
*)



(* 4. Access the inductive type *)
From PluginNestedElim Require Export inductive_access.
(*
- get_pdecl : kername -> state -> state_pdecl
- get_uparams     : kername -> state -> context
- get_nb_uparams  : kername -> state -> nat
- get_nuparams    : kername -> state -> context
- get_nb_nuparams : kername -> state -> nat
- get_params      : kername -> state -> context
- get_nb_params   : kername -> state -> nat
- get_mdecl       : kername -> state -> mutual_inductive_body
- get_ind_bodies  : kername -> state -> list one_inductive_body
- get_all_args     : kername -> state -> list context
- get_indb        : kername -> nat  -> state -> one_inductive_body
- get_relevance   : kername -> nat  -> state -> relevance
- get_ctor        : kername -> nat  -> nat  -> state -> constructor_body
- get_indices      : kername -> nat -> state -> context
- get_ctor_indices : kername -> nat -> nat   -> state -> list term
*)



(* 5. Add inductive types to state *)
From PluginNestedElim Require Export inductive_store.
(*
- add_mdecl : kername -> nat -> mutual_inductive_body -> state -> state
*)



(* 6. Acces the context *)
From PluginNestedElim Require Export context_access.
(*
1. Access the context by ident
-----------------------------------------------------------------
- get_term   : ident -> state -> term
- geti_term  : list ident -> nat -> state -> term
- getij_term : list (list ident) -> nat -> nat -> state -> term
- get_terms  : list ident -> state -> list term
-----------------------------------------------------------------
- get_type   : ident -> state -> term
- geti_type  : list ident -> nat -> state -> term
- getij_type : list (list ident) -> nat -> nat -> state -> term
- get_types  : list ident -> state -> list term
-----------------------------------------------------------------
- get_aname   : ident -> state -> aname
- geti_aname  : list ident -> nat -> state -> aname
- getij_aname : list (list ident) -> nat -> nat -> state -> aname
- get_anames  : list ident -> state -> list aname
-----------------------------------------------------------------
- check_pos : ident -> nat -> state -> bool

2. Access the context by the position
-----------------------------------------------------------------
getp_name  : nat -> state -> ident
getp_aname : nat -> state -> aname
getp_body  : nat -> state -> option term
getp_type  : nat -> state -> term
check_id   : nat -> ident -> state -> bool
check_ids  : nat -> list ident -> state -> bool

3. Others
-----------------------------------------------------------------
- get_typing_context : state -> context
- reduce_lets : state -> term -> term
- reduce_except_lets :  global_env -> state -> term -> term
- reduce_full : global_env -> state -> term -> term

*)



(* 7. Add terms to state *)
From PluginNestedElim Require Export context_store.
(*
- notation: "let* x .. z ':=' c1 'in' c2"
- fresh_ident : option ident -> state -> ident
- add_old_var   {X}     : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_old_context {X}   : option ident -> context -> state -> (list ident -> list ident -> list ident -> state -> X) -> X
- add_fresh_var {X}     : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_fresh_context {X} : option ident -> context -> state -> (list ident -> state -> X) -> X
- subst_old_var {X}     : term -> state -> (state -> X) -> X
- subst_old_vars {X}    : list term -> state -> (state -> X) -> X

*)



(* 8. Interface to create terms *)
From PluginNestedElim Require Export creating_terms.
(*

  1. Functions for building inductive types
-----------------------------------------------------------------
- replace_ind {X} : kername -> state -> (state -> X) -> X
- make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term
- make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term

  2. Keep and Make Let in
-----------------------------------------------------------------
- kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term
- mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term

  3. Keep and Make Binary binder(s)
--------------------------------------------------------------------------------
Context (binder : aname -> term -> term -> term)

- kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_kp_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_uparams : kername -> state -> (list ident -> state -> term) -> term
- closure_nuparams : kername -> state -> (list ident -> state -> term) -> term
- closure_params : kername -> state -> (list ident -> state -> term) -> term

- mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_mk_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term
- closure_binder {A} : option ident -> list A -> (naming : nat -> A -> aname) ->
    (typing : nat -> A -> state -> term) -> state -> (list ident -> state -> term) -> term

- kp_tProd / kp_tLambda / mk_tProd / mk_tLambda

  4. Make Fixpoint
--------------------------------------------------------------------------------
Context (kname : kername)
        (fty   : nat -> term)
        (frarg : nat -> nat)

- mk_tFix : nat -> state -> (list ident -> nat -> state -> term) -> term

End

- tFix_default_rarg : kername -> state -> nat -> nat

  5. Make Match
-----------------------------------------------------------------
Context (kname : kername) (pos_indb : nat) (indb : one_inductive_body)
        (id_uparams id_nuparams : list ident)
        (mk_case_pred : list ident -> ident -> nat -> one_inductive_body -> state -> term).

- mk_tCase : term -> state -> (nat -> constructor_body -> list ident -> list ident -> list ident -> state -> branch term) -> term

*)



(* Read Interface for Inductives *)
From PluginNestedElim Require Export read_mode_ind.


(* 9. Interface to decide properties *)
From PluginNestedElim Require Export decide.
(*
Context {A : Type} (bop : A -> A -> A) (default : A)
        (E : global_env) (kname : kername)

- check_args_by_arg : (term -> state -> A) -> context -> state -> A
- check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A
- debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A)

*)

(* 10 Views to match on arguments *)
From PluginNestedElim Require Export view_args.


(*
#############################
###         Others        ###
#############################

*)

Record output_univ : Type := mk_output_univ
  { out_univ  : term;
    out_relev : relevance
  }.

Definition relev_sort (U : term) : relevance :=
  match U with
  | tSort sSProp => Irrelevant
  | _ => Relevant
  end.

Definition make_name : ident -> nat -> ident :=
  fun s n => s ^ (string_of_nat n).

Definition make_name0 : ident -> nat -> ident :=
  fun s n => match n with
  | 0 => s
  | S n => make_name s n
  end.

Definition make_name_bin : ident -> nat -> nat -> ident :=
  fun s n m => s ^ (string_of_nat n) ^ (string_of_nat m).

Definition name_map : (string -> string) -> name -> name :=
  fun f name => match name with
  | nNamed s => nNamed (f s)
  | nAnon => nAnon
  end.

MetaRocq Quote Definition qTrue := True.

Definition funTrue : term -> term :=
  fun ty => tLambda (mkBindAnn nAnon Relevant) ty qTrue.

MetaRocq Quote Definition qI := I.

Definition funI : term -> term :=
  fun ty => tLambda (mkBindAnn nAnon Relevant) ty qI.

Definition fold_binder binder (cxt : context) (tm : term) :=
fold_left (fun c ' (mkdecl an z ty) =>
  match z with
  | Some db => tLetIn an db ty c
  | None    => binder an ty c
  end
)
cxt tm.