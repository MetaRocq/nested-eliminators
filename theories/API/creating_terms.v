From MetaRocq.NestedElim Require Import core.
From MetaRocq.NestedElim Require Import fold_functions.
From MetaRocq.NestedElim Require Import inductive_access.
From MetaRocq.NestedElim Require Import context_access.
From MetaRocq.NestedElim Require Import context_store.

(* Interface to create terms

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
        (key_uparams key_nuparams : list ident)
        (mk_case_pred : list ident -> ident -> state -> term)

- mk_tCase : term -> state -> (nat -> list ident -> list ident -> list ident -> state -> term) -> term

*)



(* 1. Keep and Make Binary Binders *)
Definition kp_binder binder : state -> option ident -> aname -> term -> (state -> key -> term) -> term :=
  fun s x an ty cc =>
  let ty' := weaken s ty in
  let* s' key_bind := add_old_var s x an ty in
  binder an ty' (cc s' key_bind).

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition mk_binder binder : state -> option ident -> aname -> term -> (state -> key -> term) -> term :=
  fun s x an ty cc =>
    let* s key_mk := add_fresh_var s x an ty in
    binder an ty (cc s key_mk).

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.


(* 2. Keep and Make Let in *)
Definition kp_tLetIn : state -> (option ident) -> aname -> term -> term -> (state -> key -> term) -> term :=
  fun s x an db ty cc =>
  let db' := weaken s db in
  let ty' := weaken s ty in
  let* s' key_let := add_old_letin s x an db ty in
  tLetIn an db' ty' (cc s' key_let).

Definition mk_tLetIn : state -> (option ident) -> aname -> term -> term -> (state -> key -> term) -> term :=
  fun s x an db ty cc =>
  let* s key_let := add_fresh_letin s x an db ty in
  tLetIn an db ty (cc s key_let).

(* 3. Inductive Terms *)

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : state -> kername -> nat -> keys -> keys -> keys -> term :=
  fun s kname pos_indb key_uparams key_nuparams key_indices =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_terms s key_uparams
          ++ get_terms s key_nuparams
          ++ get_terms s key_indices  ).

Arguments make_ind _ _ pos_indb key_uparams key_nuparams key_indices.

Definition make_indt : state -> kername -> nat -> keys -> list term -> list term -> term :=
  fun s kname pos_indb key_uparams nuparams indices =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (get_terms s key_uparams ++ nuparams ++ indices).

Arguments make_indt s kname pos_indb key_uparams nuparams indices.


(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : state -> kername -> nat -> nat -> keys -> keys -> term :=
  fun s kname pos_indb pos_ctor key_uparams key_nuparams =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_terms s key_uparams ++ get_terms s key_nuparams).

Arguments make_cst _ pos_indb pos_ctor _ key_uparams key_nuparams.