From MetaRocq.NestedElim Require Import core.
From MetaRocq.NestedElim Require Import context_store.

(* Get and check functions for the context

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
- newc : state -> context
- reduce_lets : state -> term -> term
- reduce_except_lets :  global_env -> state -> term -> term
- reduce_full : global_env -> state -> term -> term

*)


(* 1.0 Local functions geting term and type with shifted *)
Definition lift_cdecl : nat -> context_decl -> context_decl :=
  fun n ' (mkdecl an x ty) => mkdecl an (option_map (lift0 n) x) (lift0 n ty).

#[local] Definition ERROR_CDECL : context_decl :=
  mkdecl (mkBindAnn nAnon Relevant) None (tVar "error_get_sdecl").

#[local] Definition get_decl : state -> key -> context_decl :=
  fun s k =>
  let n' := length (newc s) - k -1 in
  lift_cdecl n' (nth n' (newc s) ERROR_CDECL).

Section Get.

  Context {X : Type}.
  Context (f : nat -> context_decl -> X).

  #[local] Definition geti_key: keys -> nat -> key :=
    fun ks pos1 => nth pos1 ks 200.

  #[local] Definition getij_key : list keys -> nat -> nat -> key :=
  fun kss pos1 pos2 =>
  let ks := nth pos1 kss [] in
  nth pos2 ks 200.

  #[local] Definition get_X : state -> key -> X :=
    fun s k => f (#|newc s| - k -1) (get_decl s k).

  #[local] Definition geti_X : state -> keys -> nat -> X :=
      fun s ks pos_k => get_X s (geti_key ks pos_k).

  #[local] Definition getij_X : state -> list keys -> nat -> nat -> X :=
  fun s kss pos_k1 pos_k2 => get_X s (getij_key kss pos_k1 pos_k2).

  #[local] Definition get_Xs : state -> keys -> list X :=
  fun s ks => map (fun k => get_X s k) ks.

End Get.


(* 1.1 Get terms *)
#[local] Definition get_sdecl_term : nat -> context_decl -> term :=
  fun n ' (mkdecl _ bd _) =>
  match bd with
  | Some tm => lift0 1 tm
  | None => tRel n
  end.

Definition get_term := get_X get_sdecl_term.
Definition geti_term := geti_X get_sdecl_term.
Definition getij_term := getij_X get_sdecl_term.
Definition get_terms := get_Xs get_sdecl_term.

(* 1.2 Get types *)
#[local] Definition get_sdecl_type : nat -> context_decl -> term :=
  fun _ ' (mkdecl _ _ ty) => lift0 1 ty.

Definition get_type   := get_X   get_sdecl_type.
Definition geti_type  := geti_X  get_sdecl_type.
Definition getij_type := getij_X get_sdecl_type.
Definition get_types  := get_Xs  get_sdecl_type.

(* 1.3 Get aname *)
#[local] Definition get_sdecl_aname : nat -> context_decl -> aname :=
  fun _ cdecl => cdecl.(decl_name).

Definition get_aname   := get_X   get_sdecl_aname.
Definition geti_aname  := geti_X  get_sdecl_aname.
Definition getij_aname := getij_X get_sdecl_aname.
Definition get_anames  := get_Xs  get_sdecl_aname.


(* 1.4 Get name *)
#[local] Definition get_sdecl_name : nat -> context_decl -> name :=
  fun _ cdecl => cdecl.(decl_name).(binder_name).

Definition get_name   := get_X   get_sdecl_name.
Definition geti_name  := geti_X  get_sdecl_name.
Definition getij_name := getij_X get_sdecl_name.
Definition get_names  := get_Xs  get_sdecl_name.


(* 1.5 Check *)
Definition get_pos : state -> key -> nat :=
  fun s k => #|newc s| -k -1.

Definition check_pos: state -> key -> nat -> bool :=
  fun s k read_pos => eqb (#|newc s| -k -1) read_pos.



(* 2. Access by position *)

#[local] Definition getp_cdecl : state -> nat -> context_decl :=
  fun s pos => nth pos s.(state_context) ERROR_CDECL.

Definition getp_key : state -> nat -> key :=
  fun s pos => pos.

Definition getp_aname : state -> nat -> aname :=
  fun s pos => (getp_cdecl s pos).(decl_name).

Definition getp_body : state -> nat ->  option term :=
  fun s pos => (getp_cdecl s pos).(decl_body).

Definition getp_type : state -> nat -> term :=
  fun s pos => (getp_cdecl s pos).(decl_type).

Definition check_key : state -> key -> nat -> bool :=
  fun s k pos => eqb (#|newc s| -k -1) (getp_key s pos).

Definition check_keys : state -> keys -> nat -> bool :=
  fun s ks pos => fold_right (fun k c => (check_key s k pos) || c) false ks.


(* 3. Others *)
From MetaRocq Require Import Template.Checker.
Import RedFlags.

#[local] Definition nozeta_flags := mk true true false true true true.

Definition reduce_lets : state -> term -> term :=
  fun s t => expand_lets (newc s) t.

Definition reduce_except_lets :  global_env -> state -> term -> term :=
  fun E s t =>
  match reduce_stack nozeta_flags E (newc s) 5000 t [] with
  | Some t => zip t
  | None => tVar "ERREUR REDUCTION"
  end.


Definition isInd (t : term) : bool :=
  match t with
  | tInd _ _ => true
  | _ => false
  end.

(** Reduce a type so that the inductive structure is apparent.
  Strategy: take the hnf [t'] of a term [t], if it starts with tInd, 
  recursively compute the inductive structure, 
  otherwise return [t].
*)
Fixpoint reduce_inds_fuel n (Σ : global_env) Γ (t : term) : term := 
  match n with
  | 0 => t
  | S n =>
    match reduce_stack default Σ Γ n t [] with
    | Some c' =>
      let hd := c'.1 in
      if isInd hd then
        (map_constr_with_binders Σ (fun Γ t => reduce_inds_fuel n Σ Γ t) Γ (zip c'))
      else t
    | None => t
    end
  end.

Definition reduce_inds : global_env -> state -> term -> term :=
  fun E s t => reduce_inds_fuel 5000 E (newc s) t.

Definition reduce_full : global_env -> state -> term -> term :=
  fun E s t =>
  match reduce_stack default E (newc s) 5000 t [] with
  | Some t => zip t
  | None => tVar "ERREUR REDUCTION"
  end.