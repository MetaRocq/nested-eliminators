From PluginNestedElim Require Import core.
From PluginNestedElim Require Import fold_functions.


(* Add terms to state
- notation: "let* x .. z ':=' c1 'in' c2"
- fresh_ident : option ident -> state -> ident
- add_old_var {X}       : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_old_context {X}   : option ident -> context -> state -> (list ident -> list ident -> list ident -> state -> X) -> X
- add_fresh_var {X}     : option ident -> context_decl -> state -> (ident -> state -> X) -> X
- add_fresh_context {X} : option ident -> context -> state -> (list ident -> state -> X) -> X
- subst_old_var {X}     : term -> state -> (state -> X) -> X
- subst_old_vars {X}    : list term -> state -> (state -> X) -> X

*)

Notation "let* x .. z ':=' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).

Definition key := nat.
Definition keys := list nat.
Definition fresh_key : state -> key :=
  fun s => #|s.(state_context)|.

Definition lift1 : list term -> list term :=
    map (lift0 1).




(* 1. Add existing var / letin / context *)

Definition add_ovar (s : state) (x : option ident) (an : aname) (ty : term) : state :=
  mk_state (newc s ,, vass an (weaken s ty))
           (state_context_debug s ,, x)
           (lift1 s.(state_subst),, tRel 0)
           (state_inds s).

Definition add_old_var {X} : state -> option ident -> aname -> term -> (state -> key -> X) -> X :=
fun s x an ty cc =>
  let s' := add_ovar s x an ty in
  cc s' (fresh_key s).


Definition add_oletin (s : state) (x : option ident) (an : aname) (db : term) (ty : term) : state :=
mk_state (newc s ,, vdef an (weaken s db) (weaken s ty))
         (state_context_debug s ,, x)
         (lift1 s.(state_subst),, tRel 0)
         (state_inds s).

Definition add_old_letin {X} : state -> option ident -> aname -> term -> term -> (state -> key -> X) -> X :=
  fun s x an db ty cc =>
    let s' := add_oletin s x an db ty in
    cc s' (fresh_key s).


Definition add_ocontext (s : state) (x : option ident) (cxt : context) : state :=
  fold_right (fun ' (mkdecl an z ty) s =>
    match z with
    | None => add_ovar s x an ty
    | Some db => add_oletin s x an db ty
    end) s cxt.

(* To rebuild on top of add_ocontext to make dependent *)
Definition add_old_context {X} : state -> option ident -> context ->
    (state -> keys -> keys -> keys -> X) -> X :=
  fun s x cxt => fold_left_state_opt 3 s cxt
    ( fun s _ ' (mkdecl an z ty) cc =>
      match z with
      | Some db => let* s id_let := add_old_letin s x an db ty in
                   cc s [id_let] [] [id_let]
      | None    => let* s id_arg := add_old_var s x an ty in
                   cc s [] [id_arg] [id_arg]
      end
  ).




(* 2. Add fresh var / letin / context *)

Definition add_fvar (s : state) (x : option ident) (an : aname) (ty : term) : state :=
  mk_state (newc s ,, vass an ty)
           (state_context_debug s ,, x)
           (lift1 s.(state_subst))
           (state_inds s).

Definition add_fresh_var {X} : state -> option ident -> aname -> term -> (state -> key -> X) -> X :=
  fun s x an ty cc =>
  let s' := add_fvar s x an ty in
  cc s' (fresh_key s).


Definition add_fletin (s : state) (x : option ident) (an : aname) (db : term) (ty : term) : state :=
  mk_state (newc s ,, vdef an db ty)
            (state_context_debug s ,, x)
            (lift1 s.(state_subst))
            (state_inds s).

Definition add_fresh_letin {X} : state -> option ident -> aname -> term -> term -> (state -> key -> X) -> X :=
  fun s x an db ty cc =>
  let s' := add_fletin s x an db ty in
  cc s' (fresh_key s).


Definition add_fcontext (s : state) (x : option ident) (cxt : context) : state :=
  fold_right (fun ' (mkdecl an z ty) s =>
    match z with
    | None => add_fvar s x an ty
    | Some db => add_fletin s x an db ty
    end) s cxt.

(* To rebuild on top of add_fcontext to make dependent *)
Definition add_fresh_context {X} : state -> option ident -> context ->
    (state -> keys -> keys -> keys -> X) -> X :=
  fun s x cxt => fold_left_state_opt 3 s cxt
    (fun s _ ' (mkdecl an z ty) cc =>
      match z with
      | Some db => let* s id_let := add_fresh_letin s x an db ty  in
                   cc s [id_let] [] [id_let]
      | None    => let* s id_arg := add_fresh_var s x an ty in
                   cc s [] [id_arg] [id_arg]
      end
  ).




(* 3. Substitute existing var / letin / context *)
(* To rebuild to make dependent *)
Definition subst_obind (s : state) (tm : term) : state :=
  mk_state (newc s)
           (state_context_debug s)
           (tm :: lift1 s.(state_subst))
           (state_inds s).

Definition subst_old_bind {X} : state -> term -> (state -> X) -> X :=
  fun s tm cc =>
  let s' := subst_obind s tm in
  cc s'.

Definition subst_ocontext (s : state) (ltm : list term) : state :=
  mk_state (newc s)
  (state_context_debug s)
  (rev ltm ++ map (lift0 #|ltm|) s.(state_subst))
  (state_inds s).

Definition subst_old_context {X} : state -> list term -> (state -> X) -> X :=
  fun s ltm cc =>
  let s' := subst_ocontext s ltm in
  cc s'.

