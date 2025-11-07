From Stdlib Require Export List.
Export ListNotations.

From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Export All.

(* Aux Functions *)
Definition isSome {A} : option A -> bool :=
  fun x => match x with Some _ => true | _ => false end.

Definition fold_right_i {A B} : (nat -> B -> A -> A) -> A -> list B -> A :=
  fun f a =>
  let fix aux n l : A :=
    match l with
    | [] => a
    | b :: l => f n b (aux (S n) l)
  end in
  aux 0.

Definition fold_left_i {A B} : (nat -> A -> B -> A) -> list B -> A -> A :=
  fun f =>
  let fix aux n l a0 : A :=
    match l with
    | [] => a0
    | b :: l => aux (S n) l (f n a0 b)
  end in
  aux 0.

Definition find_errori {A} (p : A -> bool) (l : list A) (default : A) : nat * A :=
  let fix aux n l : nat * A :=
    match l with
    | [] => (n , default)
    | a::l => if p a then (n, a) else aux (S n) l
    end
  in aux 0 l.

(*

This interface is inspired from work by Weituo DAI, and Yannick Forester

#############################
###      Constrains       ###
#############################

1. Be able to refer to variables indirectly by names
2. Keep track of the old variables for weakening
3. Be able to replace variables by term on the fly


#############################
###   Backend interface   ###
#############################


(* 0. Datastructre and General Purposed Functions *)
- state_decl : Type
- state : Type
- init_state : state

(* 1. General Purposed Functions *)
- add_idecl : state_decl -> state -> state
- add_pdecl : state_pdecl -> state -> state


(* 2. Debug and Printing Functions *)
- state_to_term : state -> list term





*)





(* 0. Datastructre *)
Record state_pdecl : Type := mk_pdecl
{ state_kname       : kername ;
  state_uparams     : context ;
  state_nb_uparams  : nat ;
  state_nuparams    : context ;
  state_nb_nuparams : nat ;
  state_mdecl       : mutual_inductive_body ;
}.

Record state : Type := mk_state
{ state_context : context;
  state_context_debug : list (option ident);
  state_subst : list term ;
  state_inds : list state_pdecl ;
}.

Definition init_state : state := mk_state [] [] [] [].

Definition newc : state -> context := state_context.

(* 1. General Purposed Functions  *)
Definition add_pdecl : state_pdecl -> state -> state :=
  fun pdecl s => mk_state s.(state_context) s.(state_context_debug) s.(state_subst) (pdecl :: s.(state_inds)).

#[local] Definition weaken_aux : nat -> state -> term -> term :=
  fun n s => subst s.(state_subst) n.

Definition weaken : state -> term -> term := weaken_aux 0.

#[local] Definition weaken_decl_aux : nat -> state -> context_decl -> context_decl :=
  fun n s cdecl =>
  let ' (mkdecl an db ty) := cdecl in
  mkdecl an (option_map (weaken_aux n s) db) (weaken_aux n s ty).

Definition weaken_decl : state -> context_decl -> context_decl := weaken_decl_aux 0.

Definition weaken_context : state -> context -> context :=
  fun s cxt => rev (mapi (fun i cdecl => weaken_decl_aux i s cdecl) (rev cxt)).



  (*
#############################
###    Info for Nesting   ###
#############################

*)

Record one_param_env : Type := mk_one_param_env
{ ep_kname          : kername ;
  ep_nb_uparams     : nat ;
  ep_type_uparams   : list term ;
  ep_strpos_uparams : list bool ;
  ep_cparam_kname   : kername ;
  ep_fdt_kname      : kername;
  (* ep_func_kname     : kername *)
}.

Definition param_env := list one_param_env.

Definition BinBinder := (aname -> term -> term -> term).