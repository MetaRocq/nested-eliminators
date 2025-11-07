From PluginNestedElim Require Import core.

(* Access the inductive type
- get_pdecl        : kername -> state -> state_pdecl
- get_uparams      : kername -> state -> context
- get_nb_uparams   : kername -> state -> nat
- get_nuparams     : kername -> state -> context
- get_nb_nuparams  : kername -> state -> nat
- get_params       : kername -> state -> context
- get_nb_params    : kername -> state -> nat
- get_mdecl        : kername -> state -> mutual_inductive_body
- get_ind_bodies   : kername -> state -> list one_inductive_body
- get_all_args     : kername -> state -> list context
- get_indb         : kername -> nat -> state -> one_inductive_body
- get_relevance    : kername -> nat -> state -> relevance
- get_ctor         : kername -> nat -> nat   -> state -> constructor_body
- get_indices      : kername -> nat -> state -> context
- get_ctor_indices : kername -> nat -> nat   -> state -> list term
*)

#[local] Definition ERROR_GET_PDECL : state_pdecl :=
  mk_pdecl (MPfile [], "ERROR") [] 0 [] 0
    (Build_mutual_inductive_body Finite 0 [] [] (Monomorphic_ctx) None).

Section GetInds.

  Context (s : state).
  Context (kname : kername).

  Definition get_pdecl : state_pdecl :=
      match find (fun pdecl => eqb pdecl.(state_kname) kname) s.(state_inds) with
      | Some pdecl => pdecl
      | None => ERROR_GET_PDECL
      end.

  Definition get_uparams : context :=
    get_pdecl.(state_uparams).

  Definition get_nb_uparams : nat :=
    get_pdecl.(state_nb_uparams).

  Definition get_nuparams : context :=
    get_pdecl.(state_nuparams).

  Definition get_nb_nuparams : nat :=
    get_pdecl.(state_nb_nuparams).

  Definition get_params : context :=
    get_pdecl.(state_mdecl).(ind_params).

  Definition get_nb_params : nat :=
    get_pdecl.(state_mdecl).(ind_npars).

  Definition get_mdecl : mutual_inductive_body :=
    get_pdecl.(state_mdecl).

  Definition get_ind_bodies : list one_inductive_body :=
    get_pdecl.(state_mdecl).(ind_bodies).

  Definition get_all_args : list context :=
    map cstr_args (concat (map ind_ctors get_mdecl.(ind_bodies))).

  #[local] Definition ERROR_GET_INDB : one_inductive_body :=
    Build_one_inductive_body "ERROR GET_INDB" [] sProp (tVar "ERROR GET_INDB") IntoAny [] [] Relevant.

  Context (pos_indb : nat).

  Definition get_indb : one_inductive_body :=
    nth pos_indb get_ind_bodies ERROR_GET_INDB.

  Definition get_relevance : relevance :=
    get_indb.(ind_relevance).

  #[local] Definition ERROR_GET_CTOR : constructor_body :=
    Build_constructor_body "ERROR GET CTOR" [] [] (tVar "ERROR GET CTOR") 0.

  Definition get_ctors : list constructor_body :=
    get_indb.(ind_ctors).

  Context (pos_ctor : nat).

  Definition get_ctor : constructor_body :=
    nth pos_ctor get_indb.(ind_ctors) ERROR_GET_CTOR.

  Definition get_args : context :=
    get_ctor.(cstr_args).

  Definition get_indices : context :=
    weaken_context s get_indb.(ind_indices).

  Definition get_ctor_indices : list term :=
    map (weaken s) get_ctor.(cstr_indices).

End GetInds.