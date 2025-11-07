From PluginNestedElim Require Import api_debruijn.


Unset Guard Checking.

Section PreprocessParameters.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (E : global_env).

  Definition nb_params := mdecl.(ind_npars).


(* Extra functions as we don't know the number of uparams which is neccassary for the api *)
#[local] Definition get_all_args : mutual_inductive_body -> list context :=
  fun mdelc => map cstr_args (concat (map ind_ctors mdecl.(ind_bodies))).


Definition first_false : list bool -> nat :=
  let fix aux n l :=
  match l with
  | true :: l => aux (S n) l
  | _ => n
  end in
  aux 0.

Definition default_value := nb_params.


Section CheckUniform.

  Context (key_inds   : keys).
  Context (key_params : keys).

  (* 1. Compute the number of uniform params for an instance *)
  Definition check_term : state -> key -> term -> bool :=
    fun s k tm => eqb (get_term s k) tm.

  Definition check_uniform : state -> keys -> list term -> nat :=
    fun s key_params tm =>
    first_false (map2 (fun x y => check_term s x y) key_params tm).
    (* default_value. *)

  (* 2. Compute the number of uniform parameters of an argument *)
  #[using="All"]
  Fixpoint preprocess_uparams_arg (s : state) (ty : term) {struct ty} : _ :=
    (* default_value. *)
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* Check for local arg *)
    | tProd an A B => let* s key_local := add_old_var s (Some "local_arg") an A in
                      preprocess_uparams_arg s B
    | tLetIn an db A B => let* s key_local := add_old_letin s (Some "local_let") an db A in
                          preprocess_uparams_arg s B
    (* Check if is the inductive *)
    | tRel n => if check_keys s key_inds n
                then check_uniform s key_params (firstn nb_params iargs)
                else default_value
    (* Otherwise if it is nested *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        fold_right min default_value (map (fun x => preprocess_uparams_arg s x) iargs)
    | _ => default_value
    end.

End CheckUniform.


(* 3. Compute the number of uniform parameters of an inductive type *)
#[using="All"] Definition preprocess_uparams : nat :=
  let s := init_state in
  let* s key_inds := add_inds mdecl s in
  let* s _ key_params _ := add_old_context s (Some "params") mdecl.(ind_params) in
  check_ctors_by_arg min default_value E s (preprocess_uparams_arg key_inds key_params) (get_all_args mdecl).


(* 4. Debug functions *)
Section Debug.

  Context (key_inds   : keys).
  Context (key_params : keys).

  #[using="All"]
  Fixpoint debug_preprocess_uparams_arg (s : state) (ty : term) {struct ty} : term :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* Check for local arg *)
    | tProd an A B => let* s key_local := add_old_var s (Some "local_arg") an A in
                      debug_preprocess_uparams_arg s B
    | tLetIn an db A B => let* s key_local := add_old_letin s (Some "local_let") an db A in
                          debug_preprocess_uparams_arg s B
    (* Check if is the inductive *)
    | tRel n => mkApps (tVar "DEBUG CASE tRel:")
                  [ (state_to_term s) ;
                    (mkApp (tVar "DEBUG tRel case, type := ") ty)
                  ]
                (* if check_ids n key_inds s
                then check_uniform key_params (firstn nb_params iargs) s
                else default_value *)
    (* Otherwise if it is nested *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        mkApps (tVar "nested") (map (fun x => debug_preprocess_uparams_arg s x) iargs)
    | _ => mkApp ty (state_to_term s)
        end.

End Debug.

#[using="All"] Definition debug_preprocess_uparams : _ :=
  let s := init_state in
  let* s key_inds := add_inds mdecl s in
  let* s _ key_params _ := add_old_context s (Some "params") mdecl.(ind_params) in
  debug_check_ctors_by_arg E s (debug_preprocess_uparams_arg key_inds key_params) (get_all_args mdecl).

End PreprocessParameters.
