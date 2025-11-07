From MetaRocq.NestedElim Require Import api_debruijn.
From MetaRocq.NestedElim Require Import sparse_parametricity.
From MetaRocq.NestedElim Require Import sparse_parametricity_rec_hyp.


Section FdTheorem.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (knamep : kername).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : param_env).


  Section GenTypes.

  Context (binder : aname -> term -> term -> term).

  Definition closure_uparams_preds_hold : state -> (list (context_decl * bool)) ->
      (state -> keys -> keys -> keys -> keys -> term) -> term :=
    fun s x => fold_right_state_opt 4 s x
      (fun s _ ' (mkdecl an db ty, b) cc =>
        (* add old_param *)
        let* s key_uparam := kp_binder binder s (Some "uparams") an ty in
        (* add a predicate and that it holds *)
        match b with
        | false => cc s [key_uparam] [1000] [key_uparam] [1000]
        | true =>
            (* add pred *)
          (* get local vars + make cxt *)
            let '((ans, tys), _) := decompose_prod (get_type s key_uparam) in
            let cxt := rev (map2 (fun an ty => mkdecl an None ty) ans tys) in
            let name := name_map (fun x => "P" ^ x) an.(binder_name) in
            let ty_pred := (
              let* s key_lc := closure_context tProd s (Some "locals") cxt in
              tProd (mkBindAnn nAnon Relevant) (mkApps (get_term s key_uparam) (get_terms s key_lc)) U.(out_univ)
            ) in
            let* s key_pred := mk_binder binder s (Some "preds") (mkBindAnn name Relevant) ty_pred in
            (* add it holds *)
            let nameHP := name_map (fun x => ("HP" ^ x)) an.(binder_name) in
            let ty_pred_holds := (
              let* s key_lc := closure_context tProd s (Some "locals") cxt in
              let name := name_map (fun x => "p" ^ x) an.(binder_name) in
              let* s key_varPred := mk_tProd s (Some "app_loc") (mkBindAnn name Relevant) (mkApps (get_term s key_uparam) (get_terms s key_lc)) in
              (mkApps (get_term s key_pred) (get_terms s key_lc ++ [get_term s key_varPred]))
            ) in


                  (* (let* s key_varPred := mk_tProd s None (mkBindAnn nAnon Relevant) (get_term s key_uparam) in
                                         (mkApp (get_term s key_pred) (get_term s key_varPred))) in *)
            let* s key_pred_holds := mk_binder binder s (Some "preds_hold") (mkBindAnn nameHP Relevant) ty_pred_holds in
            cc s [key_uparam] [key_pred] [key_pred; key_uparam] [key_pred_holds]
        end
      ).


  (* 2. Return type *)
  Section mkReturnType.

  Context (s : state).
  Context (key_uparams : keys).
  Context (key_uparams_preds : keys).
  Context (pos_indb : nat).

  Definition make_ccl : state -> keys -> keys -> key -> term :=
    fun s key_nuparams key_indices key_VarMatch =>
    mkApp (make_ind s knamep pos_indb key_uparams_preds key_nuparams key_indices)
          (get_term s key_VarMatch).

  Definition make_return_type : term :=
    let* s key_nuparams := closure_nuparams tProd s kname in
    let* s key_indices  := closure_indices  tProd s kname pos_indb in
    let* s key_VarMatch := mk_tProd s (Some "VarMatch") (mkBindAnn (nNamed "x") (get_relevance s kname pos_indb))
                            (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
    make_ccl s key_nuparams key_indices key_VarMatch.

  End mkReturnType.

  End GenTypes.


(* ############################################### *)
(*    2. Make the type of the fundamental lemma    *)
(* ############################################### *)

Definition local_fundamental_lemma_type (pos_indb : nat) : term :=
  (* 0. initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams s kname)) strpos_uparams in
  let* s := subst_ind s kname in
  (* 1. Closure param + preds *)
  let* s key_uparams key_preds key_uparams_preds _ := closure_uparams_preds_hold tProd s annoted_uparams in
  (* 2. Ccl *)
  make_return_type s key_uparams key_uparams_preds pos_indb.




(* ################################### *)
(*    3. Make the fundamental lemma    *)
(* ################################### *)


  Section GetRecCall.

  Context (s : state).
  Context (key_uparams       : keys).
  Context (key_preds         : keys).
  Context (key_uparams_preds : keys).
  Context (key_preds_hold    : keys).
  Context (key_fixs          : keys).

  Definition make_indp : state -> nat -> keys -> list term -> list term -> term :=
    fun s pos_indb key_uparams_preds nuparams indices =>
    mkApps (tInd (mkInd knamep pos_indb) [])
           (get_terms s key_uparams_preds ++ nuparams ++ indices).

  Definition compute_args_fix : keys -> list term :=
    fun key_args =>
    fold_right (fun key_arg t =>
      let red_ty := reduce_full E s (get_type s key_arg ) in
      match make_cparam_call make_indp kname strpos_uparams Ep s [] key_uparams key_preds
              key_uparams_preds key_preds_hold key_fixs key_arg red_ty with
      | Some (rc_ty, rc_tm) => (get_term s key_arg) :: rc_tm :: t
      | None => (get_term s key_arg) :: t
      end
    ) [] key_args.

End GetRecCall.


(* 3. Compute the custom parametricty  *)
Definition local_fundamental_lemma_term (pos_indb : nat) : term :=
  (* 0. initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams s kname)) strpos_uparams in
  let* s := subst_ind s kname in
  (* 1. add uparams + extra predicate *)
  let* s key_uparams key_preds key_uparams_preds key_preds_hold :=
        closure_uparams_preds_hold tLambda s annoted_uparams in
  (* 2. fixpoint *)
  let tFix_type pos_indb := make_return_type s key_uparams key_uparams_preds pos_indb in
  let tFix_rarg := tFix_default_rarg s kname in
  let* s key_fixs pos_indb := mk_tFix kname tFix_type tFix_rarg s pos_indb in
  (* 3. closure nuparams + indices + var match *)
  let* s key_nuparams := closure_nuparams tLambda s kname in
  let* s key_indices  := closure_indices  tLambda s kname pos_indb in
  let* s key_VarMatch := mk_tLambda s (Some "VarMatch") (mkBindAnn (nNamed "x") (get_relevance s kname pos_indb))
                        (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
  (* 4. match VarMatch *)
  let tCase_pred := (fun s => make_ccl key_uparams_preds pos_indb s key_nuparams) in
  let* s _ key_args _ pos_ctor := mk_tCase kname pos_indb tCase_pred
                          key_uparams key_nuparams s (get_term s key_VarMatch) in
  (* 5. Conclude *)
  (mkApps (make_cst s knamep pos_indb pos_ctor key_uparams_preds key_nuparams)
          (compute_args_fix s key_uparams key_preds key_uparams_preds key_preds_hold
            key_fixs key_args)).


End FdTheorem.