From MetaRocq.NestedElim Require Import api_debruijn.
From MetaRocq.NestedElim Require Import sparse_parametricity_rec_hyp.

Section SparseParametricity.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (strpos_uparams : list bool).
  Context (U : output_univ).
  Context (E : global_env).
  Context (Ep : param_env).

Definition mk_entry : context -> list one_inductive_entry -> mutual_inductive_entry :=
  fun params inds_entry =>
  {| mind_entry_record    := None;
	   mind_entry_finite    := Finite;
     mind_entry_params    := params;
     mind_entry_inds      := inds_entry;
     mind_entry_universes := universes_entry_of_decl (ind_universes mdecl);
     mind_entry_template  := false;
     mind_entry_variance  := None;
     mind_entry_private   := None
  |}.



(* 1. Make types associated to new inductive *)

Section MkNewTypes.

  Context (annoted_uparams : list (context_decl * bool)).

(* 1.1 Closure by uniform parameters and predicate if strictly positive *)
(* forall A, (PA : A -> U), ... *)
Definition closure_uparams_preds : state -> (state -> keys -> keys -> keys -> term) -> term :=
  fun s => fold_right_state_opt 3 s annoted_uparams
    (fun s _ ' (mkdecl an _ ty, b) cc =>
      (* register P *)
      let* s key_uparam := kp_tProd s (Some "uparams") an ty in
      (* add a predicate *)
      match b with
      | false => cc s [key_uparam] [1000] [key_uparam]
      | true =>
        (* get local vars + make cxt *)
          let '((ans, tys), _) := decompose_prod (get_type s key_uparam) in
          let cxt := rev (map2 (fun an ty => mkdecl an None ty) ans tys) in
          (* name *)
          let name := name_map (fun x => "P" ^ x) an.(binder_name) in
          (* type *)
          let ty_pred := (
            (let* s key_lc := closure_context tProd s (Some "locals") cxt in
            tProd (mkBindAnn nAnon Relevant) (mkApps (get_term s key_uparam) (get_terms s key_lc)) U.(out_univ))
          ) in
        let* s key_pred := mk_tProd s (Some "preds") (mkBindAnn name Relevant) ty_pred in
        cc s [key_uparam] [key_pred] [key_pred; key_uparam]
      end
    ).

  (* 1.2 Make return type of the new inductive with parameters in the context *)
  (* forall i0 ... in, Ind A0 ... Al B0 ... Bm i0 ... in -> U *)
  Definition make_type_ind : state -> keys -> keys -> nat -> term :=
    fun s key_uparams key_nuparams pos_indb =>
    let* s key_indices := closure_indices tProd s kname pos_indb in
    tProd (mkBindAnn nAnon Relevant)
          (make_ind s kname pos_indb key_uparams key_nuparams key_indices)
          U.(out_univ).

  Arguments make_type_ind _ key_uparams key_nuparams _ : rename.

  (* 1.3 Make the full new type *)
  (* forall A, (PA : A -> U) ... B0 ... forall i0 ... in, Ind A0 ... Al B0 ... Bm i0 ... in -> U *)
  Definition make_new_type : nat -> state -> term :=
    fun pos_indb s =>
    let* s key_uparams _ key_uparams_preds := closure_uparams_preds s in
    let* s key_nuparams := closure_nuparams tProd s kname in
    make_type_ind s key_uparams key_nuparams pos_indb.

  (* 1.4 Make the associated context *)
  Definition make_new_context : state -> context :=
    fun s =>
    let ind_bodies := get_ind_bodies s kname in
    let nb_bodies  := length ind_bodies in
    let an := mkBindAnn nAnon Relevant in
    fold_right_i (fun i _ x => mkdecl an None (make_new_type (nb_bodies -i -1) s) :: x)
      [] ind_bodies.

  (* 1.5 Add uniform parameters and predicate if strictly positive *)
  Definition add_uparams_preds {X} : state -> (state -> keys -> keys -> keys -> X) -> X :=
    fun s => fold_right_state_opt 3 s annoted_uparams
      (fun s _ ' (mkdecl an z ty, b) cc =>
        (* register P *)
        let* s key_uparam := add_old_var s (Some "uparams") an ty in
        (* add a predicate *)
        match b with
        | false => cc s [key_uparam] [1000] [key_uparam]
        | true =>
            (* get local vars + make cxt *)
            let '((ans, tys), _) := decompose_prod (get_type s key_uparam) in
            let cxt := rev (map2 (fun an ty => mkdecl an None ty) ans tys) in
            (* name *)
            let name := name_map (fun x => "P" ^ x) an.(binder_name) in
            (* type *)
            let ty_pred := (
              (let* s key_lc := closure_context tProd s (Some "locals") cxt in
              tProd (mkBindAnn nAnon Relevant) (mkApps (get_term s key_uparam) (get_terms s key_lc)) U.(out_univ))
            ) in
            let* s key_pred := add_fresh_var s (Some "preds") (mkBindAnn name Relevant) ty_pred in
            cc s [key_uparam] [key_pred] [key_pred; key_uparam]
        end
      ).

  (* 1.6 Given an argument add the custom parametricty if needed *)
  #[local] Definition make_indp : state -> keys -> nat -> keys -> list term -> list term -> term :=
      fun s key_inds pos_indb key_uparams_preds nuparams indices =>
      mkApps (geti_term s key_inds pos_indb)
             (get_terms s key_uparams_preds ++ nuparams ++ indices).

End MkNewTypes.

(* 2. Compute custom param of an inductive block *)
Section MkInd.

  Context (s : state).
  Context (key_inds          : keys).
  Context (key_uparams       : keys).
  Context (key_preds         : keys).
  Context (key_uparams_preds : keys).
  Context (key_nuparams      : keys).
  Context (pos_indb : nat).

  (* 2.1 Add the paramtricity of an argument if one *)
  Definition make_type_arg : state ->context_decl ->
      (state -> keys -> keys -> keys -> term) -> term :=
    fun s '(mkdecl an db ty) cc =>
    match db with
    | Some db => kp_tLetIn s (Some "let") an db ty (fun s x => cc s [x] [] [])
    | None =>
        let* s key_arg := kp_tProd s (Some "args") an ty in
        let red_ty := reduce_full E s (get_type s key_arg) in
        match make_cparam_call (fun s => make_indp s key_inds) kname strpos_uparams Ep s
                key_inds key_uparams key_preds key_uparams_preds [] [] key_arg red_ty with
        | Some (ty, _) => mk_tProd s (Some "rec_call") (mkBindAnn nAnon Relevant) ty
                            (fun s key_rec => cc s [] [key_arg] [key_rec])
        | None => cc s [] [key_arg] []
        end
    end.

  (* 2.2 Build the type of the custom param of a constructor *)
  Definition mk_ty_cparam : state -> nat -> constructor_body -> term :=
    fun s pos_ctor ctor =>
    let* s _ key_args _ := fold_left_state_opt 3 s ctor.(cstr_args) (fun s _ => make_type_arg s)  in
    (* ind_params1 A0 PA ... B0 ... Bn i0 ... im (cst A0 ... B0 ) *)
    mkApp (make_indp s key_inds pos_indb key_uparams_preds
            (get_terms s key_nuparams) (get_ctor_indices s kname pos_indb pos_ctor))
          (mkApps (make_cst s kname pos_indb pos_ctor key_uparams key_nuparams)
                  (get_terms s key_args)).

  (* 2.3 Compute custom param of the inductive block *)
  Definition mk_ind_entry : one_inductive_body -> state -> one_inductive_entry :=
    fun indb s =>
    {| mind_entry_typename  := indb.(ind_name) ^ "ₛ" ;
       mind_entry_arity     := make_type_ind s key_uparams key_nuparams pos_indb;
       mind_entry_consnames := map (fun ctor => ctor.(cstr_name) ^ "ₛ") indb.(ind_ctors);
       mind_entry_lc        := mapi (fun x y => mk_ty_cparam s x y) indb.(ind_ctors);
    |}.

End MkInd.

(* 3. Compute the custom parametricty  *)
Definition custom_param : mutual_inductive_entry :=
  (* add inds to state *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let annoted_uparams := combine (rev (get_uparams s kname)) strpos_uparams in
  (* Add new inds, uprams and pred, nuparams *)
  let* s := subst_ind s kname in
  let* s _ key_inds _ := add_fresh_context s (Some "inds") (make_new_context annoted_uparams s) in
  let* s key_uparams key_preds key_uparams_preds := add_uparams_preds annoted_uparams s in
  let* s _ key_nuparams _ := add_old_context s (Some "nuparams") (get_nuparams s kname) in
  (* get the context associated to the (new) parameters *)
  let params_preds := (firstn (length key_uparams_preds + length key_nuparams) s.(state_context)) in
  mk_entry params_preds
    (mapi (fun pos_indb indb => mk_ind_entry key_inds key_uparams key_preds key_uparams_preds key_nuparams pos_indb indb s)
          mdecl.(ind_bodies)).

End SparseParametricity.