From MetaRocq.NestedElim Require Import api_debruijn.

(*
  Structure:

  1. Make Different Types
    1.1 Make the type of the predicates
    1.2 Make the type of the constructors
    1.3 Make the return type
  2. Make the type of the eliminators
  3. Make the the eliminators

*)

Unset Guard Checking.

Section GenRecursors.

Context (kname : kername).
Context (mdecl : mutual_inductive_body).
Context (nb_uparams : nat).
Context (U : output_univ).
Context (E : global_env).
Context (Ep : param_env).


(* ################################# *)
(*    1. Make the different types    *)
(* ################################# *)

Section GenTypes.

  Context (binder : aname -> term -> term -> term).

  (* 1.1 Make Type Predicate(s) *)

  Section MkPreds.

  Context (key_uparams : keys).

  (* 1.1.1 Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
      (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  Definition make_type_pred : state -> nat -> term :=
    fun s pos_indb =>
    let* s key_nuparams := closure_nuparams tProd s kname in
    let* s key_indices  := closure_indices  tProd s kname pos_indb in
    tProd (mkBindAnn nAnon (get_relevance s kname pos_indb))
          (make_ind s kname pos_indb key_uparams key_nuparams key_indices)
          U.(out_univ).

  (* 1.1.1 Associated continuation *)
  Definition naming_pred pos_indb : ident := make_name0 "P" pos_indb.

  Definition make_type_pred_cc s pos_indb cc : term :=
    mk_binder binder s (Some "preds") (mkBindAnn (nNamed (naming_pred pos_indb)) Relevant)
              (make_type_pred s pos_indb) cc.

  End MkPreds.

  Definition closure_preds : state -> kername -> keys -> (state -> keys -> term) -> term :=
    fun s kname key_uparams cc => iterate_inductives 1 s kname (make_type_pred_cc key_uparams) cc.

  Definition make_pred : state -> keys -> nat -> list term -> list term -> term :=
    fun s key_preds pos_indb nuparams indices =>
    mkApps (geti_term s key_preds pos_indb) (nuparams ++ indices).


  (* 1.2. Make Type Constructor(s) *)

  Section MkCtor.

  Context (key_uparams : keys).
  Context (key_preds   : keys).
  Context (key_fixs    : keys).

  (* 1.2.1 Compute Recursive Call *)

  (* to instantiate parametricity *)
  Fixpoint add_param (strpos : list bool) (l : list term) (rc : list (option (term * term))) : list term * list term :=
    match strpos, l, rc with
    | nil, nil, nil => (nil , nil)
    | true :: strpos, A::l, x :: rc =>
        let (lty, ltm) := add_param strpos l rc in
        match x with
        | None => (A :: (funTrue A) :: lty, A :: (funTrue A) :: (funI A) :: ltm)
        | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
        end
    | false :: strpos, A::l, x :: rc =>
      let (lty, ltm) := add_param strpos l rc in (A :: lty, A :: ltm)
    | _, _, _ => (nil, nil)
  end.

  Fixpoint decompose_lambda (t : term) : (list aname × list term) × term :=
    match t with
    | tLambda n A B => let (nAs, B0) := decompose_lambda B in
                    let (ns, As) := nAs
                    in (n :: ns, A :: As, B0)
    | _ => ([], [], t)
    end.


  Program Fixpoint make_rec_call (s : state) (key_arg : key) (ty : term) {struct ty} : option (term * term) :=
    match view_args s kname Ep [] ty with
    | VArgIsFree _ _ _ => None
    | VArgIsInd pos_indb loc local_nuparams local_indices =>
              (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
        Some (let* s _ key_locals _ := closure_context_sep tProd s (Some "local") loc in
              mkApp (make_pred s key_preds pos_indb local_nuparams local_indices)
                    (mkApps (get_term s key_arg) (get_terms s key_locals)),
              (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
              let* s _ key_locals _ := closure_context_sep tLambda s (Some "local") loc in
              mkApp (mkApps (geti_term s key_fixs pos_indb) (local_nuparams ++ local_indices))
                    (mkApps (get_term s key_arg) (get_terms s key_locals)))
    | VArgIsNested xp pos_indb loc local_uparams local_nuparams_indices type_uparams =>
      let compute_nested_rc (s : state) (i : nat) (x : term) : (option (term * term)) :=
          (* add llargs to the context *)
          let ' (ans, tys, x) := decompose_lambda x in
          let cxt := rev (map2 (fun an ty => mkdecl an None ty) ans tys) in
          let* s _ key_lc _ := add_fresh_context s None cxt in
          (* new var *)
          let anx := mkBindAnn nAnon Relevant in
          let* s key_farg := add_fresh_var s (Some "rec_arg") anx x in
          (* rc call *)
          match make_rec_call s key_farg (get_type s key_farg) with
          | Some (ty, tm) => Some (
              fold_binder tLambda cxt (tLambda anx x ty),
              fold_binder tLambda cxt (tLambda anx x tm)
              )
          | None => None
          end
      in
      (* add local variables: largs*)
      let* s _ key_locals _ := add_old_context s (Some "local") loc in
      (* compute rec call *)
      let rec_call := mapi (fun i x => compute_nested_rc s i x) local_uparams in
      if existsb isSome rec_call
        (* If some instatiate the parametricty  *)
      then let (lty, ltm) := add_param xp.(ep_strpos_uparams) local_uparams rec_call in
            Some ( fold_binder tProd loc (
                  mkApp (mkApps (tInd (mkInd xp.(ep_cparam_kname) pos_indb) [])
                               (lty ++ local_nuparams_indices))
                        (mkApps (get_term s key_arg) (get_terms s key_locals))),
                fold_binder tLambda loc (
                mkApp (mkApps (tConst xp.(ep_fdt_kname) [])
                              (ltm ++ local_nuparams_indices))
                              (mkApps (get_term s key_arg) (get_terms s key_locals))))
      else None
    end.


  (* 1.2.1 Generates the type associated to an argument *)
  Definition type_arg_cc : state -> nat -> key -> (state -> keys -> term) -> term :=
    fun s _ key_arg cc =>
    let red_ty := reduce_full E s (get_type s key_arg) in
    match make_rec_call s key_arg red_ty with
    | Some (ty, _) => mk_tProd s (Some "rec_call") (mkBindAnn nAnon Relevant) ty
                        (fun s key_rec => cc s [key_arg] )
    | None => cc s [key_arg]
    end.

  (* 1.2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall x0 : t0, [P x0], ..., xn : tn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  Definition make_type_ctor : state -> nat -> nat -> term :=
  fun s pos_indb pos_ctor =>
  let* s key_nuparams := closure_nuparams tProd s kname in
  let* s key_args     := closure_by_arg tProd 1 s kname pos_indb pos_ctor
                          (cc_nosave 1) type_arg_cc  in
  mkApp (make_pred s key_preds pos_indb (get_terms s key_nuparams) (get_ctor_indices s kname pos_indb pos_ctor))
        (mkApps (make_cst s kname pos_indb pos_ctor key_uparams key_nuparams)
                (get_terms s key_args)).

  (* 1.2.3 The associated continuation *)
  Definition make_type_ctor_cc s pos_indb pos_ctor cc : term :=
    let name := make_name_bin "f" pos_indb pos_ctor in
    mk_binder binder s (Some name) (mkBindAnn (nNamed name) Relevant)
              (make_type_ctor s pos_indb pos_ctor) cc.

  End MkCtor.

  Definition closure_ctors s kname key_uparams key_preds cc : term :=
    iterate_all_ctors 1 s kname (make_type_ctor_cc key_uparams key_preds []) cc.


  (* 1.3 Make Return Type *)

  Section MkCcl.

  Context (s :state).
  Context (key_uparams : keys).
  Context (key_preds   : keys).
  Context (pos_indb : nat).

  (* 1.3.1 Make the type of the conclusion *)
  (* P B0 ... Bm i0 ... il x *)
  Definition make_ccl : state -> keys -> keys -> key -> term :=
    fun s key_nuparams key_indices key_VarMatch =>
    mkApp (make_pred s key_preds pos_indb (get_terms s key_nuparams) (get_terms s key_indices))
          (get_term s key_VarMatch).

  (* 1.3.2 Make the return type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  Definition make_return_type : term :=
    let* s key_nuparams := closure_nuparams tProd s kname in
    let* s key_indices  := closure_indices  tProd s kname pos_indb in
    let* s key_VarMatch := mk_tProd s (Some "VarMatch")
                            (mkBindAnn (nNamed "x") (get_relevance s kname pos_indb))
                            (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
    make_ccl s key_nuparams key_indices key_VarMatch.

  End MkCcl.

  End GenTypes.



(* ####################################### *)
(*    2. Make the type of the eliminators    *)
(* ####################################### *)

Definition gen_rec_type (pos_indb : nat) : term :=
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s := subst_ind s kname in
  let* s key_uparams := closure_uparams tProd s kname in
  let* s key_preds   := closure_preds   tProd s kname key_uparams in
  let* s key_ctors   := closure_ctors   tProd s kname key_uparams key_preds in
  make_return_type s key_uparams key_preds pos_indb.



(* ####################################### *)
(*    3. Make the type of the eliminators    *)
(* ####################################### *)

(* 3.1 Compute the arguments of the rec call *)
Section GetRecCall.

  Context (s : state).
  Context (key_preds : keys).
  Context (key_fixs  : keys).

  Definition compute_args_fix : keys -> list term :=
    fun key_args =>
    fold_right (fun key_arg t =>
      let red_ty := reduce_full E s (get_type s key_arg) in
      match make_rec_call key_preds key_fixs s key_arg red_ty with
      | Some (rc_ty, rc_tm) => (get_term s key_arg) :: rc_tm :: t
      | None => (get_term s key_arg) :: t
      end
    ) [] key_args.

End GetRecCall.


(* 3.2 Generates the recursor *)
Definition gen_rec_term (pos_indb : nat) : term :=
  (* 0. Initialise state with inductives *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s := subst_ind s kname in
  (* 1. Closure Uparams / preds / ctors *)
  let* s key_uparams := closure_uparams tLambda s kname in
  let* s key_preds   := closure_preds   tLambda s kname key_uparams in
  let* s key_ctors   := closure_ctors   tLambda s kname key_uparams key_preds in
  (* 2. Fixpoint *)
  let tFix_type pos_indb := make_return_type s key_uparams key_preds pos_indb in
  let tFix_rarg := tFix_default_rarg s kname in
  let* s key_fixs pos_indb := mk_tFix kname tFix_type tFix_rarg s pos_indb in
  (* 3. Closure Nuparams / Indices / Var *)
  let* s key_nuparams := closure_nuparams tLambda s kname in
  let* s key_indices  := closure_indices  tLambda s kname pos_indb in
  let* s key_VarMatch := mk_tLambda s (Some "VarMatch")
                        (mkBindAnn (nNamed "x") Relevant)
                        (make_ind s kname pos_indb key_uparams key_nuparams key_indices) in
  (* 4. Proof of P ... x by match *)
  let tCase_pred := (fun s => make_ccl key_preds pos_indb s key_nuparams) in
  let* s _ key_args _ pos_ctor := mk_tCase kname pos_indb
          tCase_pred key_uparams key_nuparams s (get_term s key_VarMatch) in
  (* 5. Make the branch *)
  (mkApps (getij_term s key_ctors pos_indb pos_ctor)
          (get_terms s key_nuparams ++ compute_args_fix s key_preds key_fixs key_args)).


End GenRecursors.