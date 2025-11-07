(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICOnFreeVarsConv PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv PCUICConfluence.
Import PCUICEnvironment.
From MetaRocq.PCUIC Require Import BDStrengthening.
From MetaRocq.PCUIC Require Import PCUICTactics.

From Formalization Require Import Lemma Positivity_condition.
Import ViewInductive.


Definition All_repeat {A B} {f : A -> B} {b l} :
  All (fun x => f x = b) l -> map f l = repeat b #|l|.
Proof.
  intros X; induction X; cbn; f_equal; eauto.
Qed.


Section StrengthArg.
  Context (nb_block : nat).
  Context (up : list (context_decl * bool)).
  Context (nup : context).

  Definition StrAcc := list argument * list argument * (nat -> nat).

  Definition StrPosAcc (acc : StrAcc) : Type :=
      let oargs := acc.1.1 in let nargs := acc.1.2 in let rename_no_rc := acc.2 in
      All (fun arg => check_lax arg = false) nargs
      (* no rc + pos *)
    * All_telescope (PosArg nb_block up nup) nargs
      (* renaming is well-defined *)
    * (forall P i t,
      rc_notin oargs i t ->
      on_free_vars (shiftnP (#|oargs| + i) P) t ->
      on_free_vars (shiftnP (#|nargs| + i) P) ((rename (shiftn i rename_no_rc) t)))
    * (forall i t, rc_notin oargs i t -> rc_notin nargs i (rename (shiftn i rename_no_rc) t)).

  Definition remove_rc_one (acc : StrAcc) arg :=
    if check_lax arg
    then (acc.1.1 ++ [arg], acc.1.2, strengthen_renaming 1 acc.2)
    else (acc.1.1 ++ [arg], acc.1.2 ++ [rename_argument acc.2 0 arg], shiftn 1 acc.2).

(** t =>>
      ... k + 2 | k + 1 | k -- 0

    unlift 1 k t =>>
      ... (k + 2) - 1 | k -- 0

    lift 1 k (unlift 1 k t) =>>
      ... (k + 2) - 1 + 1 | k -- 0

    t := same term as k + 1 is not in it
*)
  Definition pos_remove_rc_one acc arg :
    PosArg nb_block up nup acc.1.1 arg ->
    StrPosAcc acc ->
    StrPosAcc (remove_rc_one acc arg).
  Proof.
    intros [rc_notin_arg pos_arg].
    (* intros [[oargs nargs] pos_rename_no_rc]. *)
    intros [[[oargs nargs] pos_rename_no_rc] rename_rename_no_rc_r].
    unfold remove_rc_one. destruct (check_lax arg) eqn:lax_arg; cbn in *.
    (* branch true => arg is removed *)
    + repeat split => //.
      - len; cbn. intros P k t rc_notin_t isup_notin_t.
        rewrite rc_notin_lax_true in rc_notin_t => //.
        rewrite -> (unlift_lift 1 k t).
        2: {
          eapply on_free_vars_impl; only 2: apply rc_notin_t.
          eapply shiftnP_impl. unfold shiftnPneg.
          intros i; destruct i; done.
        }
        rewrite shiftn_strengthen.
        eapply (pos_rename_no_rc P).
        (* so tedious *)
        * unfold rc_notin, unlift, rc_notin_bool.
          rewrite on_free_vars_rename.
          unfold shiftnPneg in rc_notin_t. unfold unlift_renaming.
          eapply on_free_vars_impl; only 2 : apply rc_notin_t.
          intros i. unfold shiftnP; cbn.
          repeat case_inequalities => //.
          replace (i - 1 -k) with (i - k - 1) by lia. done.
        * unfold unlift, isup_notin.
          rewrite on_free_vars_rename.
          eapply on_free_vars_impl2; [ | apply rc_notin_t | apply isup_notin_t  ].
          intros j. destruct k; cbn.
          ** unfold shiftnPneg. destruct j => //=. intros _. unfold shiftnP => //=.
            repeat case_inequalities => //=. intros X; apply_eq X. f_equal. lia.
          ** intros _. unfold shiftnP, unlift_renaming.
            repeat (case_inequalities => //=). intros X; apply_eq X; f_equal; lia.
      - len; cbn. intros k t rc_notin_t.
        rewrite rc_notin_lax_true in rc_notin_t => //.
        rewrite -> (unlift_lift 1 k t).
        2: {
          eapply on_free_vars_impl; only 2: apply rc_notin_t.
          eapply shiftnP_impl. unfold shiftnPneg.
          intros i; destruct i; done.
        }
        rewrite shiftn_strengthen.
        eapply rename_rename_no_rc_r.
        unfold rc_notin, unlift, rc_notin_bool.
        rewrite on_free_vars_rename.
        unfold shiftnPneg in rc_notin_t. unfold unlift_renaming.
        eapply on_free_vars_impl; only 2 : apply rc_notin_t.
        intros i. unfold shiftnP; cbn.
        repeat case_inequalities => //.
        replace (i - 1 -k) with (i - k - 1) by lia. done.
    (* branch false => arg is keept *)
    +
      eassert (all_false : All (fun arg0 : argument => check_lax arg0 = false) (acc.1.2 ++ [rename_argument acc.2 0 arg])).
        { apply All_app_inv => //. repeat constructor => //. rewrite argument_mapi_check_lax //. }
      repeat split => //=.
      - constructor => //.
        destruct arg; only 2-4: inversion lax_arg.
        cbn. repeat constructor => //=.
        1: {
              specialize (rc_notin_arg ltac:(done)).
              apply on_free_vars_argument_free in rc_notin_arg.
              assert (map check_lax acc.1.2 = repeat false #|acc.1.2|) as ->.
              { rewrite -map_xpred0. eapply All_map_eq. done. }
              eapply rc_notin_false. eapply pos_rename_no_rc with (P := xpredT). done.
              eapply on_free_vars_impl with (2 := rc_notin_arg).
              intros i _. rewrite shiftnP_xpredT //.
        }
        rewrite length_map. unfold isup_notin.
        replace (#|nup| + #|acc.1.2| + 0) with (#|acc.1.2| + 0 + #|nup|) by lia.
        rewrite -shiftnP_add. eapply pos_rename_no_rc.
        * apply on_free_vars_argument_free in rc_notin_arg => //.
        * inversion pos_arg. eapply on_free_vars_up_shift; tea. reflexivity.
          rewrite shiftnP_add.
          replace (#|acc.1.1| + 0 + #|nup|) with (#|nup| + #|map check_lax acc.1.1| + 0) by len.
          done.
      - len. intros P i t rc_notin_t isup_notin_t.
        rewrite shiftn_add.
        replace (#|acc.1.2| + 1 + i) with (#|acc.1.2| + (i + 1)) by lia.
        eapply pos_rename_no_rc.
        * rewrite -(rc_notin_lax_false _ arg) //.
        * eapply on_free_vars_up_shift; tea; lia.
      - intros k t rc_notin_t. eapply (@All_repeat _ _ check_lax) in all_false.
        unfold rc_notin. rewrite all_false. len. eapply rc_notin_false.
        rewrite shiftn_add. eapply rename_rename_no_rc_r.
        revert rc_notin_t. rewrite rc_notin_lax_false => //.
  Qed.

  Definition pos_remove_rc (Γ : list argument) :
    All_telescope (fun Γ => PosArg nb_block up nup Γ) Γ ->
    StrPosAcc (fold_left remove_rc_one Γ ( @nil argument, @nil argument, (fun n => n))).
  Proof.
    intros H.
    eapply spec_fold_All_check2 with (check := check_lax) (PX := PosArgBool _ _ _) (PAcc := StrPosAcc); cbn.
    + apply All_telescope_to_All_check. tea.
    + repeat split; try constructor; cbn.
      - intros. rewrite shiftn_id rename_ren_id. done.
      - intros. rewrite shiftn_id rename_ren_id. done.
    + intros [[oargs nargs] f] arg. unfold remove_rc_one.
      destruct (check_lax arg); cbn. all:done.
    + intros. apply pos_remove_rc_one; done.
  Qed.

  Definition remove_rc_id_oargs Γ acc :
    (fold_left remove_rc_one Γ acc).1.1 = acc.1.1 ++ Γ.
  Proof.
    revert acc. induction Γ; cbn.
    + intros; rewrite app_nil_r //.
    + intros.
      replace (acc.1.1 ++ a :: Γ) with ((acc.1.1 ++ [a]) ++ Γ) by rewrite -?app_assoc //=.
      unfold remove_rc_one. destruct (check_lax a); cbn; fold remove_rc_one.
      all : rewrite IHΓ //; cbn.
  Qed.

  Definition remove_rc_nargs Γ : list argument :=
    (fold_left remove_rc_one Γ ( @nil argument, @nil argument , (fun n => n))).1.2.

  Definition remove_rc_rename Γ : nat -> nat :=
    (fold_left remove_rc_one Γ ( @nil argument, @nil argument , (fun n => n))).2.

  (* properties *)
  Definition length_remove_rc Γ acc :
    #|filter (fun t => ~~ check_lax t) Γ| + #|acc.1.2| =
    #|(fold_left remove_rc_one Γ acc).1.2|.
  Proof.
    clear. revert acc.
    unfold remove_rc_one.
    induction Γ as [|a Γ IHΓ]; cbn => //.
    intros [args f]. destruct (check_lax a) => //.
    all: rewrite -IHΓ => //=.
  Qed.

End StrengthArg.

Definition rename f above : term -> term := rename (shiftn above f).









(* *** Nested to Mutual *** *)
Section NestedToMutualInd.

  (* 1. ### Info Nesting ### *)

  (* Information Global Inductive Type *)
  Context (nb_g_block : nat).

  Context (g_uparams_b  : list (context_decl * bool)).
  Notation nb_g_uparams := #|g_uparams_b|.
  Definition g_uparams := map fst g_uparams_b.

  Context (g_nuparams : context).
  Notation nb_g_nuparams := #|g_nuparams|.

  (* Context of the nesting *)
  (* arguments already seen *)
  Context (g_args : list argument).
  Notation nb_g_args := #|g_args|.
  Context (pos_g_args :
    All_telescope (fun Γ arg =>
      (~~ check_lax arg -> rc_notin_argument Γ 0 arg) *
      positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax Γ) true 0 arg
    )
  g_args).

  (* Argument to the left of nesting  *)
  Context (g_largs : list term).
  Notation nb_g_largs := #|g_largs|.

  Context (isup_notin_g_largs : Alli (isup_notin g_uparams_b) (nb_g_nuparams + nb_g_args) g_largs).
  Context (rc_notin_g_largs : Alli (rc_notin g_args) 0 g_largs).

  (* Information about the inductive type used for nesting *)
  Context (nb_l_block : nat).
  Notation nb_m_block := (nb_g_block + nb_l_block).

  Context (l_uparams_b : list (context_decl * bool)).
  Notation nb_l_uparams  := #|l_uparams_b|.

  Context (l_nuparams : context).
  Notation nb_l_nuparams := #|l_nuparams|.
  Context (pos_l_nuparams : Alli (isup_notin l_uparams_b) 0 (terms_of_cxt l_nuparams)).

  (* Instantiation Nesting *)
  Notation nb_old_cxt_sub := (nb_g_nuparams + nb_g_args + nb_g_largs).

  Context (inst_uparams_a : list (list term * argument)).
  Context (spec_inst_uparams_a :
      All2 (fun x y  =>
          let llargs := x.1 in let arg := x.2 in
          let cdecl  := y.1 in let pos := y.2 in
        (* fully applied ensured by typing*)
          (#|llargs| = cdecl_to_arity cdecl)
          (* llargs are free *)
        * Alli (isup_notin g_uparams_b) nb_old_cxt_sub llargs
          (* args are pos lax or strict depending if you can nest or not *)
        * positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args) pos (nb_g_largs + #|llargs|) arg
    ) inst_uparams_a (List.rev l_uparams_b)).

  Context (rc_notin_inst_llargs_args : All (fun p => Alli (rc_notin g_args) nb_g_largs p.1
              * (rc_notin_argument g_args (nb_g_largs + #|p.1|) p.2)) inst_uparams_a).


  (* ### 2. Spec Not Strength ### *)
  Definition size_inst_uparams : #|inst_uparams_a| = nb_l_uparams.
  Proof.
    len.
    rewrite -(List.length_rev (l_uparams_b)).
    eapply All2_length; tea.
  Qed.

  (* !!! rev to remove at a point => probably keep reversing eq *)
  Definition fapp_inst_uparams_a : All2 (fun n x => n = #|x.1|)
      (List.rev (uparams_nb_args l_uparams_b)) inst_uparams_a.
  Proof.
    rewrite -List.map_rev -(map_id inst_uparams_a).
    eapply All2_map. eapply All_sym_inv.
    eapply All2_impl; only 1 : apply spec_inst_uparams_a.
    intros [llargs arg] [cdecl pos]; cbn.
    intros [[]] => //.
  Qed.

  Definition isup_notin_llargs :
    All (fun p => Alli (isup_notin g_uparams_b) nb_old_cxt_sub p.1)
        inst_uparams_a.
  Proof.
    clear rc_notin_inst_llargs_args.
    induction spec_inst_uparams_a; cbn in spec_inst_uparams_a; constructor.
    inversion spec_inst_uparams_a. subst.
    destruct x as [llargs arg], y as [cdecl pos], r as [[fapp pos_llargs] pos_arg]; cbn in * => //.
    apply IHa. assumption.
  Qed.

  Definition positive_true_all :
    All (fun x => positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args)
                      true (nb_g_largs + #|x.1|) x.2) inst_uparams_a.
  Proof.
    clear rc_notin_inst_llargs_args.
    induction spec_inst_uparams_a; constructor; cbn; eauto.
    destruct x as [llargs arg], y as [cdecl pos], r as [[fapp ?] pos_arg]; cbn in *.
    destruct pos => //. apply positive_argument_increase2 => //.
  Qed.

  Definition inst_to_term_old : (list term * argument) -> term :=
  fun '(llargs, arg) =>
    (it_tLambda llargs (argument_to_term nb_g_block g_uparams_b (nb_old_cxt_sub + #|llargs|) arg)).

  Definition pos_inst_to_term_old :
    All2 (fun x y =>
        y.2 = false -> isup_notin g_uparams_b (nb_old_cxt_sub) (inst_to_term_old x)
    ) inst_uparams_a (List.rev l_uparams_b).
  Proof.
    eapply All2_impl ; [exact spec_inst_uparams_a|].
    intros [llargs arg] [cdecl pos] [[fapp_llargs isup_notin_llargs] pos_arg]; cbn in *.
    destruct pos. 1: intros x; inversion x.
    intros _. unfold inst_to_term_old.
    apply on_free_vars_tLambda => //.
    destruct (positive_argument_strict pos_arg) as [t [_ ->]]; cbn.
    inversion pos_arg => //. eapply on_free_vars_up_shift; tea. done.
  Qed.

  Definition inst_uparams : nat -> term :=
    fun n => nth n (map inst_to_term_old inst_uparams_a) (tRel n).

  Definition pos_inst_uparams : forall n,
    isup_notinP l_uparams_b n ->
    isup_notin g_uparams_b nb_old_cxt_sub (inst_uparams n).
  Proof.
    intros n. unfold isup_notinP, andP, ind_notinP, sp_uparams_notinP.
    intros x%andb_prop; destruct x as [notInd notSpUparams].
    destruct (Nat.leb_spec nb_l_uparams n) as [nleb | nlt] => //.
    unfold inst_uparams.
    rewrite negb_true_iff in notSpUparams. revert notSpUparams.
    apply (All2_nth (fun x y => y.2 = false -> isup_notin g_uparams_b nb_old_cxt_sub x)).
    1: len; rewrite size_inst_uparams //.
    apply All2_map_left. apply pos_inst_to_term_old.
  Qed.

  Definition inst_preserve_isup_notin (k m : nat) t :
    m = nb_old_cxt_sub + k ->
    isup_notin l_uparams_b k t ->
    isup_notin g_uparams_b m t.[up k inst_uparams].
  Proof.
    intros ->; rewrite Nat.add_comm. apply on_free_vars_inst.
    intros n. rewrite <- shiftnP_add. apply on_free_vars_up.
    apply pos_inst_uparams.
  Qed.

  Definition All_inst_isup_notin k m l :
  m = nb_old_cxt_sub + k ->
  All (isup_notin l_uparams_b k) l ->
  All (isup_notin g_uparams_b m) (map (fun t => t.[up k inst_uparams]) l).
  Proof.
    intros ->; intros H; apply All_map, (All_impl H).
    intros; apply inst_preserve_isup_notin => //.
  Qed.

  Definition Alli_inst_isup_notin l k m :
  m = (nb_old_cxt_sub + k) ->
  Alli (isup_notin l_uparams_b) k l ->
  Alli (isup_notin g_uparams_b) m
          (mapi_rec (fun i t => t.[up i inst_uparams]) l k).
  Proof.
    intros ->. intros X; eapply Alli_mapi_rec; tea; cbn.
    intros. apply inst_preserve_isup_notin => //.
  Qed.


  (* 3. ### Strengthen args + rename ### *)

  (* New args + Spec *)
  Definition g_args_no_rc : list argument :=
    remove_rc_nargs g_args.

  Definition pos_g_args_no_rc :
    All_telescope (fun Γ => positive_argument nb_g_block g_uparams_b g_nuparams
      (map check_lax Γ) false 0) g_args_no_rc.
  Proof.
    destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[[lax_false pos_nargs] pos_rename] _].
    intros. unfold g_args_no_rc, remove_rc_nargs.
    eapply (All_telescope_impl2 pos_nargs). eapply (All_to_All_telescope _ _ lax_false).
    intros ? ? [] lax_arg. destruct p; inversion lax_arg.
    constructor => //.
  Qed.

  Definition g_args_no_rc_check_lax :
    All (fun arg => check_lax arg = false) g_args_no_rc.
  Proof.
    destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[[lax_false pos_nargs] pos_rename] _].
    done.
  Qed.

  Definition g_args_no_rc_check_lax2 :
    map check_lax g_args_no_rc = repeat false #|g_args_no_rc|.
  Proof.
    induction g_args_no_rc_check_lax; cbn; f_equal; eauto.
  Qed.


  Definition g_args_no_rc_false :
    Alli (fun i => positive_argument nb_g_block g_uparams_b g_nuparams
      (repeat false i) false 0) 0 g_args_no_rc.
  Proof.
    induction pos_g_args_no_rc. constructor.
    eapply Alli_app_inv; eauto. repeat constructor.
    eapply positive_argument_decrease1; tea.
    clear. induction Γ; constructor; eauto.
  Qed.

  Definition length_g_args_no_rc :
    #|filter (fun t => ~~ check_lax t) g_args| = #|g_args_no_rc|.
  Proof.
    unfold g_args_no_rc. rewrite -length_remove_rc; cbn. len; done.
  Qed.

  Notation nb_g_args_no_rc := (#|g_args_no_rc|).
  Notation nb_new_cxt_sub := (nb_g_nuparams + nb_g_args_no_rc + nb_g_largs).

  (* New renaming + Spec *)
  Definition rename_no_rc : nat -> nat := remove_rc_rename g_args.

  Definition on_free_vars_rename_no_rc P i t :
    (rc_notin g_args) i t ->
    on_free_vars (shiftnP (nb_g_args + i) P)  t ->
    on_free_vars (shiftnP (nb_g_args_no_rc + i) P) (rename rename_no_rc i t).
  Proof.
    destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[[pos_oargs pos_nargs] pos_rename] _].
    cbn in pos_rename. intros. apply pos_rename => //.
    all: rewrite remove_rc_id_oargs; cbn => //.
  Qed.

  Definition add_custom_shuffle_4 a b c d : a + b + (c + d) = (c + (d + b)) + a.
    lia.
  Qed.

  Definition add_custom_shuffle_5 a b c d e : a + b + c + (d + e) = (d + (e + b + c)) + a.
    lia.
  Qed.

  Ltac ofva_rnorc_aux := try solve [
      eapply Alli_mapi2; mtea; cbn; intros;
      rewrite shiftnP_add add_custom_shuffle_4 -shiftnP_add; eapply on_free_vars_rename_no_rc => //;
      eapply on_free_vars_impl; tea; intros ?; rewrite !shiftnP_add; intros LL; apply_eq LL => //
    | eapply All_map, All_impl2; mtea; cbn; intros;
      rewrite shiftnP_add add_custom_shuffle_4 -shiftnP_add; eapply on_free_vars_rename_no_rc => //;
      eapply on_free_vars_impl; tea; intros ?; rewrite !shiftnP_add; intros LL; apply_eq LL => //
    | rewrite shiftnP_add Nat.add_comm -shiftnP_add;
      eapply on_free_vars_rename_no_rc => //;
      rewrite shiftnP_add Nat.add_comm -shiftnP_add //
  ].

  Definition on_free_vars_argument_rename_no_rc P i arg k :
    (rc_notin_argument g_args) i arg ->
    on_free_vars_argument (shiftnP (nb_g_args + i) P) k arg ->
    on_free_vars_argument (shiftnP (nb_g_args_no_rc + i) P) k (rename_argument rename_no_rc i arg).
  Proof.
    unfold rc_notin_argument. unfold rc_notin_argument_bool.
    intros X. revert k.
    induction X using on_free_vars_argument_rect'; intros n Y; inversion Y; subst; constructor; len => //.
    all: ofva_rnorc_aux.
    all: fold argument_mapi.
    induction IHuparams; cbn; constructor; inversion X0; subst; eauto => //=; len; eauto.
    + destruct px as [K L], X2 as [U V]. split => //=; ofva_rnorc_aux.
      - eapply (Alli_mapi2 K U); cbn; intros.
        rewrite shiftnP_add add_custom_shuffle_5 -shiftnP_add; eapply on_free_vars_rename_no_rc => //;
        eapply on_free_vars_impl; tea; intros ?; rewrite !shiftnP_add; intros LL; apply_eq LL => //.
      - destruct x; cbn in *.
        change (argument_mapi (fun n0 : nat => PCUICSigmaCalculus.rename (shiftn n0 rename_no_rc))) with (rename_argument rename_no_rc).
        eapply on_free_vars_argument_impl_shiftnP. 1: apply h with (k := n) => //.
        * eapply on_free_vars_argument_impl_shiftnP; tea.
          intros i. erewrite !shiftnP_add. intros LL; eapply_eq LL. f_equal => //.
        * intros i. erewrite !shiftnP_add. intros LL; eapply_eq LL. f_equal => //.
      + eapply IHIHuparams => //. constructor => //.
  Qed.


  (* should follow *)
  Definition pos_rename_no_rc i t :
    (rc_notin g_args) i t ->
    isup_notin g_uparams_b (nb_g_nuparams + nb_g_args + i) t ->
    isup_notin g_uparams_b (nb_g_nuparams + nb_g_args_no_rc + i)
                                      (rename rename_no_rc i t).
  Proof.
    intros. unfold isup_notin.
    replace (nb_g_nuparams + nb_g_args_no_rc + i) with ((nb_g_args_no_rc + i) + nb_g_nuparams) by lia.
    rewrite -shiftnP_add. apply on_free_vars_rename_no_rc => //. rewrite shiftnP_add.
    replace ((nb_g_args + i) + nb_g_nuparams) with (nb_g_nuparams + nb_g_args + i) by lia.
    done.
  Qed.

  Definition rename_rename_no_rc i t :
    rc_notin g_args i t -> rc_notin g_args_no_rc i (rename rename_no_rc i t).
  Proof.
    destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[[pos_oargs pos_nargs] pos_rename] rename_nrc].
    intros X. eapply rename_nrc. rewrite remove_rc_id_oargs; cbn => //.
  Qed.

  Ltac rename_rename_arg_no_rc_aux := try solve [
        eapply Alli_mapi; mtea; cbn; intros; eapply rename_rename_no_rc; done
      | eapply All_map, All_impl; mtea; cbn; intros; eapply rename_rename_no_rc; done
      | eapply rename_rename_no_rc => //
    ].

  Definition rename_rename_arg_no_rc i arg :
    rc_notin_argument g_args i arg ->
    rc_notin_argument g_args_no_rc i (rename_argument rename_no_rc i arg).
  Proof.
    intros X; induction X using on_free_vars_argument_rect'; constructor; eauto; len.
    all: rename_rename_arg_no_rc_aux.
    fold argument_mapi. induction IHuparams; len; constructor; eauto => //=.
    destruct px. split => //=; rename_rename_arg_no_rc_aux.
  Qed.

  Definition isup_impl {up n m t} : n = m -> isup_notin up n t -> isup_notin up m t.
  Proof.
    intros -> => //.
  Qed.

  Definition par4 a b c d : a + b + c + d = a + b + (c + d).
  Proof. lia. Qed.

  Definition par5 a b c d e : a + b + c + d + e = a + b + (c + d + e).
  Proof. lia. Qed.

  Ltac pos_rnorc_aux := try solve [
      eapply Alli_mapi2; mtea; cbn; intros ? ?; len; rewrite !par4;
      intros; eapply pos_rename_no_rc => //; done
    | eapply All_map, All_impl2; mtea; cbn; intros ? ?; len; rewrite !par4;
      intros; eapply pos_rename_no_rc => //; done
    | eapply Alli_mapi; mtea; cbn; intros; eapply rename_rename_no_rc => //
    | eapply All_map, All_impl2; mtea; intros; eapply rename_rename_no_rc => //
    | eapply pos_rename_no_rc => //; eapply isup_impl; tea; len
  ].

  Definition pos_rename_no_rc_arg lax i arg :
    rc_notin_argument g_args i arg ->
    positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args) lax i arg ->
    positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args_no_rc) lax i
                                      (rename_argument rename_no_rc i arg).
  Proof.
    unfold rc_notin_argument. unfold rc_notin_argument_bool.
    intros X; induction X using on_free_vars_argument_rect'; intros Y; inversion Y; subst; econstructor => //; len.
    all: pos_rnorc_aux.
    all: fold argument_mapi.
    + clear Y. cbn in *. revert X1. generalize (List.rev (ind_uparams mdecl)).
      induction IHuparams; intros l' X1; inversion X1; subst; constructor; eauto; len.
      destruct px as [K L], X4 as [[fapp pos_llargs] pos_inst]; repeat split => //=; pos_rnorc_aux.
      - eapply (Alli_mapi2 K pos_llargs). len. intros.
        rewrite par5. eapply pos_rename_no_rc => //. eapply isup_impl; tea; done.
      - change (argument_mapi (fun n : nat => PCUICSigmaCalculus.rename (shiftn n rename_no_rc)))
        with (rename_argument rename_no_rc).
        destruct y.2.
        * apply h. done.
        * apply positive_argument_strict in pos_inst as (t & isup_t & Harg).
            rewrite -> Harg in *.
            cbn. constructor. len. eapply pos_rename_no_rc => //.
            rewrite <- Harg in *.
            ** rewrite Harg in L. inversion L; subst. done.
            ** rewrite -par5. eapply isup_impl; tea; done.
      + clear Y X1.
        cbn in *. induction IHuparams; inversion X3; subst; constructor; eauto; len; fold map.
        destruct px as [K L]; split => //=; pos_rnorc_aux. eapply rename_rename_arg_no_rc => //.
  Qed.

  (* 4. Update instantiation and properties *)
  Definition g_largs_no_rc : list term :=
    mapi (rename rename_no_rc) g_largs.

  Definition isup_notin_g_largs_no_rc :
    Alli (isup_notin g_uparams_b) (nb_g_nuparams + nb_g_args_no_rc) g_largs_no_rc.
  Proof.
    eapply (Alli_mapi2 rc_notin_g_largs isup_notin_g_largs); cbn.
    apply pos_rename_no_rc.
  Qed.

  Definition l_inst_uparams_no_rc : list (list term * argument) :=
    map (fun ' (llargs, arg) =>
      let llargs' := mapi (fun i => rename rename_no_rc (nb_g_largs + i)) llargs in
      let arg' := rename_argument rename_no_rc (nb_g_largs + #|llargs|) arg in
      (llargs', arg')
      )
    inst_uparams_a.

  Definition wd_l_inst_uparams_no_rc :
    All (fun p =>
        Alli (fun=> (fun t0 => on_free_vars xpredT t0)) 0 p.1
      * on_free_vars_argument xpredT (nb_g_largs + #|p.1|) p.2
      ) l_inst_uparams_no_rc.
  Proof.
    unfold l_inst_uparams_no_rc. eapply All_map.
    eapply (All_impl rc_notin_inst_llargs_args).
    intros [llargs arg] [rc_notin_llargs rc_notin_arg]; cbn in *. split.
    + eapply (Alli_mapi rc_notin_llargs). intros.
      erewrite <- shiftnP_xpredT. eapply on_free_vars_rename_no_rc => //.
      rewrite shiftnP_xpredT => //. eapply on_free_vars_any_xpredT; tea.
    + eapply on_free_vars_argument_impl with (P := shiftnP _ xpredT).
      2: done. eapply on_free_vars_argument_rename_no_rc => //.
      eapply on_free_vars_argument_impl => //.
      intros. rewrite shiftnP_xpredT => //.
  Qed.

  Definition size_l_inst_uparams_no_rc : #|l_inst_uparams_no_rc| = nb_l_uparams.
  Proof.
    len. rewrite -(List.length_rev (l_uparams_b)). eapply All2_length; tea.
  Qed.

  Definition fapp_l_inst_uparams_no_rc : All2 (fun n x => n = #|x.1|)
      (List.rev (uparams_nb_args l_uparams_b)) l_inst_uparams_no_rc.
  Proof.
    rewrite -List.map_rev -(map_id l_inst_uparams_no_rc).
    eapply All2_map. eapply All_sym_inv.
    apply All2_map_left.
    eapply All2_impl; only 1 : apply spec_inst_uparams_a.
    intros [llargs arg] [cdecl pos]; cbn.
    intros [[]] => //.
  Qed.

  Definition isup_notin_llargs_no_rc :
    All (fun p => Alli (isup_notin g_uparams_b) nb_new_cxt_sub p.1)
        l_inst_uparams_no_rc.
  Proof.
    unfold l_inst_uparams_no_rc.
    eapply All_map, (All_impl2 isup_notin_llargs rc_notin_inst_llargs_args).
    intros [llargs arg]; cbn. intros X [Y _].
    eapply (Alli_mapi2 X Y).
    intros. eapply on_free_vars_up_shift.
    2: { apply pos_rename_no_rc => //. eapply on_free_vars_up_shift; tea. done. }
    lia.
  Qed.

  Definition positive_true_all_no_rc :
    All (fun x => positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args_no_rc)
                      true (nb_g_largs + #|x.1|) x.2) l_inst_uparams_no_rc.
  Proof.
    unfold l_inst_uparams_no_rc.
    eapply All_map. eapply (All_impl2 rc_notin_inst_llargs_args positive_true_all).
    intros [llargs arg]; len; cbn. intros [_ ?] ?.
    apply pos_rename_no_rc_arg => //.
  Qed.


  (* 5. instantiation *)

  (* should not have renaming as applied to inst_uparams_no_rc *)
  Definition inst_to_term_no_rc : (list term * argument) -> term :=
    fun '(llargs, arg) =>
      (it_tLambda llargs (argument_to_term nb_g_block g_uparams_b (nb_new_cxt_sub + #|llargs|) arg)).

  Definition pos_inst_to_term :
    All2 (fun x y =>
        y.2 = false -> isup_notin g_uparams_b (nb_new_cxt_sub) (inst_to_term_no_rc x)
    ) l_inst_uparams_no_rc (List.rev l_uparams_b).
  Proof.
    unfold l_inst_uparams_no_rc.
    eapply All2_map_left. eapply All2_impl2.
    + apply spec_inst_uparams_a.
    + apply All2_left_triv. 2: rewrite size_inst_uparams //.
      apply rc_notin_inst_llargs_args.
    + intros [llargs arg] [cdecl pos] [[fapp_llargs isup_notin_llargs] pos_arg]
        [rc_notin_llargs rc_notin_arg] pos_lax. cbn in *. len.
      apply on_free_vars_tLambda => //.
      - eapply (Alli_mapi2 isup_notin_llargs rc_notin_llargs); cbn. intros.
        eapply on_free_vars_up_shift; only 2: apply pos_rename_no_rc => //. lia.
        eapply on_free_vars_up_shift; tea. len.
      - rewrite pos_lax in pos_arg.
        destruct (positive_argument_strict pos_arg) as [t [notin_t ->]]; cbn.
        len. eapply on_free_vars_up_shift; only 2: apply pos_rename_no_rc; move => //.
      * apply on_free_vars_argument_free in rc_notin_arg => //.
      * eapply on_free_vars_up_shift ; tea; len.
  Qed.

  Definition inst_uparams_no_rc : nat -> term :=
    fun n => nth n (map inst_to_term_no_rc l_inst_uparams_no_rc) (tRel n).

  (* check that if n uparams is not positive
     then the instantiation does not contain the variable
  *)
  Definition pos_inst_uparams_no_rc : forall n,
    isup_notinP l_uparams_b n ->
    isup_notin g_uparams_b nb_new_cxt_sub (inst_uparams_no_rc n).
  Proof.
    intros n. unfold isup_notinP, andP, ind_notinP, sp_uparams_notinP.
    intros x%andb_prop; destruct x as [notInd notSpUparams].
    destruct (Nat.leb_spec nb_l_uparams n) => //.
    unfold inst_uparams_no_rc.
    rewrite negb_true_iff in notSpUparams. revert notSpUparams.
    apply (All2_nth (fun x y => y.2 = false -> isup_notin g_uparams_b nb_new_cxt_sub x)).
    1: len; rewrite size_inst_uparams //.
    apply All2_map_left. apply pos_inst_to_term.
  Qed.

  Definition inst_no_rc_preserve_isup_notin (k m : nat) t :
    m = nb_new_cxt_sub + k ->
    isup_notin l_uparams_b k t ->
    isup_notin g_uparams_b m t.[up k inst_uparams_no_rc].
  Proof.
    intros ->; rewrite Nat.add_comm. apply on_free_vars_inst.
    intros n. rewrite <- shiftnP_add. apply on_free_vars_up.
    apply pos_inst_uparams_no_rc.
  Qed.

  Definition All_inst_no_rc_isup_notin k m l :
  m = nb_new_cxt_sub + k ->
  All (isup_notin l_uparams_b k) l ->
  All (isup_notin g_uparams_b m) (map (fun t => t.[up k inst_uparams_no_rc]) l).
  Proof.
    intros ->; intros H; apply All_map, (All_impl H).
    intros; apply inst_no_rc_preserve_isup_notin => //.
  Qed.

  Definition Alli_inst_no_rc_isup_notin l k m :
  m = (nb_new_cxt_sub + k) ->
  Alli (isup_notin l_uparams_b) k l ->
  Alli (isup_notin g_uparams_b) m
          (mapi_rec (fun i t => t.[up i inst_uparams_no_rc]) l k).
  Proof.
    intros ->. intros X; eapply Alli_mapi_rec => //.
    intros. apply inst_no_rc_preserve_isup_notin => //.
  Qed.

  Definition wd_inst_uparams_no_rc : forall i, on_free_vars xpredT (inst_uparams_no_rc i).
  Proof.
    intros i. unfold inst_uparams_no_rc.
    destruct (Nat.ltb_spec i #|(map inst_to_term_no_rc l_inst_uparams_no_rc)|).
    2: { rewrite nth_overflow; tea. done. }
    apply All_nth; tea.
    eapply All_map, (All_impl2 positive_true_all_no_rc wd_l_inst_uparams_no_rc).
    intros [llargs arg] pos_arg [wd_llargs wd_arg]; cbn in *.
    rewrite -(shiftnP_xpredT 0).
    eapply on_free_vars_tLambda.
    + eapply (Alli_impl wd_llargs). intros; rewrite shiftnP_xpredT; done.
    + clear -wd_arg.
      eapply (on_free_vars_argument_xpredT _ #|llargs|) in wd_arg.
      induction wd_arg using on_free_vars_argument_rect'; cbn => //.
      - apply on_free_vars_tProd, on_free_vars_mkApps => //; cbn.
        rewrite shiftnP_xpredT => //.
      - apply on_free_vars_tProd, on_free_vars_mkApps => //; cbn.
        * unfold tRels. apply All_app_inv => //.
          apply All_rev_pointwise_map => //.
          intros. rewrite shiftnP_xpredT => //.
        * rewrite shiftnP_xpredT => //.
      - apply on_free_vars_tProd, on_free_vars_mkApps => //.
        apply All_app_inv => //.
        induction IHuparams ; constructor. 2:apply IHIHuparams => //.
        destruct x as [llargs0 arg0], px as [ofr_llargs0 ofr_arg0].
        eapply on_free_vars_tLambda => //.
        cbn in h. apply_eq h. f_equal. f_equal. lia.
  Qed.





  (* ******************* END LEMMA ******************* *)






  (* New indices are ↓↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams ,,, indices) + positivity *)
  Definition new_indices indices : context :=
    arguments_to_context nb_g_block g_uparams_b (nb_g_uparams + nb_g_nuparams) g_args_no_rc ,,,
    cxt_of_terms g_largs_no_rc ,,,
    List.rev ( mapi (fun i cdecl =>
              let f := inst (up i inst_uparams_no_rc) in
              mkdecl cdecl.(decl_name) (option_map f cdecl.(decl_body))
                  (f cdecl.(decl_type))) (List.rev (l_nuparams ,,, indices))
      ).

  Definition pos_new_indices indices :
    positive_indices l_uparams_b l_nuparams indices ->
    positive_indices g_uparams_b g_nuparams (new_indices indices).
  Proof.
    unfold positive_indices. intros pos_indices.
    unfold new_indices. rewrite !rev_app_distr ?map_app.
      repeat apply Alli_app_inv; len.
      - unfold arguments_to_context.
        rewrite rev_involutive -(map_mapi _ _ vassAR) map_map /= map_id.
        eapply (Alli_mapi g_args_no_rc_false). intros i x pos_arg.
        destruct (positive_argument_strict pos_arg) as [t [notin_t ->]]; cbn.
        len in notin_t.
      - unfold cxt_of_terms.
        rewrite List.rev_involutive map_map /= map_id.
        eapply (Alli_impl isup_notin_g_largs_no_rc) => //.
      - rewrite rev_involutive map_mapi -(mapi_map (fun i t => t.[up i inst_uparams_no_rc])) map_app mapi_app.
        eapply Alli_app_inv; len.
        * apply Alli_inst_no_rc_isup_notin => //.
        * eapply (Alli_mapi pos_indices). intros.
          eapply inst_no_rc_preserve_isup_notin => //.
  Qed.



  (* Extra Arguments: g_args ,,, g_largs ,,,  σ(l_nuparams) + Positivity *)
  Definition cstr_extra_args : list argument :=
       g_args_no_rc
    ++ map arg_is_free g_largs_no_rc
    ++ map arg_is_free (mapi_rec (fun i t => t.[up i inst_uparams_no_rc])
        (terms_of_cxt l_nuparams) 0).

  Definition cstr_extra_args_lax_false :
    map check_lax cstr_extra_args = repeat false #|cstr_extra_args|.
  Proof.
    unfold cstr_extra_args; len.
    rewrite !repeat_app !map_app !map_map !map_xpred0 !app_assoc; cbn.
    len; repeat f_equal => //.
    rewrite -map_xpred0.
    eapply All_map_eq. eapply g_args_no_rc_check_lax.
  Qed.

  Definition wd_cstr_extra_args :
    All (on_free_vars_argument xpredT 0) cstr_extra_args.
  Proof.
    unfold cstr_extra_args. repeat apply All_app_inv.
    - destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[[lax_false pos_nargs] pos_rename] _].
      change ((fold_left remove_rc_one g_args ([], [], id)).1.2) with g_args_no_rc in lax_false, pos_nargs.
      apply All_to_All_telescope in lax_false.
      induction pos_nargs; only 1 : constructor.
      inversion lax_false.
      1: apply (f_equal ( @length argument)) in H0; len in H0.
      apply app_inj_tail in H as []; subst.
      apply All_app_inv => //. 1: apply IHpos_nargs => //.
      repeat constructor.
      destruct p as [LL ?]. eapply on_free_vars_argument_impl.
      { eapply LL. hnf. apply negb_true_iff. done. }
      done.
    - apply All_map. unfold g_largs_no_rc.
      eapply All_impl.
      2: { intros a b. constructor. exact b. }
      eapply @Alli_All with (n := 0). 2: exact (fun a b c => c).
      eapply (Alli_mapi2 isup_notin_g_largs rc_notin_g_largs). intros.
      rewrite shiftnP_xpredT.
      rewrite <- shiftnP_xpredT. apply on_free_vars_rename_no_rc => //.
      rewrite shiftnP_xpredT. eapply on_free_vars_impl => //.
    - apply All_map.
      eapply All_impl; only 2: (intros a b; constructor; exact b).
      eapply @Alli_All with (n := 0); only 2: exact (fun a b c => c).
      eapply (Alli_mapi pos_l_nuparams).
      intros. eapply on_free_vars_inst => //.
      intros. rewrite shiftnP_xpredT. erewrite <- shiftnP_xpredT. eapply on_free_vars_up with (Q := xpredT).
      2: by rewrite shiftnP_xpredT. intros; eapply wd_inst_uparams_no_rc.
  Qed.

  Definition rc_notin_cstr_exta_args :
    All_telescope (fun Γ arg => ~~ check_lax arg -> rc_notin_argument_bool (map check_lax Γ) 0 arg)
    cstr_extra_args.
  Proof.
    eapply All_telescope_rc_notin_lax_false.
    + apply cstr_extra_args_lax_false.
    + apply wd_cstr_extra_args.
  Qed.

  Definition pos_cstr_extra_args :
    All_telescope (fun Γ => positive_argument nb_m_block g_uparams_b g_nuparams (map check_lax Γ) false 0) cstr_extra_args.
  Proof.
    eapply All_telescope_impl; only 2: (intros ? ? X; apply pos_arg_inc; exact X).
    unfold cstr_extra_args.
    repeat apply All_telescope_app_inv; cbn.
    + eapply pos_g_args_no_rc.
    + eapply All_telescope_map.
      - intros ? ? X; apply pos_arg_is_free. len. rewrite Nat.add_assoc. exact X.
      - apply All_telescope_to_Alli with
              (P := (fun n (x : term) => isup_notin g_uparams_b n x))
              (n := nb_g_nuparams + nb_g_args_no_rc) => //.
        apply isup_notin_g_largs_no_rc.
    + eapply All_telescope_map.
      - intros ? ? X; apply pos_arg_is_free; len. rewrite !Nat.add_assoc. exact X.
      - apply All_telescope_to_Alli with
              (P := (fun n (x : term) => isup_notin g_uparams_b (n) x))
              (n := nb_new_cxt_sub).
        eapply (Alli_mapi pos_l_nuparams). cbn. intros. apply inst_no_rc_preserve_isup_notin => //.
  Qed.

  Definition PosArg_cstr_extra_args : All_telescope (PosArg nb_m_block g_uparams_b g_nuparams) cstr_extra_args.
  Proof.
    unfold PosArg, PosArgBool. apply All_telescope_prod.
    - apply rc_notin_cstr_exta_args.
    - eapply (All_telescope_impl pos_cstr_extra_args). intros ? ?.
      eapply positive_argument_increase2.
  Qed.





  (** Specialization of Arguments
      1. [sub_uparam] that given [forall largs, A_k args] substitute [A_k]
         for its instanciation [λ llargs, arg] that must be given already updated
      2. [specialize_argument] that specialize an argument, calling [sub_uparam]
         to substitute the strictly positive uniform parameters
  *)

  (* Substitute a strictly positive uniform parameter by its instantiation *)
  (* largs, args : already updated arg to sub [forall largs, A_k args]
     llargs, arg : instantiation [λ llargs, arg] to replace A_k,
                   already updated with largs in the context
  *)
  Definition sub_uparam (largs : list term) (args : list term) (llargs : list term) (arg : argument) : argument :=
    match arg with
    | arg_is_free t => arg_is_free (it_tProd largs (mkApps (it_tLambda llargs t) args))
    | arg_is_sp_uparam ll k x =>
        let ll' := mapi (fun i => subst (List.rev args) i) ll in
        let x' := map (subst (List.rev args) #|ll|) x in
        arg_is_sp_uparam (largs ++ ll') k x'
    | arg_is_ind ll pos_indb i_upi =>
        let ll' := mapi (fun i => subst (List.rev args) i) ll in
        let i_upi' := map (subst (List.rev args) #|ll|) i_upi in
        arg_is_ind (largs ++ ll') pos_indb i_upi'
    | arg_is_nested ll ind u inst_up inst_else =>
        let ll' := mapi (fun i => subst (List.rev args) i) ll in
        let inst_up'  := map (fun ' (llargs, arg) =>
            let llargs' := mapi (fun i => subst (List.rev args) (#|ll| + i)) llargs in
            let arg' := subst_argument (List.rev args) (#|ll| + #|llargs|) arg in
            (llargs', arg')
            ) inst_up
          in
        let inst_else' := map (subst (List.rev args) #|ll|) inst_else in
        arg_is_nested (largs ++ ll') ind u inst_up' inst_else'
    end.

  Tactic Notation "solve_sub_uparams_largs" :=
    ( eapply Alli_mapi; only 1: multi_eassumption;
      intros j x; eapply on_free_vars_subst_eq; only 3: (apply All_rev; mtea); done).

  Tactic Notation "solve_sub_uparams_args" :=
    ( eapply All_map, All_impl; only 1: multi_eassumption;
      intros x; eapply on_free_vars_subst_eq; only 3: (apply All_rev; mtea); done).

  Definition pos_sub_uparams Γ largs args (lax : bool) nb_binders (llargs : list term) (arg : argument)
    (* contet substitution *)
    (pos_largs : Alli (isup_notin g_uparams_b) (nb_g_nuparams + #|Γ| + nb_binders) largs)
    (pos_args  : All  (isup_notin g_uparams_b  (nb_g_nuparams + #|Γ| + nb_binders + #|largs|)) args)
    (* arg to substitute by *)
    (fapp_arg : #|llargs| = #|args|)
    (pos_llargs : Alli (isup_notin g_uparams_b) (nb_g_nuparams + #|Γ| + nb_binders + #|largs|) llargs)
    (pos_arg : positive_argument nb_m_block g_uparams_b g_nuparams Γ
                  lax (nb_binders + #|largs| + #|llargs|) arg)
    (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
    (rc_notin_largs : Alli (rc_notin_bool Γ) nb_binders largs)
    (rc_notin_args : All (rc_notin_bool Γ (nb_binders + #|largs|)) args)
    (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
    :
    positive_argument nb_m_block g_uparams_b g_nuparams Γ
      lax nb_binders (sub_uparam largs args llargs arg).
  Proof.
    remember (nb_binders + #|largs| + #|llargs|) as p eqn:Heqp.
    induction pos_arg using positive_argument_rect' in Heqp |- *; cbn.
    all: (ltac2:(nconstructor 4)); len => //; tea;
    try solve [apply Alli_app_inv; mtea; solve_sub_uparams_largs | solve_sub_uparams_args].
    + apply on_free_vars_tProd => //.
      apply on_free_vars_mkApps => //.
      eapply on_free_vars_tLambda_eq; tea. done.
    + clear rc_notin_instance.
      induction Ppos_nested; constructor. 2: apply IHPpos_nested.
      destruct x as [l_ll l_arg], y as [cdecl pos_arg], r as [[fapp pos_l_ll] pos_l_arg]; cbn in *.
      len; repeat split => //.
      - solve_sub_uparams_largs.
      - clear p al Ppos_nested isup_notin_instance IHPpos_nested.
        rewrite Heqp in pos_l_arg.
        eapply pos_subst_argument_eq; tea. 4-5: apply All_rev; tea.
        all:len.
    (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
    + eapply All_map. eapply (All_impl rc_notin_instance); cbn.
      intros [llargs0 arg0]. cbn. intros [rc_notin_llargs0 rc_notin_arg0]; cbn. split.
      * eapply (Alli_mapi rc_notin_llargs0). intros i t rc_notin_t.
        eapply on_free_vars_subst_eq; only 3: apply All_rev ; tea; done.
      * len. unfold rc_notin_argument_bool.
        eapply on_free_vars_argument_subst_eq; only 3: apply All_rev; tea; done.
    (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
  Qed.



  Definition err_arg : list term * argument
    := ([], arg_is_free (tVar "impossible case")).

  (* Specialize an argument
  1. If it is a strpos uparams => substite by its instantiation
  2. Otherwise propagate the instantiation

  pos sub_cxt : how deep after the sub_contxt => needed to lift the instantiation
    => l_nuparams (becomes arg) + Γ
  *)
  Fixpoint specialize_argument (pos_sub_cxt : nat) (arg : argument) : argument :=
    match arg with
    | arg_is_free t =>
        arg_is_free (t.[up pos_sub_cxt inst_uparams_no_rc])
    | arg_is_sp_uparam largs k args =>
        (* update largs and args of [forall largs, A_k args] to sub *)
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams_no_rc]) largs pos_sub_cxt in
        let args'  := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams_no_rc]) args in
        (* get and lift the instantiation *)
        let ' (llargs, arg_to_sub) := nth k l_inst_uparams_no_rc err_arg in
        let llargs := mapi (fun i => lift (pos_sub_cxt + #|largs|) i) llargs in
        let arg_to_sub := lift_argument (pos_sub_cxt + #|largs|) #|llargs| arg_to_sub in
        sub_uparam largs' args' llargs arg_to_sub
    | arg_is_ind largs i inst_uparams_no_rc_indices =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams_no_rc]) largs pos_sub_cxt in
        (* we need to add var for new nup + new indices - old_nup *)
        let new_indices := tRels (pos_sub_cxt + #|largs|) (nb_g_nuparams + nb_g_args_no_rc + #|g_largs|) in
        (* nup are now indices so just need to be updated *)
        let inst_uparams_no_rc_indices'  := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams_no_rc]) inst_uparams_no_rc_indices in
        arg_is_ind largs' (i + nb_g_block) (new_indices ++ inst_uparams_no_rc_indices')
    | arg_is_nested largs ind u insta_uparams inst_nuparams_indices =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams_no_rc]) largs pos_sub_cxt in
        let insta_uparams'  := map (fun ' (llargs, arg) =>
            let llargs' := mapi_rec (fun i t => t.[up i inst_uparams_no_rc]) llargs (pos_sub_cxt + #|largs|) in
            let arg' := specialize_argument (pos_sub_cxt + #|largs| + #|llargs|) arg in
            (llargs', arg')
            ) insta_uparams
          in
        let inst_nuparams_indices' := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams_no_rc]) inst_nuparams_indices in
        arg_is_nested largs' ind u insta_uparams' inst_nuparams_indices'
    end.

  (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
    Definition check_lax_specialize_argument Γ i:
      All2 (fun a b => is_true (~~ a) -> is_true (~~ b))
      (map check_lax Γ) (map check_lax (mapi_rec specialize_argument Γ i)).
    Proof.
      induction Γ in i |- *; cbn; constructor; eauto.
      destruct a; cbn. all: solve [done | intros [=]].
    Qed.

    Definition rc_notin_specialize_up Γ i nb_binders x n m :
      n = i + nb_binders ->
      m = i + (nb_l_nuparams + #|Γ| + nb_binders) ->
      rc_notin_bool (map check_lax Γ) (i + nb_binders) x ->
      rc_notin_bool (map check_lax (cstr_extra_args ++ mapi_rec specialize_argument Γ nb_l_nuparams))
        n x.[up m inst_uparams_no_rc].
    Proof.
      intros -> -> rc_notin_t.
      rewrite map_app cstr_extra_args_lax_false rc_notin_false_left; len.
      eapply (rc_notin_decrease (check_lax_specialize_argument Γ _)).
      eapply rc_notin_inst_up => //. eapply wd_inst_uparams_no_rc.
    Qed.

    Definition rc_notin_specialize_argument Γ nb_binders arg :
    (positive_argument nb_l_block l_uparams_b l_nuparams (map check_lax Γ) true nb_binders arg) ->
    (~~ check_lax arg -> rc_notin_argument Γ nb_binders arg) ->
      ~~ (check_lax (specialize_argument (nb_l_nuparams + #|Γ| + nb_binders) arg)) ->
      rc_notin_argument
        (cstr_extra_args ++ (mapi_rec specialize_argument Γ nb_l_nuparams))
        nb_binders (specialize_argument (nb_l_nuparams + #|Γ| + nb_binders) arg).
    Proof.
      unfold negb, specialize_argument. intros pos_arg H lax_spe_arg.
      destruct pos_arg => //=.
      2: destruct (nth k l_inst_uparams_no_rc) as [llargs []] eqn:Heqnth; cbn in * => //=.
      all: fold specialize_argument in *.
      all: constructor.
      (* all: cbn in H. apply on_free_vars_argument_free in H => //. *)
      all: unfold rc_notin; rewrite map_app cstr_extra_args_lax_false rc_notin_false_left2.
      all: eapply (rc_notin_decrease (check_lax_specialize_argument _ _)).
      all: unfold rc_notin_bool.
      all: cbn in *.
      + eapply rc_notin_inst_up => //. try lia. 1: apply wd_inst_uparams_no_rc.
        apply on_free_vars_argument_free in H => //.
      + apply eq_prod in Heqnth as [Hfst Hsnd].
        eapply on_free_vars_tProd, on_free_vars_mkApps, on_free_vars_tLambda; len.
        (* tProd largs *)
        - eapply Alli_mapi_rec => //. intros.
          eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
        (* mkApss _ inst_args *)
        - eapply All_map; eapply All_impl => //.
          intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
        (* llargs *)
        - eassert (wd_llargs : Alli _ _ llargs). {
            rewrite -Hfst. eapply All_nth.
            1: len; rewrite size_inst_uparams => //.
            eapply (All_impl wd_l_inst_uparams_no_rc). intros [] [] => //.
        }
          eapply (Alli_mapi wd_llargs). cbn.
          intros j x wdx. eapply rc_notin_lift_overflow => //.
        (* arg *)
        - eassert (wd_t : on_free_vars_argument xpredT (nb_g_largs + #|llargs|) (arg_is_free t)). {
            rewrite -Hfst -Hsnd. eapply All_nth.
            1: len; rewrite size_inst_uparams => //.
            eapply (All_impl wd_l_inst_uparams_no_rc).
            intros [] [] => //=.
          }
          apply on_free_vars_argument_free in wd_t.
          eapply rc_notin_lift_overflow => //.
    Qed.

    Definition rc_notin_argument_sub_uparam lb nb_binders
      largs inst_args llargs arg_to_sub :
      Alli (rc_notin_bool lb) nb_binders largs ->
      All (rc_notin_bool lb (nb_binders + #|largs|)) inst_args ->
      (* --- *)
      #|llargs| = #|inst_args| ->
      Alli (rc_notin_bool lb) (nb_binders + #|largs|) llargs ->
      rc_notin_argument_bool lb (nb_binders + #|largs| + #|llargs|) arg_to_sub ->
      rc_notin_argument_bool lb nb_binders (sub_uparam largs inst_args llargs arg_to_sub).
    Proof.
      intros rc_notin_largs rc_notin_inst_args fapp_arg rc_notin_llargs rc_notin_arg_to_sub.
      remember (nb_binders + #|largs| + #|llargs|) as m.
      induction rc_notin_arg_to_sub using on_free_vars_argument_rect'; cbn.
      + constructor.
        eapply on_free_vars_tProd, on_free_vars_mkApps, on_free_vars_tLambda => //.
        rewrite -Heqm => //.
      + constructor => //.
        - apply Alli_app_inv => //. apply (Alli_mapi on_free_largs).
          intros. eapply on_free_vars_subst_eq => //.
          1: apply All_rev => //.
          apply_eq H. do 2 f_equal. len.
        - apply All_map, (All_impl on_free_inst_args).
          intros. eapply on_free_vars_subst_eq => //; len.
          1: rewrite !Nat.add_assoc; reflexivity.
          1: apply All_rev => //.
          apply_eq H. do 2 f_equal. len.
      + constructor => //.
        - apply Alli_app_inv => //. apply (Alli_mapi on_free_largs).
          intros. eapply on_free_vars_subst_eq => //.
          1: apply All_rev => //.
          apply_eq H. do 2 f_equal. len.
        - apply All_map, (All_impl on_free_inst_args).
          intros. eapply on_free_vars_subst_eq => //; len.
          1: rewrite !Nat.add_assoc; reflexivity.
          1: apply All_rev => //.
          apply_eq H. do 2 f_equal. len.
      + constructor => //.
        - apply Alli_app_inv => //. apply (Alli_mapi on_free_largs).
          intros. eapply on_free_vars_subst_eq => //.
          1: apply All_rev => //.
          apply_eq H. do 2 f_equal. len.
        - len. induction IHuparams; constructor. 2: apply IHIHuparams => //.
          destruct x as [llargs0 arg0], px as [ofr_llargs0 ofr_arg0]; cbn in *; len.
          split.
          * apply (Alli_mapi ofr_llargs0).
            intros. eapply on_free_vars_subst_eq => //.
            2: apply All_rev => //. len.
            apply_eq H. do 2 f_equal. len.
          * eapply on_free_vars_argument_subst_eq => //; len.
            1: rewrite !Nat.add_assoc => //.
            1: apply All_rev => //.
            apply_eq ofr_arg0. lia.
        - apply All_map, (All_impl on_free_inst_nuparams_indices).
          intros. eapply on_free_vars_subst_eq => //; len.
          1: rewrite !Nat.add_assoc; reflexivity.
          1: apply All_rev => //.
          apply_eq H. do 2 f_equal. len.
    Qed.

    Definition rc_notin_argument_specialize_up lb nb_binders m arg :
      #|lb| + nb_binders <= m ->
      rc_notin_argument_bool lb nb_binders arg ->
      positive_argument nb_l_block l_uparams_b l_nuparams lb true nb_binders arg ->
      rc_notin_argument_bool lb nb_binders
      (specialize_argument m arg).
    Proof.
      intros Hlt rc_notin_arg.
      induction rc_notin_arg using on_free_vars_argument_rect' in m,Hlt |-; cbn; intros pos_arg.
      + constructor. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
      + destruct (nth k l_inst_uparams_no_rc err_arg) as [llarg arg_to_sub] eqn:H; cbn.
        inversion pos_arg; subst.
        apply eq_prod in H as [Hfst Hsnd]. len.
        apply rc_notin_argument_sub_uparam ; len => //.
        - apply (Alli_mapi_rec on_free_largs).
          intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
        - apply All_map, (All_impl on_free_inst_args).
          intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
        - rewrite -H6 -Hfst. symmetry.
          apply (All2_nth (fun n x => n = #|x.1|)) => //.
          apply fapp_l_inst_uparams_no_rc.
        - eapply Alli_mapi.
          * rewrite -Hfst. apply All_nth => //. 1: rewrite size_l_inst_uparams_no_rc //.
            eapply (All_impl wd_l_inst_uparams_no_rc). intros x [a b]. exact a.
          * cbn. intros n x rc_notin_x.
            eapply rc_notin_lift_overflow => //.
        - eapply rc_notin_argument_lift_overflow with (q := 0) => //.
          rewrite -Hsnd. apply All_nth => //. 1: rewrite size_l_inst_uparams_no_rc //.
          eapply (All_impl wd_l_inst_uparams_no_rc). intros x [a b].
          eapply on_free_vars_argument_xpredT in b. exact b.
      + constructor.
        - apply (Alli_mapi_rec on_free_largs).
          intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
        - apply All_app_inv.
          * unfold tRels. apply All_rev_pointwise_map. len.
            intros. unfold shiftnP. case_inequalities => //. cbn.
            eapply rc_notinP_overflow. len.
          * eapply All_map, (All_impl on_free_inst_args).
            intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
      + constructor.
        - apply (Alli_mapi_rec on_free_largs).
          intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
        - inversion pos_arg; subst; cbn in *.
        assert (All (fun x => positive_argument nb_l_block
            l_uparams_b l_nuparams lb true (nb_binders + #|largs| + #|x.1|) x.2) inst_uparams0).
        {
          clear -X1. induction X1; constructor; eauto.
          destruct r as [[]]. destruct y.2 => //. apply positive_argument_increase2 => //.
        }
        clear pos_arg X1 X2 X3.
          induction IHuparams; constructor.
          all: inversion X4; subst; cbn in *.
          2: apply IHIHuparams => //.
          destruct x as [llargs arg], px as [ofr_llargs ofr_arg]; cbn in *; len.
          split.
          * apply (Alli_mapi_rec ofr_llargs).
            intros. eapply rc_notin_inst_up => //. eapply wd_inst_uparams_no_rc.
          * inversion X4. apply h => //.
        - apply All_map, (All_impl on_free_inst_nuparams_indices).
          intros. eapply rc_notin_inst_up => //. apply wd_inst_uparams_no_rc.
    Qed.
  (** END ADDITION NO INDUCTIVE-INDUCTIVE **)


  Definition pos_specialize_argument Γ lax nb_binders arg :
    positive_argument nb_l_block l_uparams_b l_nuparams (map check_lax Γ) lax nb_binders arg ->
    positive_argument nb_m_block g_uparams_b g_nuparams
      (map check_lax (cstr_extra_args ++ (mapi_rec specialize_argument Γ nb_l_nuparams)))
      lax nb_binders (specialize_argument (nb_l_nuparams + #|Γ| + nb_binders) arg).
  Proof.
    intro pos_arg; induction pos_arg using positive_argument_rect'; cbn.
    + apply pos_arg_is_free; rewrite -> ? length_map in *.
      apply inst_no_rc_preserve_isup_notin => //.
    + rewrite <- Nat.add_assoc.
      destruct (nth k l_inst_uparams_no_rc err_arg) as [llargs arg_to_sub] eqn:H.
      apply eq_prod in H as [Hfst Hsnd]. len. rewrite !Nat.add_assoc.
      apply pos_sub_uparams. all: len; repeat (rewrite !Nat.add_assoc); rewrite -> ? length_map in *.
      - apply Alli_inst_no_rc_isup_notin => //.
      - apply All_inst_no_rc_isup_notin => //.
      - rewrite - fapp -Hfst. symmetry.
        apply (All2_nth (fun n x => n = #|x.1|)) => //. apply fapp_l_inst_uparams_no_rc.
      - eapply Alli_mapi.
        * rewrite -Hfst. apply All_nth => //. 1: rewrite size_l_inst_uparams_no_rc //.
          apply isup_notin_llargs_no_rc.
        * cbn. intros n x isup_notin_x.
          unfold isup_notin in isup_notin_x.
          erewrite <-(PCUICOnFreeVars.on_free_vars_lift _ _ _ x) in isup_notin_x.
          eapply on_free_vars_impl with (2 := isup_notin_x).
          intros i; unfold strengthenP, shiftnP.
          destruct (Nat.ltb_spec i n); cbn.
          repeat case_inequalities; cbn; try solve [lia | intros [=] | done].
          repeat case_inequalities; cbn; try solve [lia | intros [=] | done].
          replace (i - (nb_l_nuparams + #|Γ| + nb_binders + #|largs|) - (nb_new_cxt_sub + n))
          with (i - (nb_new_cxt_sub + nb_l_nuparams + #|Γ| + nb_binders + #|largs| + n))
          by lia. done.
      - apply pos_arg_inc => //.
        assert (MX : positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args_no_rc) lax (nb_g_largs + #|llargs|) arg_to_sub).
        1: { rewrite -Hfst -Hsnd. apply All_nth => //. 1: rewrite size_l_inst_uparams_no_rc; lia.
             destruct lax; only 2: inversion e. eapply positive_true_all_no_rc.
          }
      replace (nb_l_nuparams + #|Γ| + nb_binders + #|largs|) with ((nb_l_nuparams + #|Γ|) + (nb_binders + #|largs|)) by len.
      rewrite -(simpl_lift_argument _ _ _ _ ((nb_binders + #|largs|) + #|llargs|)) //.
      rewrite !map_app !map_map /= !map_xpred0 -!app_assoc app_assoc; len.
      eapply @pos_lift_arg_context_eq => //=.
      eapply @pos_lift_arg_binders => //=.
      eapply pos_arg_notin_unfold => //.
      (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
      - eapply (Alli_mapi_rec rc_notin_largs); cbn.
        intros. eapply rc_notin_specialize_up => //.
      - apply All_map, (All_impl rc_notin_args). intros.
        eapply rc_notin_specialize_up => //.
      (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
    + apply pos_arg_is_ind => //; rewrite -> ? length_map in *.
      - apply Alli_inst_no_rc_isup_notin => //.
      - apply All_app_inv; len.
        -- unfold tRels. apply All_rev_pointwise_map. cbn.
           intros. apply shiftnP_lt. lia.
        -- apply All_inst_no_rc_isup_notin => //.
    + apply pos_arg_is_nested with (mdecl := mdecl); rewrite -> ? length_map in * => //.
      - apply Alli_inst_no_rc_isup_notin => //.
      - apply All_inst_no_rc_isup_notin => //.
      - clear rc_notin_instance.
        induction Ppos_nested; rewrite -> ? length_map in * ; constructor; only 2: apply IHPpos_nested.
        destruct x as [l_ll l_arg], y as [cdecl pos_arg], r as [[fapp pos_l_ll] pos_l_arg]; cbn in *.
        len; repeat split => //.
        * apply Alli_inst_no_rc_isup_notin => //.
        * apply_eq p. f_equal. lia.
      (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
      - eapply (Alli_mapi_rec rc_notin_largs). intros.
        eapply rc_notin_specialize_up => //.
      - assert (pos_inst_uparams0 : All (fun x => positive_argument nb_l_block l_uparams_b l_nuparams (map check_lax Γ) true (nb_binders + #|largs| + #|x.1|) x.2) inst_uparams0).
        { clear rc_notin_instance Ppos_nested.
          induction pos_nested; constructor. 2: apply IHpos_nested => //.
          destruct r as [[] ] => //. destruct y.2 => //.
          apply positive_argument_increase2 => //.
        }
      apply All_map, (All_impl2 pos_inst_uparams0 rc_notin_instance).
        intros [llargs arg] pos_arg [rc_notin_llargs rc_notin_arg]; cbn in *; len; split.
        * apply (Alli_mapi_rec rc_notin_llargs). intros.
          eapply rc_notin_specialize_up => //.
        * rewrite map_app cstr_extra_args_lax_false.
          eapply rc_notin_argument_false_left.
          eapply (rc_notin_argument_decrease (check_lax_specialize_argument Γ _)).
          eapply rc_notin_argument_specialize_up => //.
      (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
  Qed.


  (* The instanciation of the uniform parameters is defined in the context:

        g_uparams ,,, g_nuparams ,,, g_args ,,, g_largs |- inst_uparams

     The constructor are definied in the context

        l_uparams ,,, l_nuparams ,,, cstr_args |- cstr_indices

      We then have as a new type:

         (↓↓g_args ,,, ↓g_largs), (↓σ)(l_nuparams ,,, cstr_args)
          |- new_indices ++ (↓σ) #|l_nuparams ,,, cstr_args| cstr_indices

      Note, we must also add references to new_indices as
      (↓↓g_args ,,, ↓g_largs), (↓σ)(l_nuparams) are new  indices!
  *)
  Definition specialize_ctor (ctor : constructor_body) : constructor_body :=
  {|
    (* cstr_name     := todo; *)
    cstr_args    := cstr_extra_args
                    ++ mapi (fun i => specialize_argument (nb_l_nuparams + i)) ctor.(cstr_args)  ;
    cstr_indices :=    tRels #|ctor.(cstr_args)| (#|g_args_no_rc| + #|g_largs| + #|l_nuparams|)
                    ++ map (inst (up (nb_l_nuparams + #|ctor.(cstr_args)|) inst_uparams_no_rc))
                           ctor.(cstr_indices)
  |}.

  Definition pos_specialize_ctor ctor :
    positive_constructor nb_l_block l_uparams_b l_nuparams ctor ->
    positive_constructor nb_m_block g_uparams_b g_nuparams (specialize_ctor ctor).
  Proof.
    unfold positive_constructor, specialize_ctor. cbn [cstr_args cstr_indices].
    intros [pos_cstr_args pos_cstr_indices]. split.
    (* pos args *)
    + apply All_telescope_app_inv.
      - apply PosArg_cstr_extra_args.
      - unfold PosArg, PosArgBool.
        clear pos_cstr_indices.
        induction pos_cstr_args; cbn. 1: constructor.
        rewrite mapi_app. apply All_telescope_app_inv.
        { apply IHpos_cstr_args => //. }
        cbn. apply All_telescope_singleton.
        destruct p.
        split; [intros H | ].
        all: unfold mapi; rewrite !app_nil_r -!mapi_rec_add; fold specialize_argument;
             rewrite {1}Nat.add_0_r !Nat.add_assoc.
        * apply rc_notin_specialize_argument; len => //.
          len in H.
        * apply pos_specialize_argument with (Γ := Γ) => //.
    + len. apply All_app_inv.
      - unfold tRels. apply All_rev_pointwise_map; cbn.
        intros. apply shiftnP_lt => //.
      - apply All_inst_no_rc_isup_notin => //.
  Qed.

  Definition specialize_one_inductive_body (idecl : one_inductive_body) : one_inductive_body :=
  {|
    (* ind_name      := todo; *)
    ind_indices   := new_indices idecl.(ind_indices);
    (* ind_sort      := todo; *)
    (* ind_kelim     := todo; *)
    ind_ctors     := map specialize_ctor idecl.(ind_ctors);
    (* ind_relevance := todo; *)
  |}.

  Definition pos_specialize_idecl idecl :
    positive_one_inductive_body nb_l_block l_uparams_b l_nuparams idecl ->
    positive_one_inductive_body nb_m_block g_uparams_b g_nuparams (specialize_one_inductive_body idecl).
  Proof.
    intros [pos_ctors pos_indices]; split; cbn.
    + eapply All_map, (All_impl pos_ctors pos_specialize_ctor).
    (* one extra case if you want to prove it is not inductive inductive *)
    + apply pos_new_indices => //.
  Qed.

End NestedToMutualInd.











(* Going From Nested to Mutual *)

(* To deal with nested arugments, we further suppose the environment is
   well-formed, and therefore that all previously defined inductives are positive. *)
Parameter (E_pos : forall kname, if lookup_minductive E kname is Some mdecl
                        then positive_mutual_inductive_body mdecl else False).


Section NestedToMutualIndb.

  Context (nb_g_block : nat).
  Context (g_uparams_b : list (context_decl * bool)).
  Notation nb_g_uparams := #|g_uparams_b|.

  Context (g_nuparams : context).
  Notation nb_g_nuparams := #|g_nuparams|.

  (* function to be folded *)
  Definition Acc : Type := list argument * list one_inductive_body.

  Definition nested_to_mutual_one_argument (acc : Acc) (arg : argument) : Acc :=
    let nargs := acc.1 in let acc_indb := acc.2 in
    match arg with
    | arg_is_nested largs (mkInd kname pos_indb) u inst_uparams_no_rc inst_nuparams_indices =>
      if (lookup_minductive E kname) is Some mdecl
      then (let new_indb := map (specialize_one_inductive_body (nb_g_block + #|acc_indb|)
                                  g_uparams_b g_nuparams nargs largs mdecl.(ind_nuparams)
                                  inst_uparams_no_rc) mdecl.(ind_bodies) in
            (* we need to add var for new nup + new indices => dup *)
            let new_indices := tRels 0 nb_g_nuparams
              ++ filter2 (map check_lax nargs) (tRels nb_g_nuparams #|nargs|)
              ++ tRels (nb_g_nuparams + #|nargs|) #|largs| in
          let new_arg := arg_is_ind largs (pos_indb + nb_g_block + #|acc_indb|)
                          (new_indices ++ inst_nuparams_indices) in
          (nargs ++ [new_arg], acc_indb ++ new_indb))
      else (nargs ++ [arg], acc_indb)
    | _ => (nargs ++ [arg], acc_indb)
    end.

  (* Fold Arguments *)
  Definition PosAcc (acc : Acc) : Type :=
      let nargs := acc.1 in let acc_indb := acc.2 in
        All_telescope (PosArg (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) nargs
    * (All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb).

  Tactic Notation "solve_nested_to_mut" :=
    split => //; apply All_telescope_app_inv => //; repeat constructor => //;
    apply All_telescope_singleton; rewrite app_nil_r; split => //; constructor => //; lia.

  Definition pos_nested_to_mutual_one_argument (acc : Acc) arg :
    (* spec *)
    forall (pos_acc : PosAcc acc) (pos_arg : PosArg nb_g_block g_uparams_b g_nuparams acc.1 arg),
    (* res *)
    PosAcc (nested_to_mutual_one_argument acc arg).
  Proof.
    destruct acc as [nargs acc_indb].
    unfold PosAcc, PosArg.
    intros [pos_nargs pos_acc_indb] [rc_notin_arg pos_arg].
    destruct pos_arg; cbn in *.
    all: try solve_nested_to_mut.
    rewrite -> ? Nat.add_0_r in *.
    rewrite -> ? length_map in *.
    rewrite e0; cbn in *. len. rewrite !Nat.add_assoc.
    pose proof (p := E_pos kname); rewrite e0 in p; cbn in p.
    destruct p as [pos_l_nuparams pos_l_indb]. split; cbn.
    + apply All_telescope_app_inv.
      1 :{ eapply All_telescope_impl; tea; cbn.
           intros Γ myarg [rc_notin_myarg pos_myarg]. split => //. apply pos_arg_inc => //. }
      apply All_telescope_singleton. rewrite app_nil_r. split => //.
      constructor; len => //.
      apply All_app_inv => //. repeat apply All_app_inv.
      * apply All_rev_pointwise_map; intros; apply shiftnP_lt; lia.
      * apply All_filter2, All_rev_pointwise_map; intros; apply shiftnP_lt; lia.
      * apply All_rev_pointwise_map; intros; apply shiftnP_lt; lia.
    + apply All_app_inv; only 1: (eapply All_impl; tea; intros; apply pos_idecl_inc) => //.
      eapply All_map, (All_impl pos_l_indb), pos_specialize_idecl => //.
      eapply All2_impl; tea.
      intros [llargs arg] [cdecl pos] [[fapp pos_llargs] pos_arg].
      cbn in *. repeat split; tea. apply pos_arg_inc => //.
  Qed.

  Definition length1_nested_to_mutual_one_argument acc arg :
    #|(nested_to_mutual_one_argument acc arg).1| = 1 + #|acc.1|.
  Proof.
    destruct arg; cbn.
    4: destruct ind; destruct (lookup_minductive E _).
    all: len; cbn; try lia.
  Qed.

  Definition nested_to_mutual_argument args acc_indb :=
    fold_left nested_to_mutual_one_argument args ([],acc_indb).

  Definition length_pos_left args acc :
    #|(fold_left nested_to_mutual_one_argument args acc).1| = #|acc.1| + #|args|.
  Proof.
    induction args in acc |- *; cbn.
    - lia.
    - rewrite IHargs. rewrite length1_nested_to_mutual_one_argument. lia.
  Qed.



  (* ccl fold *)
  Definition pos_nested_to_mutual_argument {args acc_indb}
    (* spec *)
    (pos_args : All_telescope (PosArg nb_g_block g_uparams_b g_nuparams) args)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb) :
    (* new_spec *)
    PosAcc (nested_to_mutual_argument args acc_indb).
  Proof.
    unfold nested_to_mutual_argument.
    eapply (spec_fold_All_check check_lax _ _ _ PosAcc (PosArgBool _ _ _)); cbn.
    - apply All_telescope_to_All_check. tea.
    - repeat constructor; cbn => //.
    - clear. intros [acc_nargs acc_indb] arg.
      destruct arg; cbn. 4: destruct ind as [kname pos_indb], (lookup_minductive E kname).
      all:rewrite ? map_app; cbn; reflexivity.
    - apply pos_nested_to_mutual_one_argument.
  Qed.


  Definition nested_to_mutual_one_ctor ctor acc_indb :
    constructor_body * list one_inductive_body :=
  let x := nested_to_mutual_argument ctor.(cstr_args) acc_indb in
  let new_ctor := {|
    (* cstr_name    := ctor.(cstr_name); *)
    cstr_args    := x.1 ;
    cstr_indices := ctor.(cstr_indices)
    |} in
  (new_ctor, x.2).

  Definition pos_nested_to_mutual_one_ctor ctor acc_indb
    (* spec *)
    (pos_ctor : positive_constructor nb_g_block g_uparams_b g_nuparams ctor)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb):
    (* new_spec *)
    let x := nested_to_mutual_one_ctor ctor acc_indb in
      (positive_constructor (nb_g_block + #|x.2|) g_uparams_b g_nuparams x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2).
  Proof.
    destruct pos_ctor as [pos_args pos_indices].
    pose proof (e := pos_nested_to_mutual_argument pos_args pos_acc_indb).
    destruct e as [pos_nargs pos_nacc].
    cbn. set (x := nested_to_mutual_argument ctor.(cstr_args) acc_indb) in *.
    repeat split; cbn => //.
    rewrite length_pos_left => //.
  Qed.


  Definition nested_to_mutual_ctor ctors acc_indb : list constructor_body * list one_inductive_body :=
  fold_left ( fun acc ctor =>
      let x := nested_to_mutual_one_ctor ctor acc.2 in
      (acc.1 ++ [x.1], x.2)
    )
    ctors
    ([],acc_indb).

  Definition length2_nested_to_mutual_argument args new_indb :
    #|new_indb| <= #|(nested_to_mutual_argument args new_indb).2|.
  Proof.
    unfold nested_to_mutual_argument.
    change new_indb with (( @nil argument,new_indb).2) at 1.
    generalize (( @nil argument, new_indb)).
    induction args as [|arg args IHargs] => //.
    intros. etransitivity. 2: eapply IHargs => //.
    destruct arg; cbn => //.
    destruct ind as [kname ?]; cbn; destruct (lookup_minductive E kname); cbn => //.
  Qed.


  Definition pos_nested_to_mutual_ctors {ctors acc_indb}
    (* spec *)
    (pos_ctors : All (positive_constructor nb_g_block g_uparams_b g_nuparams) ctors)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb) :
    (* new_spec *)
    let x := nested_to_mutual_ctor ctors acc_indb in
      (All (positive_constructor (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2).
  Proof.
    cbn. unfold nested_to_mutual_ctor.
    eapply spec_fold_Alli; cbn.
    - eapply All_to_Alli. tea.
    - split; [constructor| assumption].
    - intros; len ; cbn ; lia.
    - intros [nctors new_indb] ctor; cbn.
      intros [pos_nctors pos_new_indb] pos_ctor.
      split.
      + apply All_app_inv.
        * eapply All_impl; tea.
          intros; eapply pos_ctor_inc_le; tea.
          apply add_le_mono_l_proj_l2r, length2_nested_to_mutual_argument.
        * constructor; only 2: constructor.
          eapply fst.
          eapply pos_nested_to_mutual_one_ctor; cbn => //.
      + eapply snd. apply pos_nested_to_mutual_one_ctor => //.
  Qed.

  Definition length2_nested_to_mutual_ctor ctors new_indb :
    #|new_indb| <= #|(nested_to_mutual_ctor ctors new_indb).2|.
  Proof.
    unfold nested_to_mutual_ctor.
    change new_indb with (( @nil constructor_body,new_indb).2) at 1.
    generalize (( @nil constructor_body, new_indb)).
    induction ctors as [|ctor ctors IHctors]; cbn.
    - lia.
    - intros. etransitivity. 2: eapply IHctors. cbn.
      apply length2_nested_to_mutual_argument.
  Qed.


  (* check preservation *)
  Definition nested_to_mutual_one_indb indb acc_indb : one_inductive_body * list one_inductive_body :=
  let x := nested_to_mutual_ctor indb.(ind_ctors) acc_indb in
  let new_indb := {|
    (* ind_name      := indb.(ind_name); *)
    ind_indices   := indb.(ind_indices);
    (* ind_sort      := indb.(ind_sort); *)
    (* what to do here ? *)
    (* ind_kelim     := todo;  *)
    ind_ctors     := x.1 ;
    (* what to do here ? *)
    (* ind_relevance := todo;  *)
  |} in
  (new_indb, x.2).

  Definition pos_nested_to_mutual_one_indb indb acc_indb
    (* spec *)
    (pos_indb : positive_one_inductive_body nb_g_block g_uparams_b g_nuparams indb)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb):
    (* new_spec *)
    let x := nested_to_mutual_one_indb indb acc_indb in
      (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2).
  Proof.
    destruct pos_indb as [pos_ctors pos_indices]; cbn.
    pose proof (e := pos_nested_to_mutual_ctors pos_ctors pos_acc_indb).
    destruct e as [pos_nctros pos_nacc].
    cbn in *. set (x := nested_to_mutual_one_indb indb acc_indb) in *.
    repeat split; cbn => //.
  Qed.


  Definition nested_to_mutual_indb indbs : list one_inductive_body * list one_inductive_body :=
    fold_left ( fun acc indb =>
      let x := nested_to_mutual_one_indb indb acc.2 in
      (acc.1 ++ [x.1], x.2)
      )
      indbs
      ([],[]).

  Definition pos_nested_to_mutual_indb {indbs}
    (* spec *)
    (pos_indbs : All (positive_one_inductive_body nb_g_block g_uparams_b g_nuparams) indbs):
    (* new_spec *)
    (fun x =>
      (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2))
    (nested_to_mutual_indb indbs).
  Proof.
    cbn. unfold nested_to_mutual_indb.
    eapply spec_fold_Alli; cbn.
    - eapply All_to_Alli. tea.
    - rewrite Nat.add_0_r. split; constructor.
    - intros; len ; cbn ; lia.
    - intros [nindb new_indb] indb; cbn.
      intros [pos_nindb pos_new_indb] pos_indb.
      split.
      + apply All_app_inv.
        * eapply All_impl; tea.
          intros; eapply pos_idecl_inc_le; tea.
          apply add_le_mono_l_proj_l2r, length2_nested_to_mutual_ctor.
        * constructor; only 2: constructor.
          eapply fst.
          eapply pos_nested_to_mutual_one_indb; cbn => //.
      + eapply snd. apply pos_nested_to_mutual_one_indb => //.
  Qed.


  Definition length_nested_to_mutual_indb indbs :
    #|(nested_to_mutual_indb indbs).1| = #|indbs|.
  Proof.
    unfold nested_to_mutual_indb; cbn.
    rewrite -(Nat.add_0_r #|indbs|).
    change 0 with #|( @nil one_inductive_body, @nil one_inductive_body).1|.
    generalize ( @nil one_inductive_body, @nil one_inductive_body).
    induction indbs; cbn => //=.
    intros p. rewrite IHindbs //=.
  Qed.

End NestedToMutualIndb.


Definition nested_to_mutual (mdecl : mutual_inductive_body) : mutual_inductive_body :=
  {|
    ind_finite    := mdecl.(ind_finite);
    ind_uparams   := mdecl.(ind_uparams);
    ind_nuparams  := mdecl.(ind_nuparams);
    ind_bodies    := let x := nested_to_mutual_indb #|mdecl.(ind_bodies)|
                        mdecl.(ind_uparams) mdecl.(ind_nuparams) mdecl.(ind_bodies)
                      in
                      x.1 ++ x.2;
    (* what to do here ? *)
    (* ind_universes := todo;  *)
    (* what to do here ? *)
    (* ind_variance  := todo;  *)
  |}.

Definition pos_nested_to_mutual mdecl :
  positive_mutual_inductive_body mdecl ->
  positive_mutual_inductive_body (nested_to_mutual mdecl).
Proof.
  intros [pos_mdecl_nuparams pos_mdecl_indb].
  apply (pos_nested_to_mutual_indb) in pos_mdecl_indb as [pos_new_indb pos_acc_indb].
  unfold nested_to_mutual; cbn.
  set (x := nested_to_mutual_indb #|mdecl.(ind_bodies)| mdecl.(ind_uparams)
              mdecl.(ind_nuparams) mdecl.(ind_bodies)) in *.
  (* proof *)
  split; cbn => //.
  len. rewrite length_nested_to_mutual_indb. apply All_app_inv => //.
Qed.