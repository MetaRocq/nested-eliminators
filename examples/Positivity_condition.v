(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
From MetaRocq.PCUIC Require Import BDStrengthening.
Import PCUICEnvironment.

From Formalization Require Import Lemma.

Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | reflexivity
    | len
    ].

Ltac done_gen tac :=
  solve
  [ repeat first
    (* 1. eassumption + reflexivity *)
    [ fast_done
    (* 2. intros ? + assumption + 0 cost hints *)
    | solve [trivial]
    | solve [symmetry; trivial]
    (* 3. introduces varibales *)
    | progress (hnf; intros)
    (* 4. check for inconsistencies *)
    | contradiction
    | match goal with H : ~ _ |- _ => solve [case H; reflexivity || trivial] end
    | tac            (* inversion scheme *)
    (* 5. change goal *)
    | split
    ]
  ].

Ltac done := done_gen discriminate.





Module ViewInductive.
(* *** Simplified Def of Inductive Types *** *)

(* An argument is either:
  - a term t that does not contain the ind nor the sp_uparams
  - of the form (∀ x1 ... xn, A / Ind i / tInd ...

  - pos_indb is the position of the block
  - k is the position of the uparam in the telescope
*)
Unset Elimination Schemes.

Inductive argument : Type :=
| arg_is_free      (t : term)
| arg_is_sp_uparam (largs : list term) (k : nat) (args : list term)
| arg_is_ind       (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
| arg_is_nested    (largs : list term) (ind : inductive) (u : Instance.t)
                    (inst_uparams : list (list term * argument)) (inst_nuparams_indices : list term).

Fixpoint argument_rect (P : argument -> Type)
  (Harg_is_free : (forall t : term, P (arg_is_free t)))
  (Harg_is_sp_uparam : forall (largs : list term) (k : nat) (args : list term),
                        P (arg_is_sp_uparam largs k args))
  (Harg_is_ind : forall (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term),
                 P (arg_is_ind largs pos_indb inst_nuparams_indices))
  (Harg_is_nested : forall (largs : list term) (ind : inductive) (u : Instance.t)
                    (inst_uparams : list (list term * argument))
                    (pos_inst_uparams : All (fun x => P x.2) inst_uparams)
                    (inst_nuparams_indices : list term),
                    P (arg_is_nested largs ind u inst_uparams inst_nuparams_indices)):
  forall (a : argument), P a.
Proof.
  intros a; destruct a.
  - apply Harg_is_free.
  - apply Harg_is_sp_uparam.
  - apply Harg_is_ind.
  - apply Harg_is_nested. induction inst_uparams; constructor.
    apply argument_rect; eauto. apply IHinst_uparams.
Qed.

Set Elimination Schemes.

(* Check if an argument is a constant *)
Definition check_lax : argument -> bool :=
  fun arg => if arg is arg_is_free _ then false else true.

Definition strict_to_term arg (Hlax : check_lax arg = false) : term.
  destruct arg; only 2-4: inversion Hlax. exact t.
Defined.

Definition argument_strict {arg} :
  forall (Ht : check_lax arg = false),
  arg = arg_is_free (strict_to_term arg Ht).
Proof.
  destruct arg; intros Ht; inversion Ht.
  done.
Qed.


(* mapi for argument *)
Fixpoint argument_mapi (f : nat -> term -> term) above arg : argument :=
  match arg with
  | arg_is_free t => arg_is_free (f above t)
  | arg_is_sp_uparam largs k inst_args =>
      let largs' := mapi (fun i => f (above + i)) largs in
      let inst_args' := map (f (above + #|largs|)) inst_args in
      arg_is_sp_uparam largs' k inst_args'
  | arg_is_ind largs pos_indb inst_nuparams_indices =>
      let largs' := mapi (fun i => f (above + i)) largs in
      let inst_nuparams_indices' := map (f (above + #|largs|)) inst_nuparams_indices in
      arg_is_ind largs' pos_indb inst_nuparams_indices'
  | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
      let largs' := mapi (fun i => f (above + i)) largs in
      let inst_uparams' := map (fun x =>
        ( mapi (fun i => f (above + #|largs| + i)) x.1,
          argument_mapi f (above + #|largs| + #|x.1|) x.2))
        inst_uparams in
      let inst_nuparams_indices' := map (f (above + #|largs|)) inst_nuparams_indices in
      arg_is_nested largs' ind u inst_uparams' inst_nuparams_indices'
  end.

Definition argument_mapi_check_lax f above arg :
  check_lax (argument_mapi f above arg) = check_lax arg.
Proof.
  destruct arg => //.
Qed.

Definition lift_argument n := argument_mapi (lift n).
Definition subst_argument l := argument_mapi (subst l).
Definition rename_argument f := argument_mapi (fun n => rename (shiftn n f)).



(* on_free_vars for argument *)
Inductive on_free_vars_argument (P : nat -> bool) nb_binders : argument -> Type :=
| on_free_vars_free t :
    on_free_vars (shiftnP nb_binders P) t ->
    on_free_vars_argument P nb_binders (arg_is_free t)
| on_free_vars_sup largs k inst_args :
    Alli (fun i => on_free_vars (shiftnP i P)) nb_binders largs ->
    All (on_free_vars (shiftnP (nb_binders + #|largs|) P)) inst_args ->
    on_free_vars_argument P nb_binders (arg_is_sp_uparam largs k inst_args)
| on_free_vars_ind largs pos_indb inst_nuparams_indices :
    Alli (fun i => on_free_vars (shiftnP i P)) nb_binders largs ->
    All (on_free_vars (shiftnP (nb_binders + #|largs|) P)) inst_nuparams_indices ->
    on_free_vars_argument P nb_binders (arg_is_ind largs pos_indb inst_nuparams_indices)
| on_free_vars_nested largs ind u inst_uparams inst_nuparams_indices :
    Alli (fun i => on_free_vars (shiftnP i P)) nb_binders largs ->
    All (fun x =>
          Alli (fun i => on_free_vars (shiftnP i P)) (nb_binders + #|largs|) x.1
        * on_free_vars_argument P (nb_binders + #|largs| + #|x.1|) x.2)
      inst_uparams ->
    All (on_free_vars (shiftnP (nb_binders + #|largs|) P)) inst_nuparams_indices ->
    on_free_vars_argument P nb_binders (arg_is_nested largs ind u inst_uparams inst_nuparams_indices).

Inductive All_param1 {A P} (HP : forall a, P a -> Type) : forall {lA}, All P lA -> Type :=
| All_nil_param1 : All_param1 HP ( @All_nil A P)
| All_cons_param1 : forall (x : A) (l : list A),
              forall (px : P x), HP _ px ->
              forall (al : All P l), All_param1 HP al ->
              All_param1 HP (All_cons px al).

Definition on_free_vars_argument_rect'
  P
  (PP : forall {nb_binders arg}, on_free_vars_argument P nb_binders arg -> Type)
  (PP_on_free_vars_free :
      forall nb_binders t i,
      (* ------------------------ *)
      PP (on_free_vars_free P nb_binders t i)
    )
  (PP_on_free_vars_sup :
      forall nb_binders (largs : list term) (k : nat) (inst_args : list term)
      on_free_largs on_free_inst_args,
      (* ------------------------ *)
      PP (on_free_vars_sup P nb_binders largs k inst_args on_free_largs on_free_inst_args)
    )
  (PP_on_free_vars_ind :
      forall nb_binders (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
      on_free_largs on_free_inst_args,
      (* ------------------------ *)
      PP (on_free_vars_ind P nb_binders largs pos_indb inst_nuparams_indices
            on_free_largs on_free_inst_args)
    )
  (PP_on_free_vars_nested:
      forall nb_binders (largs : list term) ind u inst_uparams inst_nuparams_indices
      on_free_largs
      (on_free_inst_uparams:
          All (fun x =>
            Alli (fun i => on_free_vars (shiftnP i P)) (nb_binders + #|largs|) x.1
          * on_free_vars_argument P (nb_binders + #|largs| + #|x.1|) x.2)
        inst_uparams)
      on_free_inst_nuparams_indices
      (IHuparams : All_param1 (fun x px => PP px.2) on_free_inst_uparams)
      ,
      (* ------------------------ *)
      PP (on_free_vars_nested P nb_binders largs ind u inst_uparams inst_nuparams_indices
          on_free_largs on_free_inst_uparams on_free_inst_nuparams_indices)
    )
  : forall nb_binders arg (p : on_free_vars_argument P nb_binders arg), PP p.
Proof.
  fix rec 3.
  intros nb_binders arg p.
  destruct p as [ | | | ? ? ? ? ? on_free_llargs on_free_inst_uparams on_free_inst_nuparams_indices ].
  - apply PP_on_free_vars_free.
  - apply PP_on_free_vars_sup.
  - apply PP_on_free_vars_ind.
  - apply PP_on_free_vars_nested => //.
    induction on_free_inst_uparams; constructor; cbn.
    destruct x; cbn.
    apply rec. apply IHon_free_inst_uparams.
Defined.

Definition on_free_vars_argument_free Q k t :
  on_free_vars_argument Q k (arg_is_free t) -> on_free_vars (shiftnP k Q) t.
Proof.
  intros X. inversion X. tea.
Qed.

Ltac solve_impl :=
  try solve [
        intros; eapply Alli_impl; tea; cbn;
        intros; eapply on_free_vars_impl; tea; cbn;
        intros ?; rewrite -?Nat.add_assoc Nat.add_comm -shiftnP_add;
        intros ?; rewrite -?Nat.add_assoc Nat.add_comm -shiftnP_add;
        intros; eapply shiftnP_impl; tea
      | intros; eapply All_impl; tea; cbn;
        intros; eapply on_free_vars_impl; tea; cbn;
        intros ?; rewrite -?Nat.add_assoc Nat.add_comm -shiftnP_add;
        intros ?; rewrite -?Nat.add_assoc Nat.add_comm -shiftnP_add;
        intros; eapply shiftnP_impl; tea
      | intros; eapply on_free_vars_impl; tea; cbn;
        intros; eapply shiftnP_impl; tea
    ].

Definition on_free_vars_argument_impl_shiftnP (P Q : nat -> bool) p q arg:
  on_free_vars_argument P p arg ->
  (forall i : nat, (shiftnP p P) i -> (shiftnP q Q) i) ->
  on_free_vars_argument Q q arg.
Proof.
  intros X; revert q; induction X using on_free_vars_argument_rect'; intros q Himpl; constructor.
  all: solve_impl.
  induction IHuparams as [|? ? [L M] IHJ]; constructor; eauto.
  split => //=. solve_impl.
  apply IHJ.
  intros ?; rewrite -Nat.add_assoc Nat.add_comm -shiftnP_add.
  intros ?; rewrite -Nat.add_assoc Nat.add_comm -shiftnP_add.
  intros; eapply shiftnP_impl; tea.
Qed.

Definition on_free_vars_argument_impl (P Q : nat -> bool) k arg:
  on_free_vars_argument P k arg ->
  (forall i : nat, P i -> Q i) ->
  on_free_vars_argument Q k arg.
Proof.
  intros. eapply on_free_vars_argument_impl_shiftnP; tea.
  intros; eapply shiftnP_impl; tea.
Qed.

Definition on_free_vars_argument_xpredT p q arg:
  on_free_vars_argument xpredT p arg ->
  on_free_vars_argument xpredT q arg.
Proof.
  intros; eapply on_free_vars_argument_impl_shiftnP; tea.
  intros i; unfold shiftnP; case_inequalities; done.
Qed.

Ltac solve_impl2 :=
  try solve [
      eapply (All_impl2); mtea;
      intros ?; eapply on_free_vars_impl2; intros ?;
      rewrite Nat.add_comm -shiftnP_add; intros ?;
      rewrite Nat.add_comm -shiftnP_add; intros ?;
      rewrite Nat.add_comm -shiftnP_add;
      eapply shiftnP_impl2; tea; done
    | eapply (Alli_impl2 ); mtea;
      intros ? ?; eapply on_free_vars_impl2; intros ?;
      rewrite -!shiftnP_add;
      eapply shiftnP_impl2; tea; done
    | eapply on_free_vars_impl2; mtea
    ].

Definition on_free_vars_argument_impl2_shiftnP {P Q R : nat -> bool} {p q r arg} :
  on_free_vars_argument P p arg ->
  on_free_vars_argument Q q arg ->
  (forall i : nat, (shiftnP p P) i -> (shiftnP q Q) i -> (shiftnP r R) i) ->
  on_free_vars_argument R r arg.
Proof.
  intros X; revert q r; induction X using on_free_vars_argument_rect'; intros q r Y Himpl; constructor.
  all: inversion Y; subst.
  all: solve_impl2.
  induction IHuparams as [|? ? [L M] IHJ]; constructor; eauto.
  all : inversion X0; subst; destruct X2; eauto.
  split => //=.
  + eapply (Alli_impl2 L a). intros ? ?.
    rewrite -!(shiftnP_add i). eapply on_free_vars_impl2; intros ?. eapply shiftnP_impl2.
    intros ?. rewrite Nat.add_comm -shiftnP_add. intros ?.
    rewrite Nat.add_comm -shiftnP_add. intros ?.
    rewrite Nat.add_comm -shiftnP_add. eapply shiftnP_impl2; mtea.
  + eapply IHJ; tea.
    intros i.
    rewrite -!Nat.add_assoc Nat.add_comm -shiftnP_add. intros ?.
    rewrite -Nat.add_comm -shiftnP_add. intros ?.
    rewrite -Nat.add_comm -shiftnP_add. eapply shiftnP_impl2; mtea.
  + eapply IHIHuparams; tea. constructor; tea.
Qed.



Ltac aux_ofva_impl :=
  try solve [
      intros; eapply Alli_mapi; tea; cbn;
      intros; rewrite -!Nat.add_assoc; eapply on_free_vars_subst; tea;
      eapply on_free_vars_impl; tea; intros ? XX; apply_eq XX; f_equal => //
    | intros; eapply All_map, All_impl; tea; cbn;
      intros; rewrite -!Nat.add_assoc; eapply on_free_vars_subst; tea;
      eapply on_free_vars_impl; tea; intros ? XX; apply_eq XX; f_equal => //
  ].

Definition on_free_vars_argument_subst_eq P k i s m n t :
  m = k + i + #|s| ->
  n = k + i ->
  All (on_free_vars (shiftnP k P)) s ->
  on_free_vars_argument P m t ->
  on_free_vars_argument P n (subst_argument s i t).
Proof.
  intros -> -> Hs X. remember (k + i + #|s|) as p eqn: Heqp. revert i Heqp.
  induction X using on_free_vars_argument_rect'; cbn in *; len; constructor.
  all: len; aux_ofva_impl; subst.
  + eapply on_free_vars_subst => //.
  + induction IHuparams as [|? ? [L M] IHJ]; constructor; eauto.
    cbn; len. split => //=; aux_ofva_impl.
    rewrite -!Nat.add_assoc. eapply IHJ => //.
Qed.

Ltac simpl_lift_arg_aux := try solve [
    rewrite !mapi_mapi; apply mapi_ext; intros; eapply PCUICLiftSubst.simpl_lift => //=
  | rewrite !map_map; apply map_ext; intros; eapply PCUICLiftSubst.simpl_lift => //=
  | eapply PCUICLiftSubst.simpl_lift => //=
].

Definition simpl_lift_argument (arg : argument) :
  forall (n k p i : nat), i <= k + n -> k <= i ->
  lift_argument p (n + k) (lift_argument n k arg) = lift_argument (p + n) k arg.
Proof.
  induction arg using argument_rect; cbn => //=; intros; f_equal.
  all: simpl_lift_arg_aux.
  induction pos_inst_uparams; simpl; f_equal; eauto.
  len. rewrite mapi_mapi. f_equal.
  - eapply mapi_ext. intros. eapply PCUICLiftSubst.simpl_lift => //.
  - erewrite <-p0. 1:f_equal => //. 2: constructor. lia.
Qed.






(* A constructor is of the form (∀ args, tRel (n - cstr_pos -1) up nup indices *)
Record constructor_body := mkViewCtor {
  (** Constructor name, without the module path. *)
  (* cstr_name : ident; *)
  (* which constructors it corresponds to *)
    (* cstr_pos : nat;  ==>> necessary ? *)
  (* list of arguments *)
  cstr_args : list argument;
  (** Indices of the return type of the constructor *)
  cstr_indices : list term;
  }.

(* cstr_args : context;  ===>> list of arg (more work done)  *)
(* cstr_type : term;     ===>> removed because inferred *)
(* cstr_arity : nat;     ===>> no link pos
    cstr_pos : nat        ===>> added cause easier to check for pos
*)

(** Data associated to a single inductive in a mutual inductive block. *)
Record one_inductive_body := mkViewInd {
  (** Name of the inductive, without the module path. *)
  (* ind_name : ident; *)
  (** Indices of the inductive, which can depend on the parameters :
      `ind_params |- ind_indices`. *)
  ind_indices : context;
  (** Sort of the inductive. *)
  (* ind_sort : Sort.t; *)
  (** Full type of the inductive. This should be equal to
      `forall ind_params ind_indices, tSort ind_sort` *)
    (* ind_type : term; ===>> removed because inferred *)
  (** Allowed eliminations for the inductive. *)
  (* ind_kelim : allowed_eliminations; *)
  (** Constructors of the inductive. Order is important. *)
  ind_ctors : list constructor_body;
  (** Names and types of primitive projections, if any. *)
    (* ind_projs : list projection_body; => removed no link pos *)
  (** Relevance of the inductive. *)
  (* ind_relevance : relevance *)
  }.

(** Data associated to a block of mutually inductive types. *)
Record mutual_inductive_body := mkViewMut {
  (** Whether the block is inductive, coinductive or non-recursive (Records). *)
  ind_finite : recursivity_kind;
  (** Context of uniform parameters + if they are strictly postive *)
  ind_uparams : list (context_decl * bool);
  (** Context of non-uniform parameters *)
  ind_nuparams : context;
  (** Components of the mutual inductive block. Order is important. *)
  ind_bodies : list one_inductive_body ;
  (** Whether the mutual inductive is universe monomorphic or universe polymorphic,
      and information about the local universes if polymorphic. *)
  (* ind_universes : universes_decl; *)
  (** Variance information. `None` when non-cumulative. *)
  (* ind_variance : option (list Universes.Variance.t) *)
  }.











(* *** Strict Positivity *** *)

(* To define positivty and handle nested arguments, we suppose given an
   environment and a function to lookup our version of inductives.
   This spares from modifying the definition of environments to our definition.

*)

  Parameter (E : global_env).
  Parameter (lookup_minductive : global_env -> kername -> option mutual_inductive_body).



Section PositiveIndBlock.

  (* Check there are no potential rc *)
  Definition rc_notinP (lb : list bool) : nat -> bool :=
    (fun n => ~~ (nth n (List.rev lb) false)).

  Definition rc_notinP_overflow Γ :
    forall i : nat, #|Γ| <= i -> rc_notinP Γ i.
  Proof.
    intros.
    unfold rc_notinP. rewrite -map_nth.
    apply nth_overflow => //=.
  Qed.

  Definition rc_notinP_false_left {n l i} :
    (rc_notinP (repeat false n ++ l)) i =
    (rc_notinP l) i.
  Proof.
    unfold rc_notinP.
    (* eapply on_free_vars_ext. eapply shiftnP_ext. *)
    rewrite -!(map_nth negb) !rev_app_distr !rev_repeat map_app.
    destruct (Nat.ltb_spec i #|l|).
    + rewrite !app_nth1 => //.
    + rewrite app_nth2 // map_repeat //= nth_repeat nth_overflow //=.
  Qed.

  Definition rc_notinP_decrease {l l'} :
    All2 (fun a b => is_true (~~ a) -> is_true (~~ b)) l l' ->
    forall i, rc_notinP l i -> rc_notinP l' i.
  Proof.
    intros H. unfold rc_notinP.
    unfold is_true.
    induction H => //=. intros i.
    assert (Hll' : #|l| = #|l'|) by (eapply All2_length; tea).
    cbn in Hll'. unfold is_true.
    destruct (Nat.ltb_spec i #|l|).
    + rewrite !app_nth1 //. all: try len. eauto.
    + destruct (Nat.ltb_spec i (S #|l|)).
      - assert (i = #|List.rev l|) as -> by len.
        assert (#|List.rev l| = #|List.rev l'|) as Hll'Rev by len.
        rewrite {2}Hll'Rev.
        rewrite !nth_middle => //.
      - rewrite !nth_overflow => //.
  Qed.

  Definition rc_notinP_false {n} : forall i, rc_notinP (repeat false n) i.
  Proof.
    unfold rc_notinP. intros i. hnf. apply negb_true_iff.
    rewrite List.rev_repeat nth_repeat //.
  Qed.

  Definition rc_notinP_app {l1 l2 n i} :
    shiftnP (#|l2| + n) (rc_notinP l1) i ->
    shiftnP n (rc_notinP l2) i -> shiftnP n (rc_notinP (l1 ++ l2)) i.
  Proof.
    unfold rc_notinP.
    rewrite Nat.add_comm -shiftnP_add.
    eapply shiftnP_impl2; clear i; unfold shiftnP.
    intros i rc_notin_l1 rc_notin_l2.
    rewrite rev_app_distr. unfold shiftnP in rc_notin_l1.
    destruct (Nat.ltb_spec i #|l2|) => //=; cbn in *.
    - rewrite app_nth1 => //.
    - rewrite app_nth2 => //.
  Qed.

  Definition rc_notinP_false_right {n l} :
    rc_notinP (l ++ repeat false n) =1 shiftnP n (rc_notinP l).
  Proof.
    intros i. unfold shiftnP, rc_notinP.
    case_inequalities; cbn.
    all : rewrite List.rev_app_distr rev_repeat.
    + rewrite app_nth1 // nth_repeat_lt //.
    + rewrite app_nth2 //.
  Qed.

  (* Term version *)
  Definition rc_notin_bool (lb : list bool) k : term -> bool :=
    on_free_vars (shiftnP k (rc_notinP lb)).

  Definition rc_notin_lift0_overflow Γ k m t:
    #|Γ| + k <= m ->
    rc_notin_bool Γ k t ->
    rc_notin_bool Γ k (lift0 m t).
  Proof.
    intros. eapply on_free_vars_lift0_overflow; tea.
    apply rc_notinP_overflow.
  Qed.

  Definition rc_notin_lift_overflow Q Γ k m j t:
    #|Γ| + k <= m ->
    on_free_vars Q t ->
    rc_notin_bool Γ (k + j) (lift m j t).
  Proof.
    intros. eapply on_free_vars_lift_overflow; tea.
    apply rc_notinP_overflow.
  Qed.

  Definition rc_notin_inst_up Q Γ k m t σ:
    #|Γ| + k <= m ->
      (forall i, on_free_vars Q (σ i)) ->
    rc_notin_bool Γ k t ->
    rc_notin_bool Γ k t.[up m σ].
  Proof.
    unfold rc_notin_bool.
    intros. eapply on_free_vars_inst_up; tea.
    intros; apply rc_notinP_overflow => //.
  Qed.

  Definition rc_notin_lift0 Q {lb n t} :
    #|lb| <= n ->
    on_free_vars Q t ->
    rc_notin_bool lb 0 (lift0 n t).
  Proof.
    unfold rc_notin_bool. intros H wdt.
    eapply on_free_vars_lift0. rewrite shiftnP0.
    eapply on_free_vars_impl; tea.
    intros; cbn. unfold addnP.
    intros; apply rc_notinP_overflow => //.
  Qed.

  Definition rc_notin_lift_context Γ1 Γ2 n t :
    rc_notin_bool Γ1 n t -> rc_notin_bool (Γ1 ++ Γ2) n (lift #|Γ2| n t).
  Proof.
    unfold rc_notin_bool. revert n.
    induction t using PCUICInduction.term_forall_list_ind; intros n' => //=.
    all:unfold test_def in *; rtoProp => //.
    all:solve_all.
    all : try (change (S n') with (1 + n')).
    all: try solve [rewrite -> shiftnP_add in *; eauto].
    unfold shiftnP, rc_notinP in *. apply orb_prop in H. destruct H; repeat case_inequalities => //=.
      rewrite List.rev_app_distr app_nth2 //=. len.
      replace (#|Γ2| + n - n' - #|Γ2|) with (n - n') by len. done.
  Qed.

  Definition rc_notin_lift_binder {Γ k n t} :
    rc_notin_bool Γ k t -> rc_notin_bool Γ (n + k) (lift n k t).
  Proof.
    unfold rc_notin_bool. revert k.
    induction t using PCUICInduction.term_forall_list_ind; intros n' => //=.
    all:unfold test_def in *; rtoProp => //.
    all:solve_all.
    all : try (change (S n') with (1 + n')).
    all: try solve [rewrite -> shiftnP_add in *; rewrite Nat.add_shuffle3; eauto].
    unfold shiftnP, rc_notinP in *. apply orb_prop in H. destruct H; repeat case_inequalities => //=.
    replace (n + n0 - (n + n')) with (n0 - n') by len. done.
  Qed.

  Definition rc_notin_decrease {l l' nb_binders t} :
    All2 (fun a b => is_true (~~ a) -> is_true (~~ b)) l l' ->
    rc_notin_bool l  nb_binders t ->
    rc_notin_bool l' nb_binders t.
  Proof.
    intros H. eapply on_free_vars_impl, shiftnP_impl.
    intros; eapply rc_notinP_decrease; tea.
  Qed.

  Definition rc_notin_false Q {n nb_binders t} :
    on_free_vars Q t ->
    rc_notin_bool (repeat false n) nb_binders t.
  Proof.
    unfold rc_notin_bool, rc_notinP. eapply on_free_vars_impl; tea.
    unfold shiftnP. intros.
    rewrite -map_nth map_rev map_repeat rev_repeat nth_repeat.
    apply orbT.
  Qed.

  Definition rc_notin_false_left {n l nb_binders t} :
    rc_notin_bool (repeat false n ++ l) nb_binders t =
    rc_notin_bool l nb_binders t.
  Proof.
    unfold rc_notin_bool. apply on_free_vars_ext, shiftnP_ext. intros i. eapply rc_notinP_false_left.
  Qed.

  Definition rc_notin_false_left2 {n l nb_binders t} :
    on_free_vars (shiftnP nb_binders (rc_notinP (repeat false n ++ l))) t =
    on_free_vars (shiftnP nb_binders (rc_notinP l)) t.
  Proof.
    eapply on_free_vars_ext, shiftnP_ext. intros ?; eapply rc_notinP_false_left.
  Qed.

  Definition rc_notin_false_right {n l nb_binders t} :
    rc_notin_bool (l ++ repeat false n) nb_binders t =
    rc_notin_bool l (n + nb_binders) t.
  Proof.
    unfold rc_notin_bool. apply on_free_vars_ext.
    rewrite Nat.add_comm. rewrite -shiftnP_add. eapply shiftnP_ext.
    eapply rc_notinP_false_right.
  Qed.

  Definition rc_notin_app {l1 l2 n t} :
    rc_notin_bool l1 (#|l2| + n) t ->
    rc_notin_bool l2 n t ->
    rc_notin_bool (l1 ++ l2) n t.
  Proof.
    unfold rc_notin_bool. eapply on_free_vars_impl2. intros; eapply rc_notinP_app; tea.
  Qed.

  Definition rc_notin Γ : nat -> term -> bool
    := rc_notin_bool (map check_lax Γ).

  Definition rc_notin_lax_false Γ arg i t :
    check_lax arg = false ->
    rc_notin (Γ ++ [arg]) i t = rc_notin Γ (i + 1) t.
  Proof.
    unfold rc_notin, rc_notin_bool. intros lax_arg.
    apply on_free_vars_ext. unfold rc_notinP.
    rewrite -shiftnP_add. eapply shiftnP_ext; intros n.
    rewrite map_app; cbn. rewrite lax_arg.
    rewrite rev_app_distr; cbn. unfold shiftnP.
    destruct n => //=.
  Qed.

  Definition shiftnPneg (k : nat) (p : nat -> bool) (i : nat) :=
  if i <? k then false else p (i - k).

  Definition rc_notin_lax_true Γ arg i t :
    check_lax arg = true ->
    rc_notin (Γ ++ [arg]) i t = on_free_vars (shiftnP i (shiftnPneg 1 (rc_notinP (map check_lax Γ)))) t.
  Proof.
    unfold rc_notin, rc_notin_bool. intros lax_arg.
    apply on_free_vars_ext.
    unfold rc_notinP.
    eapply shiftnP_ext; intros n.
    rewrite map_app; cbn. rewrite lax_arg.
    rewrite rev_app_distr; cbn.
    destruct n; cbn => //.
  Qed.

  (* for arguments *)
  Definition rc_notin_argument_bool (lb : list bool) : nat -> argument -> Type :=
    fun k arg => on_free_vars_argument (rc_notinP lb) k arg.

  Definition rc_notin_argument_decrease {l l' nb_binders arg} :
    All2 (fun a b => is_true (~~ a) -> is_true (~~ b)) l l' ->
    rc_notin_argument_bool l  nb_binders arg ->
    rc_notin_argument_bool l' nb_binders arg.
  Proof.
    intros Hll'. unfold rc_notin_argument_bool.
    intros; eapply on_free_vars_argument_impl; tea.
    intros; eapply rc_notinP_decrease; tea.
  Qed.

  Definition rc_notin_argument_false Q {n nb_binders k arg} :
    on_free_vars_argument Q k arg ->
    rc_notin_argument_bool (repeat false n) nb_binders arg.
  Proof.
    unfold rc_notin_argument_bool. intros.
    eapply on_free_vars_argument_impl with (P := xpredT).
    + eapply on_free_vars_argument_xpredT, on_free_vars_argument_impl; tea. done.
    + intros; eapply rc_notinP_false.
  Qed.

  Definition rc_notin_argument_false_left {n l nb_binders arg} :
    rc_notin_argument_bool l nb_binders arg ->
    rc_notin_argument_bool (repeat false n ++ l) nb_binders arg.
  Proof.
    unfold rc_notin_argument_bool.
    intros; eapply on_free_vars_argument_impl; tea.
    intros i; rewrite rc_notinP_false_left //.
  Qed.

  Definition rc_notin_argument_app {l1 l2 n arg} :
    rc_notin_argument_bool l1 (#|l2| + n) arg ->
    rc_notin_argument_bool l2 n arg ->
    rc_notin_argument_bool (l1 ++ l2) n arg.
  Proof.
    unfold rc_notin_argument_bool.
    intros X Y. eapply (on_free_vars_argument_impl2_shiftnP X Y).
    intros. eapply rc_notinP_app; tea.
  Qed.

  Ltac rc_notin_lift_overflow_aux := try solve [
      eapply All_map, All_impl; tea; cbn; len;
      intros ?; rewrite -Nat.add_assoc; eapply rc_notin_lift_overflow; tea
    | eapply Alli_mapi; tea; cbn; intros; rewrite -Nat.add_assoc; eapply rc_notin_lift_overflow; tea
    | eapply rc_notin_lift_overflow; tea
  ].

  Definition rc_notin_argument_lift_overflow Q Γ q k m j arg:
    #|Γ| + k <= m ->
    on_free_vars_argument Q q arg ->
    rc_notin_argument_bool Γ (k + j) (lift_argument m j arg).
  Proof.
    intros Hinf X.
    induction X in k, m, j, Hinf |- * using on_free_vars_argument_rect'; constructor.
    all: rc_notin_lift_overflow_aux.
    fold argument_mapi. fold lift_argument.
    induction IHuparams as [|? ? [L M] IHJ]; constructor; eauto.
    split => //; len; rewrite -!Nat.add_assoc.
    + rc_notin_lift_overflow_aux.
    + eapply IHJ; done.
  Qed.

  Ltac rc_notin_arg_lift_context_aux := try solve [
        eapply Alli_mapi; tea; cbn; intros; apply rc_notin_lift_context; done
      | eapply All_map, All_impl; tea; cbn; apply rc_notin_lift_context; done
      | apply rc_notin_lift_context; done
    ].

  Definition rc_notin_arg_lift_context Γ1 Γ2 n arg :
  rc_notin_argument_bool Γ1 n arg -> rc_notin_argument_bool (Γ1 ++ Γ2) n (lift_argument #|Γ2| n arg).
  Proof.
    intros X; induction X using on_free_vars_argument_rect'; constructor => //=; len.
    all: rc_notin_arg_lift_context_aux.
    fold argument_mapi. induction IHuparams; len; constructor; eauto => //=.
    destruct px. split => //=; rc_notin_arg_lift_context_aux.
  Qed.

  Ltac rc_notin_arg_lift_binder_aux := try solve [
        eapply Alli_mapi; mtea; cbn; intros ? ?; rewrite -!Nat.add_assoc; apply rc_notin_lift_binder; done
      | eapply All_map, All_impl; mtea; cbn; intros ? ?; rewrite -!Nat.add_assoc; apply rc_notin_lift_binder; done
      | apply rc_notin_lift_binder; done
    ].

  Definition rc_notin_arg_lift_binder {Γ k n arg} :
    rc_notin_argument_bool Γ k arg -> rc_notin_argument_bool Γ (n + k) (lift_argument n k arg).
  Proof.
    unfold rc_notin_bool.
    intros X; revert n; induction X using on_free_vars_argument_rect'; constructor => //=; len.
    all: rc_notin_arg_lift_binder_aux.
    fold argument_mapi. induction IHuparams; len; constructor; eauto => //=.
    destruct px. split => //=; rc_notin_arg_lift_binder_aux. len.
    replace (n + nb_binders + #|largs| + #|x.1|) with (n + (nb_binders + #|largs| + #|x.1|)) by lia.
    apply h.
  Qed.

  Ltac rc_notin_arg_subst_aux := try solve [
        eapply Alli_mapi; mtea; cbn; intros ? ? L; rewrite -!Nat.add_assoc;
        eapply on_free_vars_subst => //; eapply_eq L => //
      | eapply All_map, All_impl; mtea; cbn; intros ? L; rewrite -!Nat.add_assoc;
        eapply on_free_vars_subst => //; eapply_eq L => //
      | eapply on_free_vars_subst => //
    ].

  Definition rc_notin_arg_subst {Γ n above sub arg} :
    rc_notin_argument_bool Γ (n + above + #|sub|) arg ->
    All (rc_notin_bool Γ n) sub ->
    rc_notin_argument_bool Γ (n + above) (argument_mapi (subst sub) above arg).
  Proof.
    intros X. remember (n + above + #|sub|) as p eqn:Heqp. revert n above Heqp.
    induction X using on_free_vars_argument_rect'; intros n above ->; constructor => //=; len.
    all: rc_notin_arg_subst_aux.
    fold argument_mapi. induction IHuparams; len; constructor; eauto => //=.
    destruct px. split => //=; rc_notin_arg_subst_aux. len.
    rewrite -!Nat.add_assoc. apply h => //.
  Qed.

  Definition All_telescope_rc_notin_lax_false Q k l :
    map check_lax l = repeat false #|l| ->
    All (on_free_vars_argument Q k) l ->
    All_telescope (fun Γ arg => ~~ check_lax arg -> rc_notin_argument_bool (map check_lax Γ) 0 arg) l.
  Proof.
    induction l; cbn. constructor.
    intros [= lax_a lax_l] wdal. inversion wdal.
    change (a::l) with ([a] ++ l). apply All_telescope_app_inv.
    - apply All_telescope_singleton.
      change (map check_lax _) with (repeat false 0).
      intros. rewrite -> (argument_strict lax_a) in *.
      constructor. apply on_free_vars_argument_free in X.
      eapply rc_notin_false => //.
    - eapply All_telescope_impl2. 1: eapply IHl => //. eapply All_to_All_telescope; tea.
      cbn. intros Γ arg rc_notin_arg wd_arg lax_arg. rewrite lax_a.
      change (false :: _) with (repeat false 1 ++ map check_lax Γ).
      apply rc_notin_argument_app.
      * eapply rc_notin_argument_false => //.
      * apply rc_notin_arg. done.
  Qed.

  Definition rc_notin_argument Γ :=
    rc_notin_argument_bool (map check_lax Γ).

  Definition andP {A} (P Q : A -> bool) := fun a => P a && Q a.
  Notation "P &&p Q" := (andP P Q) (at level 50).

  (* Context of the mutual inductive block *)
  Context (nb_block : nat).

  Context (uparams_b : list (context_decl * bool)).
  Definition uparams : context := map fst uparams_b.
  Notation nb_uparams := #|uparams_b|.

  Context (nuparams : context).
  Notation nb_nuparams := #|nuparams|.

  Definition params : context := uparams ,,, nuparams.


  (* Check for inds and strictly positive uparams with only that in the cxt *)
  Definition ind_notinP : nat -> bool :=
    fun n => if #|uparams_b| <=? n then false else true.

  Definition ind_notin pos_arg : term -> bool :=
    on_free_vars (shiftnP pos_arg ind_notinP).

  Definition sp_uparams_notinP : nat -> bool :=
    fun n => ~~ ((nth n (List.rev uparams_b) (mkdecl (mkBindAnn nAnon Relevant) None (tVar "impossible case"), false)).2).

  (* Definition sp_uparams_notinP : nat -> bool :=
  fun n => if nth_error (List.rev uparams_b) n is Some (_, b)
          then negb b else true. *)

  Definition sp_uparams_notin pos_arg : term -> bool :=
    on_free_vars (shiftnP pos_arg sp_uparams_notinP).

  Definition isup_notinP : nat -> bool :=
    ind_notinP &&p sp_uparams_notinP.

  Definition isup_notin pos_arg : term -> bool :=
    on_free_vars (shiftnP pos_arg isup_notinP).

  Definition tRel_is_sp_uparams : nat -> bool :=
  fun k => nth k (map snd (List.rev uparams_b)) false.

  Definition isup_notin_below k i :
    i <? k -> isup_notin k (tRel i).
  Proof.
    cbn. unfold shiftnP. now intros ->.
  Qed.

  Definition shiftnP_ltb k P i :
    i <? k -> shiftnP k P i.
  Proof.
    unfold shiftnP. now intros ->.
  Qed.

  Definition shiftnP_lt k P i :
    i < k -> shiftnP k P i.
  Proof.
    intros H. apply shiftnP_ltb. now apply Nat.ltb_lt.
  Qed.



  (* Positivity part *)

  (* An argument is positive if:
    - It is a term t and ind + sp_uparams ∉ x1 ... xn
    - It is of the form ∀ x1 ... xn, A / Ind i / tInd, x1 ... xn and,
      1. ind + sp_uparams ∉ x1 ... xn
      2. It ends with:
        - a lax postitive uniform parameter A y1 ... yn, and ind + sp_uparams ∉ y1 ... yn
        - one of the inductive block (Ind i) y1 ... yn, and ind + sp_uparams ∉ y1 ... yn
        - a nested occurence, the instantiation of the sp uparams is positive the others is not nested,
          ind + sp_uparams ∉ instantiations of nuparams and indices
  *)



  (* this function does not need to be specified *)
  Parameter cdecl_to_arity : context_decl -> nat.

  Definition uparams_nb_args : list nat :=
    map (fun x => cdecl_to_arity x.1) uparams_b.

  Reserved Notation " lax |> size_cxt |arg+> t " (at level 50, t at next level).

  (* Unset Elimination Schemes. *)

  Section PosArg.

  Context (Γ : list bool).
  Notation nb_args := #|Γ|.

  Notation size_cxt := (nb_nuparams + nb_args).

  (* size_cxt := nb_ binders already seen => nested case *)
  Inductive positive_argument (lax : bool) (nb_binders : nat) : argument -> Type :=
  | pos_arg_is_free t :
    isup_notin (size_cxt + nb_binders) t ->
    lax |> nb_binders |arg+> arg_is_free t

  | pos_arg_is_sp_uparams largs k inst_args :
    lax = true ->
    (* it is a uparams *)
    k < #|uparams_b| ->
    (* which is positive *)
    nth k (map snd (List.rev uparams_b)) false ->
    (* and fully applied *)
    nth k (List.rev uparams_nb_args) 0 = #|inst_args| ->
    (* ind + sp_uparams ∉ largs + args *)
    Alli isup_notin (size_cxt + nb_binders) largs ->
    All (isup_notin (size_cxt + nb_binders + #|largs|)) inst_args ->
    (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
      (* rc_notin ∉ largs + args *)
      Alli (rc_notin_bool Γ) (nb_binders) largs ->
      All ((rc_notin_bool Γ) (nb_binders + #|largs|)) inst_args ->
    (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
    (* -------------------------------------------------------------- *)
    lax |> nb_binders |arg+> arg_is_sp_uparam largs k inst_args

  | pos_arg_is_ind largs pos_indb inst_nuparams_indices :
    lax = true ->
    (* pos_indb corresponds to an inductive block *)
    pos_indb < nb_block ->
    (* ind + sp_uparams ∉ largs *)
    Alli isup_notin (size_cxt + nb_binders) largs ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (isup_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices ->
    (* -------------------------------------------------------------- *)
    lax |> nb_binders |arg+> arg_is_ind largs pos_indb inst_nuparams_indices

  | pos_arg_is_nested largs kname pos_ind u inst_uparams inst_nuparams_indices mdecl :
    lax = true ->
    (* ind + sp_uparams ∉ largs *)
    Alli isup_notin (size_cxt + nb_binders) largs ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (isup_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices ->
    (* declared mdecl + pos_ind *)
    lookup_minductive E kname = Some mdecl ->
    pos_ind < #|ind_bodies mdecl| ->
    (* inst_uparams are positive *)
    All2 (fun x y =>
      (* fully applied ensured by typing *)
      (#|x.1| = cdecl_to_arity y.1)
      (* llargs are free *)
      * Alli (isup_notin) (size_cxt + nb_binders + #|largs|) x.1
      (* args are pos lax or strict depending if you can nest or not *)
      * positive_argument y.2 (nb_binders + #|largs| + #|x.1|) x.2
    ) inst_uparams (List.rev (ind_uparams mdecl))
    ->
    (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
        (* rc_notin ∉ largs + inst_uparams *)
        Alli (rc_notin_bool Γ) nb_binders largs ->
        All (fun p => Alli (rc_notin_bool Γ) (nb_binders + #|largs|) p.1
                      * rc_notin_argument_bool Γ (nb_binders + #|largs| + #|p.1|) p.2)
              inst_uparams ->
    (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
    (* -------------------------------------------------------------- *)
    lax |> nb_binders |arg+> arg_is_nested largs (mkInd kname pos_ind) u
                              inst_uparams inst_nuparams_indices

  where "lax |> nb_binders |arg+> t " := (positive_argument lax nb_binders t) : type_scope.

  Inductive All2_param1 {A B R} (PR : forall a b, R a b -> Type) : forall {lA lB}, All2 R lA lB -> Type :=
  | All2_nil_param1 : All2_param1 PR ( @All2_nil A B R)
  | All2_cons_param1 : forall (x : A) (y : B) (l : list A) (l' : list B),
                forall (r : R x y), PR _ _ r ->
                forall (al : All2 R l l'), All2_param1 PR al ->
                All2_param1 PR (All2_cons r al).

  Definition positive_argument_rect'
    (P : forall {lax nb_binders arg}, positive_argument lax nb_binders arg -> Type)
    (P_arg_is_free :
        forall lax nb_binders (t : term) (i : isup_notin (size_cxt + nb_binders) t),
        (* ------------------------ *)
        P (pos_arg_is_free lax nb_binders t i)
      )
    (P_arg_is_sp_uparams :
        forall lax nb_binders (largs : list term) (k : nat) (inst_args : list term)
        (e : lax = true) (pos_k : k < #|uparams_b|)
        (is_sp : nth k (map snd (List.rev uparams_b)) false)
        (fapp : nth k (List.rev uparams_nb_args) 0 = #|inst_args|)
        (isup_notin_largs : Alli isup_notin (size_cxt + nb_binders) largs)
        (isup_notin_args : All (isup_notin (size_cxt + nb_binders + #|largs|)) inst_args)
        (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
          (rc_notin_largs : Alli (rc_notin_bool Γ) (nb_binders) largs)
          (rc_notin_args : All ((rc_notin_bool Γ) (nb_binders + #|largs|)) inst_args)
        (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
        ,
        (* ------------------------ *)
        P (pos_arg_is_sp_uparams lax nb_binders largs k inst_args e pos_k is_sp fapp
            isup_notin_largs isup_notin_args rc_notin_largs rc_notin_args)
      )
    (P_arg_is_ind :
        forall lax nb_binders (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
        (e : lax = true) (pos_ind : pos_indb < nb_block)
        (isup_notin_largs : Alli isup_notin (size_cxt + nb_binders) largs)
        (isup_notin_args : All (isup_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices),
        (* ------------------------ *)
        P (pos_arg_is_ind lax nb_binders largs pos_indb inst_nuparams_indices
              e pos_ind isup_notin_largs isup_notin_args)
      )
    (P_arg_is_nested:
        forall lax nb_binders (largs : list term) (kname : kername) (pos_ind : nat) (u : Instance.t)
        (inst_uparams : list (list term × argument)) (inst_nuparams_indices : list term)
        (mdecl : mutual_inductive_body)
        (e : lax = true)
        (isup_notin_largs : Alli isup_notin (size_cxt + nb_binders) largs)
        (isup_notin_instance : All (isup_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices)
        (ind_env_defined : lookup_minductive E kname = Some mdecl)
        (ind_pos_defined : pos_ind < #|ind_bodies mdecl|)
        (pos_nested :
            All2 (fun (x : list term × argument) (y : context_decl × bool) =>
              (#|x.1| = cdecl_to_arity y.1
              × Alli (fun (pos_arg : nat) (x0 : term) => isup_notin pos_arg x0) (size_cxt + nb_binders + #|largs|) x.1)
              * (positive_argument y.2 (nb_binders + #|largs| + #|x.1|) x.2))
            inst_uparams (List.rev (ind_uparams mdecl)))
        (Ppos_nested : All2_param1 (fun x y r => P r.2) pos_nested)
        (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
          (rc_notin_largs : Alli (rc_notin_bool Γ) nb_binders largs)
          (rc_notin_instance : All (fun p => Alli (rc_notin_bool Γ) (nb_binders + #|largs|) p.1
                              * rc_notin_argument_bool Γ (nb_binders + #|largs| + #|p.1|) p.2) inst_uparams)
        (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
        ,
        (* ------------------------ *)
        P (pos_arg_is_nested lax nb_binders largs kname pos_ind u inst_uparams inst_nuparams_indices mdecl
              e isup_notin_largs isup_notin_instance ind_env_defined ind_pos_defined
              pos_nested rc_notin_largs rc_notin_instance)
      )
    : forall lax nb_binders arg (p : positive_argument lax nb_binders arg), P p.
  Proof.
    fix rec 4.
    intros lax nb_binders arg p.
    destruct p as [ | | | ? ? ? ? ? ? ? ? ? ? ? ? pos_nested rc_notin_largs rc_notin_instance ].
    - apply P_arg_is_free.
    - apply P_arg_is_sp_uparams.
    - apply P_arg_is_ind.
    - apply P_arg_is_nested.
      clear rc_notin_instance.
      induction pos_nested; constructor; cbn.
      destruct x; destruct y; cbn.
      apply rec. apply IHpos_nested.
  Defined.

  Definition positive_argument_false {nb_binders arg} :
    positive_argument false nb_binders arg -> check_lax arg = false.
  Proof.
    intros H; destruct H; cbn; lia.
  Qed.

  Definition positive_argument_strict {nb_binders arg} :
    positive_argument false nb_binders arg ->
    ∑ t, ((isup_notin (size_cxt + nb_binders) t) * (arg = arg_is_free t)).
  Proof.
    intro k; inversion k.
    1: eauto.
    all : lia.
  Qed.

  End PosArg.

  Ltac pos_arg_decr := try solve [
      eapply Alli_impl; tea; intros; eapply rc_notin_decrease; tea
    | eapply All_impl; tea; intros; eapply rc_notin_decrease; tea
  ].

  Definition positive_argument_decrease1 {l l' b nb_binders arg} :
    All2 (fun a b => is_true (~~ a) -> is_true (~~ b)) l l' ->
    positive_argument l b nb_binders arg ->
    positive_argument l' b nb_binders arg.
  Proof.
  intros imp_ll' pos_arg.
  pose Hll' := All2_length imp_ll'.
  induction pos_arg using positive_argument_rect'; econstructor; rewrite -?Hll' => //=.
  all: pos_arg_decr.
    - induction Ppos_nested; cbn in *; constructor.
      * destruct r as [ []]. repeat split => //=.
      * apply IHPpos_nested. inversion rc_notin_instance. eapply All_impl; tea; done.
    - eapply All_impl; tea. intros ? []. repeat split => //=; pos_arg_decr.
      eapply rc_notin_argument_decrease; tea.
  Qed.

  Definition positive_argument_increase2 {l b nb_binders arg} :
    positive_argument l false nb_binders arg ->
    positive_argument l b nb_binders arg.
  Proof.
    intros k; inversion k; only 2-4: lia.
    apply pos_arg_is_free => //.
  Qed.



  (* A constructor is postive when:
     1. All of its arguments are positive
     2. The return indices do not contain the inductives nor the sp_uparams
  *)
  Definition PosArgBool lb arg :=
    (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
      (~~ check_lax arg -> rc_notin_argument_bool lb 0 arg) *
    (** END ADDITION NO INDUCTIVE-INDUCTIVE **)
    positive_argument lb true 0 arg.

  Definition PosArg Γ := PosArgBool (map check_lax Γ).

  Definition positive_constructor (ctor : constructor_body) : Type :=
      All_telescope PosArg ctor.(cstr_args)
   * All (isup_notin (#|nuparams| + #|ctor.(cstr_args)|)) ctor.(cstr_indices).


(* A inductive body is positive when:
  - All its constructors are postive
  - The indices do not mention the sp uparams. This restriction is needed to
    ensure that the associated mutual type is not inductive-inductive
  *)
  Definition positive_indices indices : Type :=
    Alli (isup_notin) #|nuparams| (map decl_type (List.rev indices)).

  Definition positive_one_inductive_body (indb : one_inductive_body) : Type :=
    All positive_constructor indb.(ind_ctors) *
    (** BEGIN ADDITION NO INDUCTIVE-INDUCTIVE **)
      positive_indices indb.(ind_indices).
    (** END ADDITION NO INDUCTIVE-INDUCTIVE **)


End PositiveIndBlock.

Definition positive_mutual_inductive_body (mdecl : mutual_inductive_body) : Type :=
    Alli (isup_notin mdecl.(ind_uparams)) 0 (terms_of_cxt mdecl.(ind_nuparams))
  * All (positive_one_inductive_body #|mdecl.(ind_bodies)| mdecl.(ind_uparams)
        mdecl.(ind_nuparams)) mdecl.(ind_bodies).


Arguments positive_argument_strict {_ _ _ _ _ _}.

(* Increasing the number of inductive block preserve positivity *)
Definition pos_arg_inc {nb_block up nup Γ lax nb_binders arg} k :
  positive_argument nb_block up nup Γ lax nb_binders arg ->
  positive_argument (nb_block + k) up nup Γ lax nb_binders arg.
Proof.
  intros pos_arg. induction pos_arg using positive_argument_rect'.
  - constructor => //.
  - constructor => //.
  - constructor => //.
  - econstructor; tea. clear rc_notin_instance.
    induction Ppos_nested; cbn in *; constructor.
    + destruct r as [[]]; repeat constructor => //.
    + apply IHPpos_nested.
Qed.

Fixpoint pos_ctor_inc {nb_block up nup ctor} k :
  positive_constructor nb_block up nup ctor ->
  positive_constructor (nb_block + k) up nup ctor.
Proof.
  intros [pos_args pos_indices]; split => //.
  eapply All_telescope_impl; tea. cbn.
  intros Γ x [rc_notin_arg pos_arg]. split => //.
  apply pos_arg_inc => //.
Qed.

Fixpoint pos_ctor_inc_le {nb_block up nup ctor} k :
  nb_block <= k ->
  positive_constructor nb_block up nup ctor ->
  positive_constructor k up nup ctor.
Proof.
  intros p%(Arith_base.le_plus_minus_stt _ _); rewrite p.
  apply pos_ctor_inc.
Qed.

Fixpoint pos_idecl_inc {nb_block up nup idecl} k :
  positive_one_inductive_body nb_block up nup idecl ->
  positive_one_inductive_body (nb_block + k) up nup idecl.
Proof.
  intros [pos_ctor pos_indices]; split => //.
  eapply All_impl; tea.
  intros; apply pos_ctor_inc => //.
Qed.

Fixpoint pos_idecl_inc_le {nb_block up pos_arg idecl} k :
  nb_block <= k ->
  positive_one_inductive_body nb_block up pos_arg idecl ->
  positive_one_inductive_body k up pos_arg idecl.
Proof.
  intros p%(Arith_base.le_plus_minus_stt _ _); rewrite p.
  apply pos_idecl_inc.
Qed.

Definition Alli_eq {A} {P : nat -> A -> Type} {n m l} :
  n = m -> Alli P n l -> Alli P m l.
Proof.
  intros -> X; exact X.
Qed.

Ltac pos_arg_unfold :=
  try solve [
      eapply All_up_shift; tea; len
    | eapply Alli_impl; mtea => //=; intros;
      rewrite rc_notin_false_right; try (rewrite !Nat.add_assoc); done
    | eapply All_impl; mtea => //=; intros;
      rewrite rc_notin_false_right; try (rewrite !Nat.add_assoc); done
    | eapply Alli_eq; mtea; len
  ].

Definition pos_arg_notin_unfold {A} {nb_block up nup Γ lax nb_binders} {tm : list A} arg :
  positive_argument nb_block up nup Γ lax (#|tm| + nb_binders) arg ->
  positive_argument nb_block up nup (Γ ++ repeat false #|tm|) lax nb_binders arg.
Proof.
  remember (#|tm| + nb_binders) as p eqn:Heqp.
  intros pos_arg. revert nb_binders Heqp.
  induction pos_arg using positive_argument_rect'; intros; econstructor; len => //=.
  all: subst; pos_arg_unfold.
  + eapply on_free_vars_up_shift; tea; len.
  + clear rc_notin_instance.
    induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
          [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; repeat split => //; pos_arg_unfold.
    apply_eq pos_arg => //.
  + eapply (All_impl rc_notin_instance).
    intros x [K L]. split => //=; pos_arg_unfold.
    unfold rc_notin_argument_bool. eapply on_free_vars_argument_impl_shiftnP; tea.
    intros j M. eapply shiftnP_impl.
    - intros i P. rewrite rc_notinP_false_right. exact P.
    - rewrite shiftnP_add. apply_eq M; len.
Qed.

Ltac pos_lift_arg_aux := try solve [
    eapply Alli_mapi; mtea; intros i t;
    eapply on_free_vars_lift_eq; tea; len; rewrite !Nat.add_assoc; (reflexivity || by len)
  | eapply All_map, All_impl; mtea; cbn; len; intros t;
    eapply on_free_vars_lift_eq; tea; len; rewrite !Nat.add_assoc; (reflexivity || by len)
  | eapply on_free_vars_lift_eq; tea; len; rewrite !Nat.add_assoc; (reflexivity || by len)
  | eapply Alli_mapi; mtea; intros; eapply rc_notin_lift_context => //
  | eapply All_map, All_impl; mtea; intros; eapply rc_notin_lift_context => //
].

Definition pos_lift_arg_context {nb_block up nup Γ1 Γ2 lax} arg k :
  positive_argument nb_block up nup Γ1 lax k arg ->
  positive_argument nb_block up nup (Γ1 ++ Γ2) lax k (lift_argument #|Γ2| k arg).
Proof.
  intros pos_arg; induction pos_arg using positive_argument_rect'.
  all: econstructor; tea; len; pos_lift_arg_aux.
  all : fold argument_mapi.
   + clear rc_notin_instance.
    induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
            [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; len; repeat split => //. pos_lift_arg_aux.
  + eapply All_map, (All_impl rc_notin_instance).
    intros [] []; cbn in *; split => //; pos_lift_arg_aux. len.
    eapply rc_notin_arg_lift_context => //.
Qed.

Definition pos_lift_arg_context_eq {nb_block up nup Γ1 Γ2 lax p q} arg k :
  p = k ->
  q = #|Γ2| ->
  positive_argument nb_block up nup Γ1 lax k arg ->
  positive_argument nb_block up nup (Γ1 ++ Γ2) lax p (lift_argument q k arg).
Proof.
  intros -> ->. apply pos_lift_arg_context => //.
Qed.

Ltac pos_lift_arg_binders_aux := try solve [
    eapply Alli_mapi; mtea; intros i t;
    eapply on_free_vars_lift_eq; tea; len; rewrite !Nat.add_assoc; (reflexivity || by len)
  |  eapply All_map, All_impl; mtea; cbn; len; intros t;
    eapply on_free_vars_lift_eq; tea; len; rewrite !Nat.add_assoc; (reflexivity || by len)
  |  eapply on_free_vars_lift_eq; tea; len; rewrite !Nat.add_assoc; (reflexivity || by len)
  | eapply Alli_mapi; mtea; intros; rewrite -Nat.add_assoc; eapply rc_notin_lift_binder => //
  | eapply All_map, All_impl; mtea; intros; rewrite -Nat.add_assoc; eapply rc_notin_lift_binder => //
].

Definition pos_lift_arg_binders {nb_block up nup Γ lax n k} arg :
  positive_argument nb_block up nup Γ lax k arg ->
  positive_argument nb_block up nup Γ lax (n + k) (lift_argument n k arg).
Proof.
  intro pos_arg. revert n.
  induction pos_arg using positive_argument_rect'; intros n.
  all: econstructor; tea; len; pos_lift_arg_binders_aux.
  all : fold argument_mapi.
   + clear rc_notin_instance.
    induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
            [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; len; repeat split => //; pos_lift_arg_binders_aux.
    replace (n + nb_binders + #|largs| + #|llargs|) with
      (n + (nb_binders + #|largs| + #|llargs|)) by lia.
    eapply pos_arg.
  + eapply All_map, (All_impl rc_notin_instance).
    intros [] []; cbn in *; len; split => //; pos_lift_arg_binders_aux.
    - eapply (Alli_mapi a0). intros ? ?. rewrite -!Nat.add_assoc. eapply rc_notin_lift_binder => //.
    - replace (n + nb_binders + #|largs| + #|l|) with (n + (nb_binders + #|largs| + #|l|)) by lia.
      eapply rc_notin_arg_lift_binder => //.
Qed.

Ltac pos_subst_arg_aux := try solve [
    intros; rewrite !Nat.add_assoc; eapply on_free_vars_subst_eq; tea; len
  | eapply Alli_mapi; mtea => //=; intros; eapply on_free_vars_subst_eq; tea; len
  | eapply All_map, All_impl; mtea => //=; intros; eapply on_free_vars_subst_eq; tea; len
].

Definition pos_subst_argument {nb_block up nup Γ lax nb_binders} sub above arg  :
  positive_argument nb_block up nup Γ lax (nb_binders + above + #|sub|) arg ->
  All (isup_notin up ((#|nup| + #|Γ|) + nb_binders)) sub ->
  All (on_free_vars (shiftnP nb_binders (rc_notinP Γ))) sub ->

  positive_argument nb_block up nup Γ lax (nb_binders + above) (subst_argument sub above arg).
Proof.
  intros pos_arg. remember (nb_binders + above + #|sub|) as p eqn:Heqp.
  revert nb_binders above Heqp.
  induction pos_arg using positive_argument_rect'; intros q above -> Hisup Hnotin.
  all: econstructor; tea; len; pos_subst_arg_aux.
  all: fold argument_mapi.
   + clear rc_notin_instance.
    induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
            [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; len; repeat split => //; pos_subst_arg_aux.
    rewrite -!Nat.add_assoc. eapply pos_arg => //.
  + eapply All_map, (All_impl rc_notin_instance).
    intros [] []; cbn in *; len; split => //; pos_subst_arg_aux.
    rewrite -!Nat.add_assoc. eapply rc_notin_arg_subst => //.
    apply_eq r => //.
Qed.

Definition pos_subst_argument_eq {nb_block up nup Γ lax nb_binders} sub above arg p q j :
  p = nb_binders + above + #|sub| ->
  q = nb_binders + above ->
  j = #|nup| + #|Γ| + nb_binders ->
  All (isup_notin up j) sub ->
  All (rc_notin_bool Γ nb_binders) sub ->
  positive_argument nb_block up nup Γ lax p arg ->
  positive_argument nb_block up nup Γ lax q (subst_argument sub above arg).
Proof.
  intros -> -> -> ? ? ?. apply pos_subst_argument. all: tea.
Qed.


(* *** View to Env *** *)

Section ViewToEnv.
  Context (nb_block : nat).
  Context (uparams_b : list (context_decl * bool)).
  Notation nb_uparams := #|uparams_b|.

  (* size_cxt := param + nuparam + args already seen *)
  Fixpoint argument_to_term (size_cxt : nat) (arg : argument) : term :=
    match arg with
    | arg_is_free t => t
    | arg_is_sp_uparam largs pos_uparams args =>
        let rel_uparams := (size_cxt - pos_uparams - 1) + #|largs| in
        it_tProd largs (mkApps (tRel rel_uparams) args)
    | arg_is_ind largs pos_indb inst_nuparams_indices =>
        let rel_indb := size_cxt + (nb_block - pos_indb - 1) + #|largs|in
        let up := tRels ((size_cxt - nb_uparams -1) + #|largs|) nb_uparams in
        it_tProd largs (mkApps (tRel rel_indb) (up ++ inst_nuparams_indices))
    | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
        let term_uparams := map (fun ' (llargs, arg) =>
            it_tLambda llargs (argument_to_term (size_cxt + #|largs| + #|llargs|) arg)
          ) inst_uparams in
        it_tProd largs (mkApps (tInd ind u) (term_uparams ++ inst_nuparams_indices))
    end.

  Definition arguments_to_context (size_cxt : nat) (args : list argument) : context :=
    List.rev (mapi (fun i t => vassAR (argument_to_term (size_cxt + i) t)) args).

  Context (nuparams : context).
  Notation nb_nuparams := #|nuparams|.

  (* size_cxt := param + nuparam + args *)
  Definition return_type (size_cxt : nat) (indices : list term) : term :=
    let rel_indb := size_cxt + (nb_block - size_cxt - 1) in
    let up_nup := tRels (size_cxt - nb_uparams - nb_nuparams -1) (nb_uparams + nb_nuparams) in
    mkApps (tRel rel_indb) (up_nup ++ indices).

  (* Definition view_to_env_constructor : ViewInductive.constructor_body -> PCUICEnvironment.constructor_body :=
    fun ' (ViewInductive.mkViewCtor args indices) => {|
      PCUICEnvironment.cstr_name := todo;
      PCUICEnvironment.cstr_args := arguments_to_context (nb_uparams + nb_nuparams) args;
      PCUICEnvironment.cstr_indices := indices;
      PCUICEnvironment.cstr_type :=
        it_mkProd_or_LetIn (map fst uparams_b ++ nuparams ++
          arguments_to_context (nb_uparams + nb_nuparams) args)
          (return_type (nb_uparams + nb_nuparams + #|args|) indices)
        ;
      PCUICEnvironment.cstr_arity := #|args|
    |}. *)

  (* Print PCUICEnvironment.mutual_inductive_body. *)

  (* Definition view_to_env_indb : ViewInductive.one_inductive_body -> PCUICEnvironment.one_inductive_body :=
    fun ' (ViewInductive.mkViewInd name indices s kelim ctors relev) => {|
      PCUICEnvironment.ind_name := name;
      PCUICEnvironment.ind_indices := indices;
      PCUICEnvironment.ind_sort := s;
      PCUICEnvironment.ind_type := it_mkProd_or_LetIn (map fst uparams_b ++ nuparams ++ indices) (tSort s);
      PCUICEnvironment.ind_kelim := kelim;
      PCUICEnvironment.ind_ctors := map view_to_env_constructor ctors ;
      PCUICEnvironment.ind_projs := todo;
      PCUICEnvironment.ind_relevance := relev;
    |}. *)

  End ViewToEnv.

  (* Definition view_to_env_mut : ViewInductive.mutual_inductive_body -> PCUICEnvironment.mutual_inductive_body :=
    fun ' (ViewInductive.mkViewMut fin up nup indb u var) => {|
      PCUICEnvironment.ind_finite := fin;
      PCUICEnvironment.ind_npars := todo;
      PCUICEnvironment.ind_params := todo;
      PCUICEnvironment.ind_bodies := map (view_to_env_indb #|indb| up nup) indb ;
      PCUICEnvironment.ind_universes := u;
      PCUICEnvironment.ind_variance := var
    |}. *)

End ViewInductive.
