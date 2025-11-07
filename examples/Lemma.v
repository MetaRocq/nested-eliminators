(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst.

Ltac multi_eassumption :=
  multimatch goal with
  | [h : ?t |- _ ] => exact h
  end.

Ltac mtea := try multi_eassumption.

Ltac apply_eq H :=
  let feq := fresh "feq" in
  eassert (feq : _ = _); only 2: (rewrite <- feq; apply H); only 1 : f_equal.

Ltac eapply_eq H :=
  let feq := fresh "feq" in
  eassert (feq : _ = _); only 2: (rewrite <- feq; eapply H); only 1 : f_equal.


(* Else *)
Definition map_xpred0 {A} (l : list A) : map xpred0 l = repeat false #|l|.
  Proof.
    induction l; cbn; f_equal; eauto.
  Qed.

(* Functions on terms *)
Definition test_tVar := [tVar "foo1"; tVar "foo2"; tVar "foo3"].

Definition vassAR : term -> context_decl :=
  fun t => vass (mkBindAnn nAnon Relevant) t.

Definition cxt_of_terms : list term -> context :=
  fun l => List.rev (map vassAR l).

Definition terms_of_cxt : context -> list term :=
  fun Γ => map decl_type (List.rev Γ).

Definition it_binder binder : list term -> term -> term :=
  fun l t => fold_right (fun t u => binder (mkBindAnn nAnon Relevant) t u) t l.

Definition it_tProd : list term -> term -> term :=
fun l t => it_mkProd_or_LetIn (List.rev (map (fun x => vass (mkBindAnn nAnon Relevant) x) l)) t.

Definition it_tLambda : list term -> term -> term :=
fun l t => it_mkLambda_or_LetIn (List.rev (map (fun x => vass (mkBindAnn nAnon Relevant) x) l)) t.

Definition tRels (start length : nat) : list term :=
  List.rev (map tRel (seq start length)).

Definition eq_prod {A B} (x : A * B) y z : x = (y,z) -> (fst x = y) * (snd x = z).
Proof. destruct x; cbn. now intros [=]. Qed.


(* All *)
Definition All_sym_inv : forall {A B C : Type} (f : A -> C) (g : B -> C)
  l l',
  All2 (fun y x => f x = g y) l' l ->
  All2 (fun x y => f x = g y) l  l'.
Proof.
  intros * X; induction X; constructor; eauto.
Qed.

Definition All_impl2 {A P Q1 Q2} {l : list A} :
  All Q1 l -> All Q2 l ->
  (forall x, Q1 x -> Q2 x -> P x) ->
  All P l.
Proof.
  intros H; induction H; intros q; inversion q; constructor; eauto.
Qed.

Definition All_pointwise_map {A P} {f : nat -> A} {start length} :
  (forall i, start <= i -> i < start + length -> P (f i)) ->
    All P (map f ((seq start length))).
  Proof.
    revert start; induction length; cbn; intros start H; constructor.
    - apply H; lia.
    - apply IHlength. intros. apply H; lia.
  Qed.

Definition All_rev_pointwise_map {A P} {f : nat -> A} {start length} :
(forall i, start <= i -> i < start + length -> P (f i)) ->
  All P (List.rev (map f ((seq start length)))).
Proof.
  revert start; induction length; cbn [seq map]; intros start H.
  + constructor.
  + cbn. apply All_app_inv.
    - apply IHlength. intros. apply H; lia.
    - repeat constructor. apply H; lia.
Qed.

Definition All_nth {A} P (l : list A) a k :
  k < #|l| ->
  All P l -> P (nth k l a).
Proof.
  intros p x; induction x in k, p |- *; cbn in * => //.
  - exfalso. inversion p.
  - destruct k; cbn in * => //.
    apply IHx. lia.
Qed.

Definition All_rev (A : Type) (P : A -> Type) (l : list A) :
  All P l -> All P (List.rev l).
Proof.
  intros x; induction x; cbn ; eauto. apply All_app_inv; eauto.
Qed.

Definition All_to_Alli {A} {P : A -> Type} {l} n :
  All P l -> Alli (fun _ => P) n l.
Proof.
  intros X; induction X in n |- *; constructor; eauto.
Qed.

(* All2 *)
Definition All2_nth {A B} P (lA : list A) (lB : list B) k a b :
  k < #|lA| ->
  All2 P lA lB -> P (nth k lA a) (nth k lB b).
Proof.
Proof.
  intros p x; induction x in k, p |- *; cbn in * => //.
  - exfalso. inversion p.
  - destruct k; cbn in * => //.
    apply IHx. lia.
Qed.

Fixpoint filter2 {A} (lb : list bool) (l : list A) : list A :=
  match lb, l with
  | [], [] => []
  | true::lb, a::l => a :: filter2 lb l
  | false::lb, a::l => filter2 lb l
  | _, _ => []
  end.

Definition All_filter2 {A} (P : A -> Type) lb l :
  All P l -> All P (filter2 lb l).
Proof.
  intros X; induction X in lb |- *; destruct lb as [|[] lb]; cbn;
  try constructor => //; auto.
Qed.


(* Alli *)
Definition Alli_impl {A : Type} {P Q : nat -> A -> Type} {l : list A} {n m : nat}:
  Alli Q n l -> (forall i x, Q (n + i) x -> P (m + i) x) -> Alli P m l.
Proof.
  intros x f; induction x in m, f|- *; cbn; constructor.
  - rewrite -(Nat.add_0_r m). apply f. rewrite Nat.add_0_r //.
  - apply IHx. cbn. intros. rewrite -Nat.add_succ_r. apply f. rewrite Nat.add_succ_r //.
Qed.

Definition Alli_impl2 {A : Type} {Q1 Q2 P : nat -> A -> Type} {n1 n2 m l} :
  Alli Q1 n1 l -> Alli Q2 n2 l ->
  (forall i x, Q1 (i + n1) x -> Q2 (i + n2) x -> P (i + m) x) ->
  Alli P m l.
Proof.
  intros X.
  induction X in n2,m |-; intros p2 H; inversion p2; constructor.
  + apply H with (i := 0) => //.
  + eapply IHX; tea. intros i x; rewrite !Nat.add_succ_r. eapply H with (i := S i).
Qed.

Definition Alli_map {A B P} {f : A -> B} {n l} :
  Alli (fun i x => P i (f x)) n l ->
  Alli P n (map f l).
Proof.
  intros H; induction H; constructor; eauto.
Qed.

Definition Alli_prod {A P1 P2 n} {l : list A} :
  Alli P1 n l ->  Alli P2 n l -> Alli (fun i n => P1 i n * P2 i n) n l.
Proof.
  intros X; induction X; intros Y; inversion Y; constructor; eauto.
Qed.

Definition Alli_mapi_rec {A B P Q} {f : nat -> A -> B} {n m k l} :
  Alli Q n l ->
  (forall i x, Q (i + n) x -> P (i + m) (f (i + k) x)) ->
  Alli P m (mapi_rec f l k).
Proof.
  intros X.
  induction X in m,k |-; intros H; constructor.
  + apply H with (i := 0) => //.
  + eapply IHX; tea. intros i x; rewrite !Nat.add_succ_r. eapply H with (i := S i).
Qed.

Definition Alli_mapi {A B P Q} {f : nat -> A -> B} {n m l} :
  Alli Q n l ->
  (forall i x, Q (n + i) x -> P (m + i) (f i x)) ->
  Alli P m (mapi f l).
Proof.
  unfold mapi. intros H X.
  eapply Alli_mapi_rec; tea.
  intros. rewrite Nat.add_0_r. rewrite Nat.add_comm. apply X. rewrite Nat.add_comm //.
Qed.

Definition Alli_mapi_rec2 {A B P Q1 Q2} {f : nat -> A -> B} {n1 n2 m k l} :
  Alli Q1 n1 l -> Alli Q2 n2 l ->
  (forall i x, Q1 (i + n1) x -> Q2 (i + n2) x -> P (i + m) (f (i + k) x)) ->
  Alli P m (mapi_rec f l k).
Proof.
  intros X.
  induction X in n2,m,k |-; intros p2 H; inversion p2; constructor.
  + apply H with (i := 0) => //.
  + eapply IHX; tea. intros i x; rewrite !Nat.add_succ_r. eapply H with (i := S i).
Qed.

Definition Alli_mapi2 {A B P Q1 Q2} {f : nat -> A -> B} {n1 n2 m l} :
  Alli Q1 n1 l -> Alli Q2 n2 l ->
  (forall i x, Q1 (n1 + i) x -> Q2 (n2 + i) x -> P (m + i) (f i x)) ->
  Alli P m (mapi f l).
Proof.
  unfold mapi. intros p1 p2 H.
  unshelve eapply (Alli_mapi_rec2 p1 p2).
  intros. rewrite Nat.add_0_r. rewrite Nat.add_comm. apply H.
  all : rewrite Nat.add_comm //.
Qed.

Definition Alli_pointwise_mapi_rec {A P} {f : nat -> A} {n start length} :
  (forall i, start <= i -> i < start + length -> P (n + (i - start)) (f i)) ->
  Alli P n (map f ((seq start length))).
Proof.
  revert n start; induction length; cbn; intros n k H; constructor.
  - apply_eq H; lia.
  - apply IHlength. intros. apply_eq H; lia.
Qed.


(* All Telescope *)
Inductive All_telescope {A : Type} (P : list A -> A -> Type)
  : list A -> Type :=
  | All_telescope_nil : All_telescope P []
  | All_telescope_cons : forall (d : A) (Γ : list A),
      All_telescope P Γ -> P Γ d -> All_telescope P (Γ ++ [d]).

Definition All_telescope_singleton {A : Type} (P : list A -> A -> Type) a :
  P [] a -> All_telescope P [a].
Proof.
  change [a] with ([] ++ [a]). repeat constructor => //.
Qed.

Definition All_telescope_app_inv {A P} {l l' : list A} :
  All_telescope P l -> All_telescope (fun Γ => P (l ++ Γ)) l' -> All_telescope P (l ++ l').
Proof.
  intros x y. revert x. induction y.
  - rewrite app_nil_r //.
  - rewrite app_assoc. constructor; eauto.
Qed.

Definition All_telescope_impl {A : Type} {P Q : list A -> A -> Type} {l : list A} :
  All_telescope P l -> (forall Γ x, P Γ x -> Q Γ x) -> All_telescope Q l.
Proof.
  intros x; induction x; constructor; eauto.
Qed.

Definition All_telescope_map {A B P Q} {f : A -> B} {l} :
  (forall x Γ, Q Γ x -> P (map f Γ) (f x)) ->
  All_telescope Q l -> All_telescope P (map f l).
Proof.
  intros Hf Hl.
  induction Hl. constructor.
  rewrite map_app; cbn.
  apply All_telescope_app_inv => //.
  apply All_telescope_singleton. rewrite app_nil_r.
  apply Hf => //.
Qed.

Definition All_telescope_to_Alli {A} P (l : list A) n :
  Alli P n l ->
  All_telescope (fun Γ => P (n + #|Γ|)) l.
Proof.
  clear.
  intros H. induction H; cbn. 1: constructor.
  change (hd :: tl) with ([hd] ++ tl).
  apply All_telescope_app_inv => //; cbn.
  - apply All_telescope_singleton; cbn. len => //=.
  - eapply All_telescope_impl; tea; cbn. intros.
    rewrite Nat.add_succ_r //.
Qed.

Definition All_telescope_prod {A} P Q (l : list A) :
  All_telescope (fun Γ arg => P Γ arg) l ->
  All_telescope (fun Γ arg => Q Γ arg) l ->
  All_telescope (fun Γ arg => P Γ arg * Q Γ arg) l.
Proof.
  intros H H2. induction H; cbn.
  1: constructor.
  inversion H2. 1: { apply (f_equal ( @length A)) in H1. rewrite length_app in H1; cbn in H1. lia. }
   apply app_inj_tail in H1 as []; subst. constructor; eauto.
Qed.

Definition All_telescope_impl2 {A : Type} {P1 P2 Q : list A -> A -> Type} {l : list A} :
  All_telescope P1 l -> All_telescope P2 l ->
  (forall Γ x, P1 Γ x -> P2 Γ x -> Q Γ x) ->  All_telescope Q l.
Proof.
  intros x; induction x; constructor; eauto; inversion X.
  all: try solve [ apply (f_equal ( @length A)) in H0; len in H0; cbn in H0; try lia ] .
  all: try solve [apply app_inj_tail in H0 as []; subst => //; eauto ].
Qed.

Definition All_to_All_telescope {A : Type} (P : A -> Type) (l : list A) :
  All P l -> All_telescope (fun _ => P) l.
Proof.
  induction 1; only 1 : constructor.
  change (x :: l) with ([x] ++ l).
  apply All_telescope_app_inv => //.
  apply All_telescope_singleton => //.
Qed.

Definition All_to_All_telescope_to_All {A : Type} (P : A -> Type) (l : list A) :
  All_telescope (fun _ => P) l -> All P l.
Proof.
  induction 1; only 1 : constructor.
  apply All_app_inv => //. repeat constructor => //.
Qed.


(* All2 *)
Definition All2_impl2 {A B : Type} {P Q1 Q2} l l':
  All2 Q1 l l' -> All2 Q2 l l' ->
  (forall (x : A) (y : B), Q1 x y -> Q2 x y -> P x y ) ->
    All2 P l l'.
Proof.
  intros X; induction X; cbn; intros Y F; try constructor; inversion Y; subst.
  - apply F; done.
  - apply IHX => //.
Qed.

Definition All2_left_triv {A B : Type} {l : list A} {l' : list B} (P : A -> Type) :
  All P l -> #|l| = #|l'| -> All2 (fun x _ => P x) l l'.
Proof.
  intros X; induction X in l' |- *; cbn; intros Heq.
  - apply eq_sym, length_nil in Heq as ->. constructor.
  - destruct l'; cbn in * => //.
    constructor => //. apply IHX. lia.
Qed.


(* All Check  *)
Inductive All_check {A : Type} (P : list bool -> A -> Type) check lb : list A -> Type :=
| All_check_nil2 : All_check P check lb []
| All_check_cons2 : forall (d : A) (Γ : list A),
    P lb d -> All_check P check (lb ++ [check d]) Γ -> All_check P check lb (d :: Γ).

Definition spec_fold_All_check {X Y} (check : X -> bool) (f : ((list X) * Y) -> X -> ((list X) * Y)) (xs : list X) (y : (list X) * Y)
  (PY : list X * Y -> Type) (PX : list bool -> X -> Type)
  (pos_xs : All_check PX check (map check y.1) xs)
  (pos_y : PY y)
  (length_f : forall y x, map check (f y x).1 = map check y.1 ++ [check x])
  (pos_f : forall y hd, PY y -> PX (map check y.1) hd -> PY (f y hd))
  :
  PY (fold_left f xs y).
Proof.
  remember (map check y.1) as lb eqn:Heqlb.
  revert y Heqlb pos_y.
  induction pos_xs; cbn. 1: easy.
  intros y Heqn pos_y.
  apply IHpos_xs.
  - rewrite length_f Heqn //.
  - apply pos_f => //. rewrite -Heqn => //.
Qed.

Definition All_check_app_inv {A P} check acc (l1 l2 : list A) :
  All_check P check acc l1 ->
  All_check P check (acc ++ map check l1) l2 ->
  All_check P check acc (l1 ++ l2).
Proof.
  intros X; revert l2; induction X; cbn.
  - rewrite app_nil_r. easy.
  - intros l2 H. constructor => //. apply IHX.
    rewrite -app_assoc //.
Qed.

Definition All_telescope_to_All_check {X} P check (l : list X):
  All_telescope (fun Γ => P (map check Γ)) l ->
  All_check P check [] l.
Proof.
  intros H. induction H. constructor.
  apply All_check_app_inv => //.
  cbn. repeat constructor. done.
Qed.

(* list X * list X * y => old_args, new_args, data *)
Definition spec_fold_All_check2 {X Y}
  (* fct *)
  (check : X -> bool)
  (f : ( list X * list X * Y) -> X -> (list X * list X * Y))
  (xs : list X) (acc : list X * list X * Y)
  (* properties *)
  (PAcc : list X * list X * Y -> Type) (PX : list bool -> X -> Type)
  (pos_xs : All_check PX check (map check acc.1.1) xs)
  (pos_acc : PAcc acc)
  (inv_old : forall acc x, (f acc x).1.1 = acc.1.1 ++ [x])
  (pos_f : forall acc hd, PAcc acc -> PX (map check acc.1.1) hd -> PAcc (f acc hd))
  :
  PAcc (fold_left f xs acc).
Proof.
  remember (map check acc.1.1) as n.
  revert acc Heqn pos_acc.
  induction pos_xs; cbn. 1: easy.
  intros acc Heqn pos_acc.
  apply IHpos_xs.
  - rewrite inv_old map_app Heqn //.
  - apply pos_f => //. rewrite -Heqn => //.
Qed.

Definition spec_fold_Alli {X Y} (f : ((list X) * Y) -> X -> ((list X) * Y)) (xs : list X) (y : (list X) * Y)
  (PY : list X * Y -> Type) (PX : nat -> X -> Type)
  (pos_xs : Alli PX #|y.1| xs)
  (pos_y : PY y)
  (length_f : forall y x, #|(f y x).1| = S #|y.1|)
  (pos_f : forall y hd, PY y -> PX #|y.1| hd -> PY (f y hd))
  :
  PY (fold_left f xs y).
Proof.
  remember (#|y.1|) as n.
  revert y Heqn pos_y.
  induction pos_xs; cbn. 1: easy.
  intros y Heqn pos_y.
  apply IHpos_xs.
  - rewrite length_f. lia.
  - apply pos_f => //. rewrite -Heqn => //.
Qed.


From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICOnFreeVarsConv PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
From MetaRocq.PCUIC Require Import BDStrengthening.
From MetaRocq Require Import PCUIC.PCUICExpandLetsCorrectness.




(* Lemma for subst to move *)
Definition on_free_vars_subst P t k i s :
  All (on_free_vars (shiftnP k P)) s ->
  on_free_vars (shiftnP (k + i + #|s|) P) t ->
  on_free_vars (shiftnP (k + i) P) (subst s i t).
Proof.
  intros X%All_forallb H. rewrite Nat.add_comm. rewrite <- shiftnP_add.
  rewrite -(substP_shiftnP_gen _ #|s|).
  apply on_free_vars_subst_gen => //.
  rewrite shiftnP_add. apply_eq H. do 2 f_equal. lia.
Qed.

Definition on_free_vars_subst_eq P k i s m n t :
  m = k + i + #|s| ->
  n = k + i ->
  All (on_free_vars (shiftnP k P)) s ->
  on_free_vars (shiftnP m P) t ->
  on_free_vars (shiftnP n P) (subst s i t).
Proof.
  intros -> ->; apply on_free_vars_subst => //.
Qed.

Definition All_up_shift P n m l :
  n = m ->
  All (on_free_vars (shiftnP n P)) l ->
  All (on_free_vars (shiftnP m P)) l.
Proof.
  intros -> X; exact X.
Qed.

Definition Alli_up_start {A} (P : nat -> A -> Type) n m l :
  n = m ->
  Alli P n l ->
  Alli P m l.
Proof.
  intros -> X; exact X.
Qed.

Definition on_free_vars_up_shift P n m x :
  n = m ->
  on_free_vars (shiftnP n P) x ->
  on_free_vars (shiftnP m P) x.
Proof.
  intros -> X; exact X.
Qed.


Definition unlift_lift p k t :
  on_free_vars (shiftnP k (fun i => ~~ (i <? p))) t ->
  t = lift p k (unlift p k t).
Proof.
  intros X. rewrite lift_rename /unlift (rename_compose _ _ _).
  erewrite rename_ext_cond; only 1: apply eq_sym, rename_ren_id; tea.
  intros i. unfold lift_renaming, unlift_renaming, shiftnP, ren_id.
  repeat (case_inequalities => //=). all: try lia.
Qed.

(* LEMMA ON FREE_VARS *)
Definition on_free_vars_lift0_overflow (P : nat -> bool) k m p t:
  p + k <= m ->
  (forall i, p <= i -> P i) ->
  on_free_vars (shiftnP k P) t ->
  on_free_vars (shiftnP k P) (lift0 m t).
Proof.
  intros Hlt cs ofr_t.
  eapply on_free_vars_lift0.
  unfold addnP. eapply on_free_vars_impl; tea.
  intros.
  unfold shiftnP. case_inequalities => //=.
  apply cs. lia.
Qed.

Definition on_free_vars_lift_overflow (P Q : nat -> bool) k m p j t:
  p + k <= m ->
  (forall i, p <= i -> P i) ->
  on_free_vars Q t ->
  on_free_vars (shiftnP (k + j) P) (lift m j t).
Proof.
  intros Hlt cs wdt.
  erewrite <-(PCUICOnFreeVars.on_free_vars_lift _ _ _ t) in wdt.
  apply on_free_vars_impl with (2 := wdt).
  unfold strengthenP, shiftnP. intros i0.
  repeat case_inequalities => //. 1: lia.
  intros. apply cs => //. lia.
Qed.

Definition on_free_vars_lift (p : nat -> bool) (c n k : nat)
  (t : term) (ft : on_free_vars (shiftnP (c + k) p) t) :
  on_free_vars (shiftnP (c + n + k) p) (lift n k t).
Proof.
  rewrite -Nat.add_assoc Nat.add_comm -shiftnP_add.
  apply on_free_vars_lift_impl.
  rewrite shiftnP_add Nat.add_comm => //.
Qed.

Definition on_free_vars_lift_eq (p : nat -> bool) (a b c n k : nat)
  (t : term) (eaq : a = c + k) (eqb : b = c + n + k) :
  on_free_vars (shiftnP a p) t ->
  on_free_vars (shiftnP b p) (lift n k t).
Proof.
  rewrite eaq eqb. apply on_free_vars_lift.
Qed.

Definition on_free_vars_inst_up (P Q : nat -> bool) k m p t σ:
  p + k <= m ->
  (forall i, p <= i -> P i) ->
  (forall i, on_free_vars Q (σ i)) ->
  on_free_vars (shiftnP k P) t ->
  on_free_vars (shiftnP k P) t.[up m σ].
Proof.
  intros Hlt cs wdf ofr_t.
  eapply on_free_vars_inst; tea.
  rewrite <-(Arith_base.le_plus_minus_r_stt (k + p) m) by lia.
  replace (k + p + (m - (k + p))) with (k + (p + (m - (k + p)))) by lia.
  intros. rewrite -up_up. eapply on_free_vars_up; tea.
  intros j ?.
  unfold up.
  destruct (Nat.leb_spec (p + (m - (k + p))) j); cbn => //.
  rewrite -lift0_rename.
  eapply on_free_vars_lift0.
  eapply on_free_vars_impl; only 2: apply wdf.
  unfold addnP. intros; cbn. apply cs. lia.
Qed.



Definition shiftnP_impl2 (p1 p2 q : nat -> bool) :
  (forall i : nat, p1 i -> p2 i -> q i) ->
  forall n i : nat, shiftnP n p1 i -> shiftnP n p2 i -> shiftnP n q i.
Proof.
  intros H. unfold shiftnP. intros; case_inequalities => //=. apply H => //=.
Qed.

Definition on_free_vars_impl2 {q1 q2 p : nat -> bool} {t} :
  (forall i, q1 i -> q2 i -> p i) ->
  on_free_vars q1 t -> on_free_vars q2 t -> on_free_vars p t.
Proof.
Admitted.
  (* intros Himpl x y. revert x y Himpl. revert t q1 q2 p.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //.
  all:unfold test_def in *; rtoProp => //.
  all:solve_all. all:eauto using shiftnP_impl2.
Qed. *)


(* Strengthening *)
Definition strengthen_renaming k f : nat -> nat :=
  fun n => if n <? k then n else f (n - k).

Definition shiftn_strengthen n k f t :
    rename (shiftn k (strengthen_renaming n f)) (lift n k t)
  = (rename (shiftn k f) t).
Proof.
  rewrite lift_rename (rename_compose _ _ _). apply rename_ext. intros i.
  unfold strengthen_renaming, lift_renaming, shiftn.
  repeat (case_inequalities => //=). all: try lia.
  replace (n + i - k - n) with (i - k) by lia. done.
Qed.




Definition on_free_vars_tProd P k l t :
  Alli (fun i => on_free_vars (shiftnP i P)) k l ->
  on_free_vars (shiftnP (k + #|l|) P) t ->
  on_free_vars (shiftnP k P) (it_tProd l t).
Proof.
  intros. unfold it_tProd. rewrite on_free_vars_it_mkProd_or_LetIn => //. len.
  rewrite andb_and. split.
  + unfold on_free_vars_ctx. rewrite List.rev_involutive.
    eapply alli_Alli. eapply Alli_map. eapply Alli_impl; tea. cbn.
    intros; rewrite shiftnP_add Nat.add_comm //.
  + rewrite shiftnP_add Nat.add_comm //.
Qed.

Definition on_free_vars_tLambda P k l t :
  Alli (fun i => on_free_vars (shiftnP i P)) k l ->
  on_free_vars (shiftnP (k + #|l|) P) t ->
  on_free_vars (shiftnP k P) (it_tLambda l t).
Proof.
  intros. unfold it_tProd. rewrite on_free_vars_it_mkLambda_or_LetIn => //. len.
  rewrite andb_and. split.
  + unfold on_free_vars_ctx. rewrite List.rev_involutive.
    eapply alli_Alli. eapply Alli_map. eapply Alli_impl; tea. cbn.
    intros; rewrite shiftnP_add Nat.add_comm //.
  + rewrite shiftnP_add Nat.add_comm //.
Qed.

Definition on_free_vars_tLambda_eq P k l t m :
  m = k + #|l| ->
  Alli (fun i => on_free_vars (shiftnP i P)) k l ->
  on_free_vars (shiftnP m P) t ->
  on_free_vars (shiftnP k P) (it_tLambda l t).
Proof.
  intros ->; apply on_free_vars_tLambda.
Qed.

Definition on_free_vars_mkApps P k u vs :
  All (on_free_vars (shiftnP k P)) vs ->
  on_free_vars (shiftnP k P) u ->
  on_free_vars (shiftnP k P) (mkApps u vs).
Proof.
  intros. rewrite on_free_vars_mkApps andb_and. split => //. eapply All_forallb => //.
Qed.



(* tactic *)
From Ltac2 Require Import Ltac2 Printf.

Ltac2 nconstructor n :=
  Control.extend (List.init n (fun i => fun _ => econstructor (Int.add 1 i)))
  (fun _ => ()) [].