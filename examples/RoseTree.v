Require Import Nat.
From Stdlib Require Import List.
(* From Equations Require Import Equations.*)
From Corelib.Lists Require Import ListDef.
Import ListNotations.

  (*********** Lists *********)

Fixpoint map {A B} (f :A -> B) (l:list A) : list B :=
  match l with
  | nil => nil
  | a :: l => f a :: map f l
  end.

Inductive listϵ A (Aϵ : A -> Type) : list A -> Type :=
  | nilϵ : listϵ A Aϵ nil
  | consϵ : forall a (aϵ : Aϵ a) l (lϵ : listϵ A Aϵ l), listϵ A Aϵ (cons a l).

Arguments nilϵ {_ _}.
Arguments consϵ {_ _}.

Fixpoint listϵ_funct A (P Q : A -> Type) (H : forall a, P a -> Q a) : forall l, listϵ A P l -> listϵ A Q l :=
  fun l x =>
  match x with
  | nilϵ => nilϵ
  | consϵ a ap l lp => consϵ a (H a ap) l (listϵ_funct A P Q H l lp)
  end.

Fixpoint listϵ_lft A PA (HPA : forall a, PA a) : forall t, listϵ A PA t :=
  fun t => match t with
  | nil => nilϵ
  | cons a l => consϵ a (HPA a) l (listϵ_lft A PA HPA l)
  end.

Notation list_elim := list_rect.

Definition listϵ_fl A (Aϵ : A -> Type) (aϵ : forall a, Aϵ a) (l : list A) : listϵ A Aϵ l
  := list_elim (listϵ A Aϵ) nilϵ (fun r => consϵ r (aϵ r)) l.

  (*********** RoseTree *********)

(** listings: RoseTree **)
Inductive RoseTree A : Type :=
| leaf : A -> RoseTree A
| node : list (RoseTree A) -> RoseTree A.
(** listings: RoseTree_end **)

Arguments leaf {_} _.
Arguments node {_} _.

Inductive RoseTreeϵ A (PA : A -> Type) : RoseTree A -> Type :=
| leafϵ : forall a, PA a -> RoseTreeϵ A PA (leaf a)
| nodeϵ : forall l, listϵ _ (RoseTreeϵ A PA) l -> RoseTreeϵ A PA (node l).

Arguments leafϵ {_ _}.
Arguments nodeϵ {_ _}.

Fixpoint RoseTreeϵ_lft A PA (HPA : forall a, PA a) : forall t, RoseTreeϵ A PA t :=
  fun t =>
  match t with
  | leaf a => leafϵ a (HPA a)
  | node l => nodeϵ l (listϵ_fl _ _ (RoseTreeϵ_lft A PA HPA) l)
  end.

(** listings: ty_RoseTree_elim **)
Definition ty_RoseTree_elim :=
  forall (A : Type) (P : RoseTree A -> Type),
  forall (Pleaf: forall a, P (leaf a)),
  forall (Pnode : forall l, P (node l)),
  forall t, P t.
(** listings: ty_RoseTree_elim_end **)

(** listings: expected_ty_RoseTree_elim **)
Definition expected_ty_RoseTree_elim :=
  forall (A : Type) (P : RoseTree A -> Type),
  forall (Pleaf: forall a, P (leaf a)),
  forall (Pnode : forall l, listϵ (RoseTree A) P l -> P (node l)),
  forall t, P t.
(** listings: expected_ty_RoseTree_elim_end **)

(** listings: RoseTree_elim **)
Fixpoint RoseTree_elim A P Pleaf Pnode (t : RoseTree A) {struct t} : P t :=
   match t with
   | leaf a => Pleaf a
   | node l => Pnode l (listϵ_fl (RoseTree A) P (RoseTree_elim A P Pleaf Pnode) l)
   end.
(** listings: RoseTree_elim_end **)

(** listings: ty_RoseTree_elim_param **)
Definition ty_RoseTree_elim_param :=
  forall (A : Type) (PA : A -> Type) (P : RoseTree A -> Type),
  forall (Pleaf: forall a, PA a -> P (leaf a)),
  forall (Pnode : forall l, listϵ (RoseTree A) P l -> P (node l)),
  forall t, RoseTreeϵ A PA t -> P t.
(** listings: ty_RoseTree_elim_param_end **)

Fixpoint RoseTree_induction A PA P
  (Hleaf : forall a, PA a -> P (leaf a))
  (Hnode : forall l, listϵ (RoseTree A) P l -> P (node l)) :
  forall t, RoseTreeϵ A PA t -> P t :=
  fun t x => match x with
  | leafϵ a pa => Hleaf a pa
  | nodeϵ l pl => Hnode l (listϵ_funct _ _ _ (RoseTree_induction A PA P Hleaf Hnode) l pl)
    end.


Lemma RoseTree_elim_node : forall A P Pleaf Pnode l,
  RoseTree_elim A P Pleaf Pnode (node l) =
  Pnode l (listϵ_fl _ P (RoseTree_elim A P Pleaf Pnode) l).
Proof.
  cbn. 
  reflexivity.
Qed.

(** listings: RoseTree_mut **)
Inductive RoseTreeMut A : Type :=
  | leaf_mut (a : A) : RoseTreeMut A
  | node_mut (l : list_RoseTreeMut A) : RoseTreeMut A
with list_RoseTreeMut A : Type :=
  | nil_mut : list_RoseTreeMut A
  | cons_mut : RoseTreeMut A -> list_RoseTreeMut A -> list_RoseTreeMut A.
(** listings: RoseTree_mut_end **)

Arguments leaf_mut {_} _.
Arguments node_mut {_} _.
Arguments nil_mut {_}.
Arguments cons_mut {_} _ _.

Scheme RoseTreeMut_rec' := Induction for RoseTreeMut Sort Type
  with list_RoseTreeMut_rec' := Induction for list_RoseTreeMut Sort Type.

Combined Scheme RoseTreeMut_combined from RoseTreeMut_rec',list_RoseTreeMut_rec'.



(* equivalence between list (RoseTreeMut A) and list_RoseTreeMut A *)

Fixpoint list_to_listMut {A} (l : list (RoseTreeMut A)) : list_RoseTreeMut A :=
match l with
| nil => nil_mut
| cons a l => cons_mut a (list_to_listMut l)
end.

Fixpoint listMut_to_list {A} (l : list_RoseTreeMut A) : list (RoseTreeMut A) :=
match l with
| nil_mut => nil
| cons_mut a l => cons a (listMut_to_list l)
end.

Definition listMut_rect : forall {A} (P : list_RoseTreeMut A -> Type) (Pnil : P nil_mut)
  (Pcons : forall a l, P l -> P (cons_mut a l)),
  forall l, P l.
  intros; unshelve eapply (list_RoseTreeMut_rec' _ (fun _ => unit) P _ _ _ _ l);
  cbn; intros; try exact tt; eauto.
Defined.

Lemma ap {A B} (f :A -> B) {x y : A} : x = y -> f x = f y.
now destruct 1.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p).
now destruct p.
Defined.

Lemma listMut_to_list_eq {A} (l : list_RoseTreeMut A) : l = list_to_listMut (listMut_to_list l).
  induction l; cbn.
  - reflexivity.
  - apply ap. assumption.
Defined.

Lemma list_to_listMut_eq {A} (l : list (RoseTreeMut A)) : l = listMut_to_list (list_to_listMut l).
  induction l; cbn.
  - reflexivity.
  - apply ap. eauto.
Defined.

(** Transporting in a pulled back fibration. *)
Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : y = x) (z : P (f x))
  : eq_rect_r (fun x => P (f x)) z p  = eq_rect_r P z (ap f p).
Proof.
  destruct p; reflexivity.
Qed.

Notation "e # x" := (eq_rect_r _ x e) (at level 55).

Lemma transport_dep {A B C} (P: forall a:A, B a -> C a) {l l' f} (e : l = l') :
  P l (f l) = e # P l' (f l').
now destruct e.
Qed.

Lemma list_to_listMut_adj {A} (l: list (RoseTreeMut A)) :
  ap list_to_listMut (list_to_listMut_eq l) = listMut_to_list_eq (list_to_listMut l).
  induction l; cbn.
  - reflexivity.
  - cbn. rewrite <- ap_compose. cbn. rewrite ap_compose. f_equal.
    assumption.
Qed.

Notation RoseTree' := RoseTreeMut.

Definition leaf' {A} : forall (a : A), RoseTree' A := leaf_mut.

Definition node' {A} : forall (l : list (RoseTree' A)), RoseTree' A :=
  fun l => node_mut (list_to_listMut l).

(* Nested Recusor Rewrited with RoseTreeMut *)

Lemma RoseTree_elim' A (P : RoseTree' A -> Type) (Pleaf: forall a, P (leaf' a))
   (Pnode : forall l, listϵ _ P l -> P (node' l)) : forall r, P r.
Proof.
  unshelve eapply RoseTreeMut_rec' with
    (P0 := fun l => listϵ _ P (listMut_to_list l)).
  - intros; eapply Pleaf.
  - intros l ?. rewrite (listMut_to_list_eq l). apply Pnode; assumption.
  - constructor.
  - intros; econstructor; assumption.
Defined.

Lemma RoseTree_elim_leaf' : forall A P Pleaf Pnode a,
  RoseTree_elim' A P Pleaf Pnode (leaf' a) = Pleaf a.
Proof.
  reflexivity.
Qed.

Lemma RoseTree_elim_node' : forall A P Pleaf Pnode l,
  RoseTree_elim' A P Pleaf Pnode (node' l) =
  Pnode l (listϵ_lft _ P (RoseTree_elim' A P Pleaf Pnode) l).
Proof.
  Fail reflexivity.
  intros. cbn. rewrite <- (list_to_listMut_adj l).
  pose (e' := list_to_listMut_eq l).
  rewrite <- transport_compose. rewrite (transport_dep Pnode e').
  f_equal. f_equal. clear e'. induction l; cbn.
  - reflexivity.
  - f_equal. eauto.
Qed.
