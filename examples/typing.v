From Stdlib Require Import List.
Import ListNotations.

Inductive All {A : Type} (P : A -> Type) : list A -> Type :=
| All_nil : All P []
| All_cons a l : P a -> All P l -> All P (a::l).

Arguments All_nil {_ _}.
Arguments All_cons {_ _}.

Inductive Allₛ {A} {P : A -> Type} (Pₚ : forall a, P a -> Type): forall {l}, All P l -> Type :=
| Allₛ_nil : Allₛ Pₚ All_nil
| Allₛ_cons a l : forall (ra : P a), Pₚ a ra -> forall (x : All P l), Allₛ Pₚ x ->
                  Allₛ Pₚ (All_cons a l ra x).

Arguments Allₛ_nil {_ _ _}.
Arguments Allₛ_cons {_ _ _}.

Definition All_elim := All_rect.

Fixpoint lfl_Allₛ {A} {P : A -> Type} {Pₚ : forall a, P a -> Type} (HPₚ : forall a pa, Pₚ a pa)
    : forall l (t : All P l), Allₛ Pₚ t :=
  fun l t => match t with
  | All_nil => Allₛ_nil
  | All_cons a l ra x => Allₛ_cons a l ra (HPₚ a ra) x (lfl_Allₛ HPₚ l x)
  end.

Check lfl_Allₛ.

Parameter term : Type.
Parameter tCase : term -> list term -> term.

Inductive typing : term -> term -> Type :=
| typing_tCase (discr ind : term) (branches : list term) (return_type : term) :
          typing discr ind -> All (fun a => typing a return_type) branches ->
          typing (tCase discr branches) return_type.

Fixpoint typing_elim (P : forall t T, typing t T -> Type)
  (PtCase : forall discr ind branches return_type,
            forall (ty_discr : typing discr ind), P discr ind ty_discr ->
            forall (ty_br : All (fun a => typing a return_type) branches),
              Allₛ (fun a ty_a => P a return_type ty_a) ty_br ->
            P _ _ (typing_tCase discr ind branches return_type ty_discr ty_br)) :
    forall t T ty_tT, P t T ty_tT :=
  fun t T ty_tT => match ty_tT with
  | typing_tCase discr ind br return_type ty_discr ty_br =>
      PtCase discr ind br return_type ty_discr (typing_elim P PtCase _ _ ty_discr)
        ty_br (lfl_Allₛ (fun t => typing_elim P PtCase t return_type) _ ty_br)
  end.

Inductive typing_mut : term -> term -> Type :=
| typing_mut_tCase (discr ind : term) (branches : list term) (return_type : term) :
    typing_mut discr ind -> All_mut return_type branches -> typing_mut (tCase discr branches) return_type
with All_mut : term -> list term -> Type :=
| All_mut_nil return_type : All_mut return_type []
| All_mut_cons return_type a l : typing_mut a return_type -> All_mut return_type l -> All_mut return_type (a::l).



(** Transporting in a pulled back fibration. *)
Lemma ap {A B} (f :A -> B) {x y : A} : x = y -> f x = f y.
Proof.
  now destruct 1.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p).
Proof.
  now destruct p.
Defined.

Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : y = x) (z : P (f x))
  : eq_rect_r (fun x => P (f x)) z p  = eq_rect_r P z (ap f p).
Proof.
  destruct p; reflexivity.
Qed.

Notation "e # x" := (eq_rect_r _ x e) (at level 15).


Lemma transport_dep {A B C} (P: forall a:A, B a -> C a) {l l' f} (e : l = l') :
  P l (f l) = e # P l' (f l').
Proof.
  now destruct e.
Qed.

(* Encoding *)
Scheme typing_mut_All_mut_rec := Induction for typing_mut Sort Type
  with All_mut_typing_mut_rec := Induction for All_mut Sort Type.

Definition typing_mut_All_mut_rec2
    (P : forall t t0 : term, typing_mut t t0 -> Type)
    (P0 : forall (t : term) (l : list term), All_mut t l -> Type)
    (Ptyping_mut_tCase : forall discr ind branches return_type,
      forall ty_discr : typing_mut discr ind, P _ _ ty_discr ->
      forall ty_br : All_mut return_type branches, P0 _ _ ty_br ->
      P _ _  (typing_mut_tCase discr ind branches return_type ty_discr ty_br))
    (P0All_mut_nil  : forall return_type, P0 _ _ (All_mut_nil return_type))
    (P0All_mut_cons : forall return_type a l, forall ty_a, P _ _ ty_a ->
      forall ty_l, P0 _ _ ty_l -> P0 _ _ (All_mut_cons return_type a l ty_a ty_l)) :
  forall t T ty_tT, P t T ty_tT.
Proof.
  apply (typing_mut_All_mut_rec P P0 Ptyping_mut_tCase P0All_mut_nil P0All_mut_cons).
Qed.

(* just relabling *)
Definition All_to_All_mut {return_type branches} :
    All (fun a : term => typing_mut a return_type) branches ->
    All_mut return_type branches :=
  All_rect _ _  (fun branches _ => All_mut return_type branches)
    (All_mut_nil _)
    (fun a l pa pl ppl => All_mut_cons return_type a l pa ppl)
    branches.

(* Same *)
Definition All_mut_to_All {return_type branches} :
    All_mut return_type branches ->
    All (fun a : term => typing_mut a return_type) branches :=
  All_mut_typing_mut_rec (fun _ _ _ => True)
    (fun return_type branches x => All (fun a : term => typing_mut a return_type) branches)
    (fun _ _ _ _ _ _ _ _ => I)
    (fun return_type => All_nil)
    (fun return_type a l ty_a Pty_a _ Al => All_cons a l ty_a Al)
    return_type branches.

Definition All_mut_eq {return_type branches} :
  forall x : All_mut return_type branches,
  x = All_to_All_mut (All_mut_to_All x).
Proof.
  induction x; cbn.
  - reflexivity.
  - apply ap. assumption.
Defined.

Definition All_eq {return_type branches} :
  forall x : All (fun a : term => typing_mut a return_type) branches,
    x = All_mut_to_All (All_to_All_mut x).
Proof.
  induction x; cbn.
  - reflexivity.
  - apply ap. assumption.
Defined.

Lemma All_to_All_mut_adj {return_type branches} :
  forall x : All (fun a : term => typing_mut a return_type) branches,
  ap All_to_All_mut (All_eq x) = All_mut_eq (All_to_All_mut x).
Proof.
  induction x; cbn.
  - reflexivity.
  - cbn. rewrite <- ap_compose. cbn. rewrite ap_compose. f_equal.
    assumption.
Qed.

Definition typing_tCase' discr ind branches return_type :
    typing_mut discr ind -> All (fun a => typing_mut a return_type) branches ->
    typing_mut (tCase discr branches) return_type :=
  fun ty_discr ty_br =>
  typing_mut_tCase discr ind branches return_type ty_discr (All_to_All_mut ty_br).

Definition typing_elim2
  (P : forall t T, typing_mut t T -> Type)
  (PtCase' : forall discr ind branches return_type,
            forall (ty_discr : typing_mut discr ind), P discr ind ty_discr ->
            forall (ty_br : All (fun a => typing_mut a return_type) branches),
              Allₛ (fun a ty_a => P a return_type ty_a) ty_br ->
            P _ _ (typing_tCase' discr ind branches return_type ty_discr ty_br)) :
    forall t T ty_tT, P t T ty_tT.
Proof.
  unshelve eapply typing_mut_All_mut_rec with
    (P := fun t T ty_tT => P t T ty_tT)
    (P0 := fun return_type branches ty_br =>
           Allₛ (fun a ty_a => P a return_type ty_a) (All_mut_to_All ty_br)).
  - intros discr ind branches return_type ty_discr Pty_discr ty_br Pty_br.
    rewrite (All_mut_eq ty_br).
    apply ((PtCase' discr ind branches return_type ty_discr Pty_discr (All_mut_to_All ty_br) Pty_br)).
    (* wont type check as P can't be inferred *)
    (* fun discr ind branches return_type ty_discr Pty_discr ty_br Pty_br =>
      (All_mut_eq ty_br) # (PtCase' discr ind branches return_type ty_discr Pty_discr (All_mut_to_All ty_br) Pty_br). *)
  - exact (fun return_type => Allₛ_nil).
  - exact (fun return_type a l ty_a Pty_a ty_l Pty_l => Allₛ_cons a l ty_a Pty_a ((All_mut_to_All ty_l)) Pty_l).
Defined.

Definition typing_elim2_tCase' :
  forall P PtCase' discr ind branches return_type ty_discr ty_br,
    typing_elim2 P PtCase' _ _ (typing_tCase' _ _ _ _ ty_discr ty_br)
  = PtCase' _ _ _ _ ty_discr (typing_elim2 P PtCase' discr ind ty_discr) ty_br
      (lfl_Allₛ (fun t => typing_elim2 P PtCase' t return_type) branches ty_br).
Proof.
  (* It does NOT compute *)
  Fail reflexivity.
  (* Push the transport in and simplify *)
  intros. cbn. rewrite <- (All_to_All_mut_adj ty_br), <- transport_compose, (transport_dep _ (All_eq ty_br)). repeat f_equal.
  (* Prove that both proofs of the local fundamental lemma are the same *)
  induction ty_br; cbn; f_equal; eauto.
Qed.
