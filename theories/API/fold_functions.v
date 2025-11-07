From Stdlib Require Export List.
Export ListNotations.

(* 1. General Purposed Fold Functions
- fold_right_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_left_state : {A B X state} : (nat -> A -> state -> (X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) -> B
- fold_right_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B
- fold_left_state_opt {A B X state} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B

=> 2 / 3 / 4 variants

*)


#[warnings="-warn-library-file-stdlib-vector"]
From Stdlib Require Import Vector.

Fixpoint iter_T n X B :=
  match n with
  | 0 => B
  | S n => X -> (iter_T n X B)
  end.

Fixpoint iter_X {n X B} (v:Vector.t X n) : iter_T n X B -> B :=
  match v in Vector.t _ n return iter_T n X B -> B with
  | nil _ => fun f => f
  | cons _ a _ tl => fun f => iter_X tl (f a)
  end.

Fixpoint X_iter {n X B} : (Vector.t X n -> B) -> iter_T n X B :=
  match n with
  | 0 => fun f => f (nil _)
  | S n => fun f x => X_iter (fun v => f (cons _ x _ v))
  end.

Definition fold_right_state {A B X state} (n : nat) (s : state) (l : list A)
  (tp : state -> nat -> A -> (state -> iter_T n X B) -> B) (t : state -> iter_T n (list X) B) : B :=
  let fix aux (s : state) (pos : nat) (ids : Vector.t (list X) n) (l : list A) {struct l} : B :=
    match l with
    | [] => iter_X (Vector.map (@List.rev _) ids) (t s)
    | a :: l => tp s pos a (fun s => X_iter (fun x => aux s (S pos) (Vector.map2 (@List.cons _) x ids) l))
    end
  in
  aux s 0 (Vector.const [] n) l.

Definition fold_left_state {A B X state} (n : nat) (s : state) (l : list A)
  (tp : state -> nat -> A -> (state -> iter_T n X B) -> B) (t : state -> iter_T n (list X) B) : B :=
  fold_right_state n s (List.rev l) tp t.

(* 1.2 Fold_right and Fold_left conditional *)
Definition fold_right_state_opt {A B X state} (n : nat) (s : state) (l : list A)
  (tp :  state -> nat -> A ->(state -> iter_T n (list X) B) -> B) (t : state -> iter_T n (list X) B) : B :=
  let fix aux (s : state) (pos : nat) (ids : Vector.t (list X) n) (l : list A) {struct l} : B :=
    match l with
    | [] => iter_X (Vector.map (@List.rev _) ids) (t s)
    | a :: l => tp s pos a (fun s => X_iter (fun x => aux s (S pos) (Vector.map2 (@List.app _) x ids) l))
    end
  in
  aux s 0 (Vector.const [] n) l.

Definition fold_left_state_opt {A B X state} (n : nat) (s : state) (l : list A)
  (tp : state -> nat -> A -> (state -> iter_T n (list X) B) -> B) (t : state -> iter_T n (list X) B) : B :=
  fold_right_state_opt n s (List.rev l) tp t.

