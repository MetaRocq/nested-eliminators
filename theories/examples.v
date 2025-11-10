From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.

From MetaRocq.NestedElim Require Import test_functions.

Unset Elimination Schemes.
Unset MetaRocq Strict Unquote Universe Mode.


(* There are two functions:
- generate_sparse_parametricty : ∀ {A : Type}, param_env → sort → A → TemplateMonad unit that given
  - a list of information about types used for nesting, like strictly uniform parameters,
    sparse parametricty and local fundamental lemma for nested case
  - the return sort
  - an inductive type

  Generates the sparse parametrictiy and the local fundamental lemma

- generate_elim ! ∀ {A : Type}, param_env → ident → sort → A → TemplateMonad unit that given:
  - a list of information about types used for nesting, like strictly uniform parameters,
    sparse parametricty and local fundamental lemma for nested case
  - a name
  - the return sort
  - an indictive type

  Generates the eliminator for the nested inductive type
*)


(* Example 1: RoseTree *)
Inductive RoseTree A : Type :=
| RTleaf (a : A) : RoseTree A
| RTnode (l : list (RoseTree A)) : RoseTree A.


(* generate the sparse parametricity and the local fundamental theorem *)
MetaRocq Run (generate_sparse_parametricty [] sProp list).

Print listₛ.
Print lfl_listₛ.

(* Compute and add the date to the environment *)
MetaRocq Run (get_paramEp list []).


(* generate the nested eliminator *)
MetaRocq Run (generate_elim [kmp_list] "RoseTree_elim" sProp RoseTree).

Check RoseTree_elim.
Print RoseTree_elim.




(* Example 2: typing *)
Inductive term : Type :=
| tCase : term -> list term -> term.

Inductive All (A : Type) (P : A -> Prop) : list A -> Prop :=
| All_nil : All A P []
| All_cons a l : P a -> All A P l -> All A P (a::l).

Inductive typing : term -> term -> Prop :=
| typing_tCase (discr ind : term) (branches : list term) (return_type : term) :
          typing discr ind -> All term (fun a => typing a return_type) branches ->
          typing (tCase discr branches) return_type.


(* generate the sparse parametricity and the local fundamental theorem *)
MetaRocq Run (generate_sparse_parametricty [kmp_list] sProp All).

Print Allₛ.
Print lfl_Allₛ.

(* It needs to know the strictly postive uniform parameters of list
   to compute striclty postive uniform parameters for All *)
MetaRocq Run (get_paramEp ( @All ) [kmp_list]).

(* generate the nested eliminator *)
MetaRocq Run (generate_elim [kmp_list; kmp_All] "typing_elim" sProp typing).

Check typing_elim.
Print typing_elim.




(* ### Other Containers ### *)

(* prod *)
MetaRocq Run (generate_sparse_parametricty [] sProp prod).
Print prodₛ.
Print lfl_prodₛ.
MetaRocq Run (get_paramEp prod []).

(* vec *)
Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

MetaRocq Run (generate_sparse_parametricty [] sProp vec).
Print vecₛ.
Print lfl_vecₛ.
MetaRocq Run (get_paramEp vec []).

(* RoseTree *)
MetaRocq Run (generate_sparse_parametricty [kmp_list] sProp RoseTree).
Print RoseTreeₛ.
Print lfl_RoseTreeₛ.
MetaRocq Run (get_paramEp RoseTree [kmp_list]).

Definition Ep := [kmp_prod; kmp_list; kmp_vec; kmp_RoseTree; kmp_All].


(* ### Other Examples ### *)

(* Nesting with lists *)
Inductive RoseRoseTree A : Type :=
| Nleaf (a : A) : RoseRoseTree A
| Nnode (p : (list (list (RoseRoseTree A)))) : RoseRoseTree A.

MetaRocq Run (generate_elim Ep "RoseRose_elim" sProp RoseRoseTree).
Check RoseRose_elim.
Print RoseRose_elim.

Inductive ArrowTree1 A : Type :=
| ATleaf1 (a : A) : ArrowTree1 A
| ATnode1 (l : (bool -> list (ArrowTree1 A))) : ArrowTree1 A.

MetaRocq Run (generate_elim Ep "ArrowTree1_elim" sProp ArrowTree1).
Check ArrowTree1_elim.
Print ArrowTree1_elim.

Inductive ArrowTree2 A : Type :=
| ATleaf2 (a : A) : ArrowTree2 A
| ATnode2 (l : list (nat -> ArrowTree2 A)) : ArrowTree2 A.

MetaRocq Run (generate_elim Ep "ArrowTree2_elim" sProp ArrowTree2).
Check ArrowTree2_elim.
Print ArrowTree2_elim.

Inductive ArrowTree3 A : Type :=
| ATleaf3 (a : A) : ArrowTree3 A
| ATnode3 (l : (bool -> list (nat -> ArrowTree3 A))) : ArrowTree3 A.

MetaRocq Run (generate_elim Ep "ArrowTree3_elim" sProp ArrowTree2).
Check ArrowTree3_elim.
Print ArrowTree3_elim.


(* nesting product *)
Inductive PairTree A : Type :=
| Pleaf (a : A) : PairTree A
| Pnode (p : (PairTree A) * (PairTree A)) : PairTree A.

MetaRocq Run (generate_elim Ep "PairTree_elim" sProp PairTree).
Check PairTree_elim.
Print PairTree_elim.

Inductive LeftTree A : Type :=
| Lleaf (a : A) : LeftTree A
| Lnode (p : (LeftTree A) * nat) : LeftTree A.

MetaRocq Run (generate_elim Ep "LeftTree_elim" sProp LeftTree).
Check LeftTree_elim.
Print LeftTree_elim.


(* nesting vectors *)
Inductive VecTree A : Type :=
| VNleaf (a : A) : VecTree A
| VNnode n (p : vec (VecTree A) n) : VecTree A.

MetaRocq Run (generate_elim Ep "VecTree_elim" sProp VecTree).
Check VecTree_elim.
Print VecTree_elim.


(* nesting with RoseTree *)
Inductive NestedRoseTree : Type :=
| node : RoseTree (NestedRoseTree) -> NestedRoseTree.

MetaRocq Run (generate_elim Ep "NestedRoseTree_elim" sProp NestedRoseTree).
Check NestedRoseTree_elim.
Print NestedRoseTree_elim.

(* Sparse Parametricity for Records *)
Record foo A := mk_foo {
  c1 : nat;
  c2 : A
}.

MetaRocq Run (generate_sparse_parametricty [] sProp foo).

Print fooₛ.

MetaRocq Run (generate_sparse_parametricty [] sProp sigT).

