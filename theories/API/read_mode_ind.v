From PluginNestedElim Require Import core.
From PluginNestedElim Require Import fold_functions.
From PluginNestedElim Require Import context_access context_store.
From PluginNestedElim Require Import inductive_access.
From PluginNestedElim Require Import creating_terms.



(*

###############################
### General Read Functions  ###
###############################

*)

Section ReadByDecl.

  Context {X : Type}.
  Context (read_letin : state -> option ident -> aname -> term -> term ->
                        (state -> key -> X) -> X).
  Context (read_var   : state -> option ident -> aname -> term ->
                        (state -> key -> X) -> X).

  Section ReadCxt.

    Context (n : nat).
    Context (s : state).
    Context (x : option ident).
    Context (cxt : context).

    Context (ccletin : state -> nat -> key -> (state -> iter_T n keys X) -> X).
    Context (ccvar   : state -> nat -> key -> (state -> iter_T n keys X) -> X).

    Definition read_by_decl : (state -> iter_T n keys X) -> X :=
      fold_left_state_opt n s cxt (fun s pos ' (mkdecl an z ty) cc =>
        match z with
        | Some db => let* s key_letin := read_letin s (Some "letin") an db ty in
                    ccletin s pos key_letin cc
        | None    => let* s key_var := read_var s x an ty in
                    ccvar s pos key_var cc
        end
      ).

  End ReadCxt.

  (* Trivial continuation + bundle letin and arg *)
  #[local] Fixpoint repeat {A} n (a : A) : Vector.t A n :=
    match n with
    | 0   => Vector.nil _
    | S n => Vector.cons _ a n (repeat n a)
    end.

  Definition cc_nosave n : state -> nat -> key -> (state -> iter_T n keys X) -> X :=
    fun s pos k cc => iter_X (repeat n []) (cc s).

  Definition cc_triv : state -> nat -> key -> (state -> keys -> X) -> X :=
    fun s pos k cc => cc s [k].

  Definition read_context : state -> option ident -> context -> (state -> keys -> X) -> X :=
    fun s x cxt => read_by_decl 1 s x cxt cc_triv cc_triv.

  (* Trivial continuation + separate letin and arg *)
  Definition cc_sep_letin : state -> nat -> key -> (state -> keys -> keys -> keys -> X) -> X :=
    fun s pos k cc => cc s [k] [] [k].

  Definition cc_sep_arg : state -> nat -> key -> (state -> keys -> keys -> keys -> X) -> X :=
    fun s pos k cc => cc s [] [k] [k].

  Definition read_context_sep : state -> option ident -> context ->
      (state -> keys -> keys -> keys -> X) -> X :=
    fun s x cxt => read_by_decl 3 s x cxt cc_sep_letin cc_sep_arg.

End ReadByDecl.

Definition add_by_decl     {X} := @read_by_decl     X add_old_letin add_old_var.
Definition add_context     {X} := @read_context     X add_old_letin add_old_var.
Definition add_context_sep {X} := @read_context_sep X add_old_letin add_old_var.

Definition closure_by_decl     binder := read_by_decl     kp_tLetIn (kp_binder binder).
Definition closure_context     binder := read_context     kp_tLetIn (kp_binder binder).
Definition closure_context_sep binder := read_context_sep kp_tLetIn (kp_binder binder).

Definition make_by_decl     binder := read_by_decl     mk_tLetIn (mk_binder binder).
Definition make_context     binder := read_context     mk_tLetIn (mk_binder binder).
Definition make_context_sep binder := read_context_sep mk_tLetIn (mk_binder binder).



(*

#############################
###      Mutual Level     ###
#############################

*)

Definition add_inds {X} : mutual_inductive_body -> state -> (state -> keys -> X) -> X :=
  fun mdecl s cc =>
  let cxt := mapi (fun i indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type)) (rev mdecl.(ind_bodies)) in
  let* s _ key_inds _ := add_old_context s (Some "ind") cxt in
  cc s key_inds.

Definition subst_ind {X} : state -> kername -> (state -> X) -> X :=
  fun s kname t =>
  let ind_terms := mapi (fun i _ => (tInd (mkInd kname i) [])) (get_ind_bodies s kname) in
  let* s := subst_old_context s ind_terms in
  t s.



(*

############################
###     Params Level     ###
############################

*)


(* Scope uniform parameters *)
Definition add_uparams {X} : state -> kername -> (state -> keys -> X) -> X :=
  fun s kname => add_context s (Some "uparams") (get_uparams s kname).

Definition add_by_uparam {X} n s kname :=
  @add_by_decl X n s (Some "uparams") (get_uparams s kname) (cc_nosave n).

Definition closure_uparams binder : state -> kername -> (state -> keys -> term) -> term :=
  fun s kname => closure_context binder s (Some "uparams") (get_uparams s kname).

Definition closure_by_uparam binder n s kname :=
  closure_by_decl binder n s (Some "uparams") (get_uparams s kname) (cc_nosave n).


(* Scope non-uniform parameters *)
Definition add_nuparams {X} : state -> kername -> (state -> keys -> X) -> X :=
  fun s kname => add_context s (Some "nuparams") (get_nuparams s kname).

Definition add_by_nuparam {X} n s kname :=
  @add_by_decl X n s (Some "nuparams") (get_nuparams s kname)  (cc_nosave n).

Definition closure_nuparams binder : state -> kername -> (state -> keys -> term) -> term :=
  fun s kname => closure_context binder s (Some "nuparams") (get_nuparams s kname).

Definition closure_by_nuparam binder n s kname :=
  closure_by_decl binder n s (Some "nuparams") (get_nuparams s kname) (cc_nosave n).


(* Scope parameters = uniform and non-uniform parameters *)
Definition add_params {X} : state -> kername -> (state -> keys -> X) -> X :=
  fun s kname => add_context s (Some "params") (get_params s kname).

Definition add_by_param {X} n s kname :=
  @add_by_decl X n s (Some "params") (get_params s kname) (cc_nosave n).

Definition closure_params binder : state -> kername -> (state -> keys -> term) -> term :=
  fun s kname => closure_context binder s (Some "params") (get_params s kname).

Definition closure_by_param binder n s kname :=
  closure_by_decl binder n s (Some "params") (get_params s kname) (cc_nosave n).



(*

#############################
###    Enter Inductive    ###
#############################

*)



(* 4. Make Term *)
Section mk_tFix.
  Context (kname : kername).
  Context (tFix_type : nat -> term).
  Context (tFix_rarg : nat -> nat).

  #[local] Definition tFix_name : nat -> ident :=
    fun pos_indb => "F" ^ string_of_nat pos_indb ^  "_" ^ (snd kname).

  #[local] Definition tFix_aname : nat -> aname :=
    fun pos_indb => mkBindAnn (nNamed (tFix_name pos_indb)) Relevant.

  #[local] Definition tFix_context : state -> context :=
    fun s => rev ( mapi
    (fun pos_indb _ => mkdecl (tFix_aname pos_indb) None (tFix_type pos_indb))
    (get_ind_bodies s kname)).

  Definition mk_tFix : state -> nat -> (state -> keys -> nat -> term) -> term :=
    fun s focus tmc =>
    let* s_Fix _ key_fixs _ := add_fresh_context s (Some "tFix") (tFix_context s) in
    tFix
      (mapi (fun pos_indb _ =>
        mkdef _ (tFix_aname pos_indb)
                (tFix_type  pos_indb)
                (tmc s_Fix key_fixs pos_indb )
                (tFix_rarg  pos_indb))
            (get_ind_bodies s kname))
      focus.

  End mk_tFix.

  Definition tFix_default_rarg : state -> kername -> nat -> nat :=
  fun s kname pos_indb => get_nb_nuparams s kname + length (get_indices s kname pos_indb).


(* Make inductive *)




(* Fold *)
Definition iterate_inductives {B X} n : state -> kername ->
            (state -> nat -> (state -> iter_T n B X) -> X) ->
            (state -> iter_T n (list B) X) -> X :=
  fun s kname tp cc => fold_right_state n s (get_ind_bodies s kname)
                        (fun s i _ => tp s i) cc.



(*

#############################
###    Inductive Level    ###
#############################

*)

Definition closure_indices binder : state -> kername -> nat -> (state -> keys -> term) -> term :=
  fun s kname pos_indb => read_context mk_tLetIn (mk_binder binder) s (Some "indices") (get_indices s kname pos_indb).



(*

############################
###      Enter Ctor      ###
############################

*)


(* 5. Make Match *)
Section MktCase.
  Context (kname : kername).
  Context (pos_indb : nat).
  Context (mk_case_pred : state -> keys -> key -> term).
  Context (key_uparams key_nuparams : keys).

  #[local] Definition mk_case_info : state -> case_info :=
    fun s => mk_case_info (mkInd kname pos_indb) (get_nb_params s kname) Relevant.

  #[local] Definition mk_pred : state -> predicate term :=
    fun s =>
    let* sPred _ key_findices _ := add_fresh_context s None (get_indices s kname pos_indb) in
    let* sPred key_fVarMatch := add_fresh_var sPred (Some "fresh var match") (mkBindAnn nAnon Relevant)
                                (make_ind sPred kname pos_indb key_uparams key_nuparams key_findices) in
    mk_predicate []
      (get_terms s key_uparams ++ get_terms s key_nuparams)
      (get_aname sPred key_fVarMatch :: get_anames sPred key_findices)
      (mk_case_pred sPred key_findices key_fVarMatch).

  Definition mk_tCase : state -> term -> (state -> keys -> keys -> keys -> nat -> term) -> term :=
    fun s tm_match branch =>
    tCase (mk_case_info s) (mk_pred s) tm_match
    (mapi
      (fun pos_ctor ctor =>
      let* s key_lets key_args key_lets_args := add_old_context s (Some ("args_" ^ snd kname)) ctor.(cstr_args) in
          mk_branch (rev (get_anames s key_lets_args)) (branch s key_lets key_args key_lets_args pos_ctor))
      (get_indb s kname pos_indb).(ind_ctors)).

End MktCase.



(* Make Inductive *)




(* Fold *)
Definition iterate_ctors {B X} n : state -> kername -> nat ->
            (state -> nat -> (state -> iter_T n B X) -> X) ->
            (state -> iter_T n (list B) X) -> X :=
  fun s kname pos_indb tp cc => fold_right_state n s (get_ctors s kname pos_indb)
                                  (fun s i _ => tp s i) cc.

Definition iterate_all_ctors {B X} n : state -> kername ->
      (state -> nat -> nat -> (state -> iter_T n B X) -> X) ->
      (state -> iter_T n (list (list B)) X) -> X :=
  fun s kname tp cc =>
  iterate_inductives n s kname (
    fun s pos_indb cc =>
    iterate_ctors n s kname pos_indb (fun s => tp s pos_indb) cc
  )
  cc.



(*

############################
###      Ctor Level      ###
############################

*)

Definition add_by_arg {X} n s kname pos_indb pos_ctor :=
  @add_by_decl X n s (Some "args") (get_args s kname pos_indb pos_ctor).

Definition closure_by_arg binder n s kname pos_indb pos_ctor :=
  closure_by_decl binder n s (Some "args") (get_args s kname pos_indb pos_ctor).

