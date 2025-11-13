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

From MetaRocq.NestedElim.Formalization Require Import Lemma Positivity_condition.
Import ViewInductive.


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


  (* function to be folded *)

    Definition remove_rc_nargs Γ : list argument :=
    (fold_left remove_rc_one Γ ( @nil argument, @nil argument , (fun n => n))).1.2.

    (* New args + Spec *)
  Definition g_args_no_rc : list argument :=
    remove_rc_nargs g_args.

  Definition remove_rc_rename Γ : nat -> nat :=
    (fold_left remove_rc_one Γ ( @nil argument, @nil argument , (fun n => n))).2.

  (* New renaming + Spec *)
  Definition rename_no_rc : nat -> nat := remove_rc_rename g_args.

  (* 4. Update instantiation and properties *)
  Definition g_largs_no_rc : list term :=
    mapi (rename rename_no_rc) g_largs.


  Definition l_inst_uparams_no_rc : list (list term * argument) :=
    map (fun ' (llargs, arg) =>
      let llargs' := mapi (fun i => rename rename_no_rc (nb_g_largs + i)) llargs in
      let arg' := rename_argument rename_no_rc (nb_g_largs + #|llargs|) arg in
      (llargs', arg')
      )
    inst_uparams_a.

  Notation nb_g_args_no_rc := (#|g_args_no_rc|).
  Notation nb_new_cxt_sub := (nb_g_nuparams + nb_g_args_no_rc + nb_g_largs).

  (* should not have renaming as applied to inst_uparams_no_rc *)

  Definition inst_to_term_no_rc : (list term * argument) -> term :=
    fun '(llargs, arg) =>
      (it_tLambda llargs (argument_to_term nb_g_block g_uparams_b (nb_new_cxt_sub + #|llargs|) arg)).

  Definition inst_uparams_no_rc : nat -> term :=
    fun n => nth n (map inst_to_term_no_rc l_inst_uparams_no_rc) (tRel n).

  (* New indices are ↓↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams ,,, indices) + positivity *)
  Definition new_indices indices : context :=
    arguments_to_context nb_g_block g_uparams_b (nb_g_uparams + nb_g_nuparams) g_args_no_rc ,,,
    cxt_of_terms g_largs_no_rc ,,,
    List.rev ( mapi (fun i cdecl =>
              let f := inst (up i inst_uparams_no_rc) in
              mkdecl cdecl.(decl_name) (option_map f cdecl.(decl_body))
                  (f cdecl.(decl_type))) (List.rev (l_nuparams ,,, indices))
      ).

  (* Extra Arguments: g_args ,,, g_largs ,,,  σ(l_nuparams) + Positivity *)
  Definition cstr_extra_args : list argument :=
       g_args_no_rc
    ++ map arg_is_free g_largs_no_rc
    ++ map arg_is_free (mapi_rec (fun i t => t.[up i inst_uparams_no_rc])
        (terms_of_cxt l_nuparams) 0).


  Definition err_arg : list term * argument
    := ([], arg_is_free (tVar "impossible case")).

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

  Definition specialize_one_inductive_body (idecl : one_inductive_body) : one_inductive_body :=
  {|
    ind_indices   := new_indices idecl.(ind_indices);
    ind_ctors     := map specialize_ctor idecl.(ind_ctors);
  |}.

  End NestedToMutualInd.

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

  Definition nested_to_mutual_argument args acc_indb :=
    fold_left nested_to_mutual_one_argument args ([],acc_indb).

  Definition nested_to_mutual_one_ctor ctor acc_indb :
    constructor_body * list one_inductive_body :=
  let x := nested_to_mutual_argument ctor.(cstr_args) acc_indb in
  let new_ctor := {|
    cstr_args    := x.1 ;
    cstr_indices := ctor.(cstr_indices)
    |} in
  (new_ctor, x.2).

  Definition nested_to_mutual_ctor ctors acc_indb : list constructor_body * list one_inductive_body :=
  fold_left ( fun acc ctor =>
      let x := nested_to_mutual_one_ctor ctor acc.2 in
      (acc.1 ++ [x.1], x.2)
    )
    ctors
    ([],acc_indb).

  (* check preservation *)
  Definition nested_to_mutual_one_indb indb acc_indb : one_inductive_body * list one_inductive_body :=
  let x := nested_to_mutual_ctor indb.(ind_ctors) acc_indb in
  let new_indb := {|
    ind_indices   := indb.(ind_indices);
    ind_ctors     := x.1 ;
  |} in
  (new_indb, x.2).


  Definition nested_to_mutual_indb indbs : list one_inductive_body * list one_inductive_body :=
    fold_left ( fun acc indb =>
      let x := nested_to_mutual_one_indb indb acc.2 in
      (acc.1 ++ [x.1], x.2)
      )
      indbs
      ([],[]).

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
  |}.
