From MetaRocq.NestedElim Require Import api_debruijn.


(* 0. Aux functions *)
Fixpoint noccur_between (k n : nat) (t : term) {struct t} : bool :=
  match t with
  | tRel i => (i <? k) || (k + n <=? i)
  | tEvar _ args => forallb (noccur_between k n) args
  | tCast c _ t0 => noccur_between k n c && noccur_between k n t0
  | tProd _ T M | tLambda _ T M =>
	  noccur_between k n T && noccur_between (S k) n M
  | tLetIn _ b t0 b' =>
      noccur_between k n b && noccur_between k n t0 &&
      noccur_between (S k) n b'
  | tApp u v => noccur_between k n u && forallb (noccur_between k n) v
  | tCase _ p c brs =>
      let k' := #|pcontext p| + k in
      let p' :=
        test_predicate (fun _ : Instance.t => true)
          (noccur_between k n) (noccur_between k' n) p in
      let brs' := test_branches_k (fun k0 : nat => noccur_between k0 n) k brs
        in
      p' && noccur_between k n c && brs'
  | tProj _ c => noccur_between k n c
  | tFix mfix _ | tCoFix mfix _ =>
      let k' := #|mfix| + k in
      forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tArray _ arr def ty =>
      forallb (noccur_between k n) arr && noccur_between k n def &&
      noccur_between k n ty
  | _ => true
  end.





(* -> Check which uniform type param are strict pos => list bool
1. given the type of an arg check
2. Check over cstr
3. Check over ind

*)
Unset Guard Checking.

Section SparseParametricity.

  Context (kname : kername).
  Context (mdecl : mutual_inductive_body).
  Context (nb_uparams : nat).
  Context (E : global_env).
  Context (Ep : param_env).

  Definition default_value : list bool :=
  let uparams := firstn nb_uparams (rev mdecl.(ind_params)) in
  let isType decl :=
    let red_ty := reduce_full E init_state decl.(decl_type) in
    let (_, t) := decompose_prod red_ty in
    match t with
    tSort _ => true | _ => false end in
  map isType uparams.

  Definition all_false : list bool := repeat false nb_uparams.

  Definition and_list : list bool -> list bool -> list bool :=
    map2 andb.

  Notation "l1 &&l l2" := (and_list l1 l2) (at level 50).


  Definition get_rel (ty : term) : nat :=
    match ty with
    | tRel i => i
    | _ => 404
    end.

  (* 2. Compute strict pos for an arg *)
Section CheckArg.
  Context (key_inds     : keys).
  Context (key_uparams  : keys).
  Context (key_nuparams : keys).

  Definition check_not_free (s : state) (ty : term) : list bool :=
    map (fun pos => noccur_between pos 1 ty)
        (map get_rel (get_terms s key_uparams)).

  Fixpoint preprocess_strpos_arg (s : state) (ty : term) {struct ty} : list bool :=
    let (hd, iargs) := decompose_app ty in
    match hd with
    (* 1. If it is an product check that id does not appear left of the arrow, and check the right side *)
    | tProd an A B => (check_not_free s A) &&l
                      (let* s _ := add_old_var s (Some "local") an A in
                       preprocess_strpos_arg s B)
    (* 2. If it is a let in, store and check the remaining of the term *)
    | tLetIn an db A B => let* s _ := add_old_letin s (Some "local") an db A in
                          preprocess_strpos_arg s (reduce_lets s B)
    (* 3. If it is variable:  *)
    | tRel n => if check_keys s key_inds n
                (* 3.1 If it is the inductive type being defined, then nothing to check *)
                then default_value
                (* 3.2 Otherwise, check the arguments  *)
                else fold_right and_list default_value (map (fun X => check_not_free s X) iargs)
    (* 3. If it is nested *)
    | tInd (mkInd kname_indb pos_indb) _ =>
        (* Check if there is at least one argument to save computation *)
        if length iargs =? 0 then default_value else
        match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
        | Some (mk_one_param_env _ nb_uparams_indb _ nestable _ _) =>
            (* Retrieve the instantiation *)
            let uparams_inst := firstn nb_uparams_indb iargs in
            let nuparams_indices_inst := skipn nb_uparams_indb iargs in
            (* 3.1 For each uparams_inst:
                - if you can nest on it => check for strict positivity in the instantiation
                - if you can not => check if they appear in it *)
            let strpos_uparams := fold_right (fun ' (b, X) t =>
                if (b : bool) then preprocess_strpos_arg s X &&l t else check_not_free s X)
              default_value (combine nestable uparams_inst) in
            (* 3.2 Check they do not appear in the instantiation of nuparams or indices *)
              let free_nuparams_indices := fold_right (fun X t => check_not_free s X &&l t)
                                              default_value nuparams_indices_inst in
            strpos_uparams &&l free_nuparams_indices
        | None => check_not_free s (mkApps hd iargs)
        end
    | _ => default_value
    end.


  (* Check the uparams does not appear in the types *)
  Definition check_not_free_terms : state -> list term -> list bool :=
    fun s lty => fold_right (fun X t => check_not_free s X &&l t) default_value lty.

End CheckArg.

Definition check_nuparams s (key_uparams key_nuparams : keys) : list bool :=
  (check_not_free_terms key_uparams s (get_types s key_nuparams)).

Definition check_indices s (key_uparams : keys) (mdecl : mutual_inductive_body) : list bool :=
  fold_right (
    fun indices t =>
    let* s _ key_indices _ := add_old_context s None indices in
    (check_not_free_terms key_uparams s (get_types s key_indices)) &&l t
  )
  default_value (map ind_indices (ind_bodies mdecl)).

(* 3. Compute the number of uniform parameters of an inductive type *)
Definition preprocess_strpos : list bool :=
  (* add inds *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s key_inds := add_inds (get_mdecl s kname) s in
  let* s _ key_uparams _  := add_old_context s (Some "uparams") (get_uparams  s kname)  in
  let* s _ key_nuparams _ := add_old_context s (Some "nparams") (get_nuparams s kname) in
  (* 1. Check strict positivity in the arguments *)
  (check_ctors_by_arg and_list default_value E s (preprocess_strpos_arg key_inds key_uparams)
    (get_all_args s kname))
  (* Check the uparams does not appear in the types of the non uniform parameters *)
  &&l (check_nuparams s key_uparams key_nuparams)
  (* Check the uparams does not appear in the types of the indices *)
  &&l (check_indices s key_uparams mdecl).


(* 4. Debug function *)
Section Foo.

Context (key_inds     : keys).
Context (key_uparams  : keys).
Context (key_nuparams : keys).

#[using="All"]
Fixpoint debug_strpos_arg (s : state) (ty : term) {struct ty} : term :=
  let (hd, iargs) := decompose_app ty in
  match hd with
  (* 1. If it is an product check that id does not appear left of the arrow, and check the right side *)
  | tProd an A B =>
                    (let* s _ := add_old_var s (Some "local") an A in
                     debug_strpos_arg s B)
  (* 2. If it is a let in, store and check the remaining of the term *)
  | tLetIn an db A B => let* s _ := add_old_letin s (Some "local") an db A in
                        debug_strpos_arg s (reduce_lets s B)
  (* 3. If it is variable:  *)
  | tRel n => mkApps (tVar "DEBUG:")
                [ state_to_term s;
                  mkApp (tVar "var :=") (tRel n) ;
                  mkApps (tVar "key_inds :=") (map (fun n => tRel n) key_inds);
                  if check_keys s key_inds n then tVar "TRUE" else tVar "FALSE"
                ]
  (* 3. If it is nested *)
  | tInd (mkInd kname_indb pos_indb) _ => tVar "not important"
  | _ => tVar "not important"
  end.

End Foo.


(* Check the uparams does not appear in the types *)
Definition debug_check_not_free_terms key_uparams : state -> list term -> list (list bool) :=
  fun s lty => map (fun X => check_not_free key_uparams s X) lty.

Definition debug_check_nuparams s (key_uparams key_nuparams : keys) : list (list bool) :=
  (debug_check_not_free_terms key_uparams s (get_types s key_nuparams)).

Definition debug_check_indices (s : state) (key_uparams : keys) (mdecl : mutual_inductive_body) : list (list (list bool)) :=
  map ( fun indices =>
    let* s _ key_indices _ := add_old_context s None indices in
    map (check_not_free key_uparams s) (get_types s key_indices)
  )
 (map ind_indices (ind_bodies mdecl)).


Definition debug_preprocess_strpos : list (string × list (string * list bool)) :=
  (* add inds *)
  let s := add_mdecl kname nb_uparams mdecl init_state in
  let* s key_inds := add_inds (get_mdecl s kname) s in
  let* s _ key_uparams _  := add_old_context s (Some "uparams") (get_uparams  s kname) in
  let* s _ key_nuparams _ := add_old_context s (Some "nparams") (get_nuparams s kname) in

  (* Default value *)
  let annot_default_value := ("Debug Default Value:", [("", default_value)]) in
  (* Check strict positivity in the arguments *)
  let debug_ctor := debug_check_ctors_by_arg E s (preprocess_strpos_arg key_inds key_uparams)
                      (get_all_args s kname) in
  let annot_debug_ctor :=
    mapi (fun pos_cstr args => ("Debug Constructor " ^ string_of_nat pos_cstr ^ " : ",
    mapi (fun pos_arg  arg  => ("Debug Arg "         ^ string_of_nat pos_arg ^ " : ", arg)) args)) debug_ctor in

  (* Check the uparams does not appear in the types of the non uniform parameters *)
  let annot_debug_nuparams :=
    mapi (fun i c => ("Debug Nuparams " ^ string_of_nat i ^ " : ", [("",c)]))
          (debug_check_nuparams s key_uparams key_nuparams) in

  (* Check the uparams does not appear in the types of the indices *)
  let annot_debug_indices : list (string * (list (string * list bool))) :=
    mapi (fun pos_indb indices => ("Debug Ind Bloc " ^ string_of_nat pos_indb ^ " : ",
    mapi (fun pos_indice indice  => ("Debug Indice " ^ string_of_nat pos_indice ^ " : ", indice)) indices))
    (debug_check_indices s key_uparams mdecl) in

  (* let nuparams := mapi (fun i t => "Nuparams" ^ string_of_nat i ^ " : " string_of_term t ^ " , ") (get_types key_nuparams )
  let nuparams := [("Nuparams", )] *)

  ("Debug Strictly Positve Uniform Parameters", []) :: annot_default_value ::
  annot_debug_ctor ++ annot_debug_nuparams ++ annot_debug_indices.

End SparseParametricity.
