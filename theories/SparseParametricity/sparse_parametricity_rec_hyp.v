From PluginNestedElim Require Import api_debruijn.

(*
1. Instiates Parametricity with rec call
2. Generates rec call for inductive

*)

(* 1. Instiates Parametricity with rec call *)
Fixpoint add_param (strpos : list bool) (l : list term) (rc : list (option (term * term))) : list term * list term :=
  match strpos, l, rc with
  | nil, nil, nil => (nil , nil)
  | true :: strpos, A::l, x :: rc =>
      let (lty, ltm) := add_param strpos l rc in
      match x with
      | None => (A :: (funTrue A) :: lty, A :: (funTrue A) :: (funI A) :: ltm)
      | Some (ty, tm) => (A::ty::lty, A::ty::tm::ltm)
      end
  | false :: strpos, A::l, x :: rc =>
    let (lty, ltm) := add_param strpos l rc in (A :: lty, A :: ltm)
  | _, _, _ => (nil, nil)
end.


(* 2. Generates rec call for inductive *)
Unset Guard Checking.

Section MkRecCall.

Context (make_indp : state -> nat -> keys -> list term -> list term -> term).
Context (kname : kername).
Context (strpos_uparams : list bool).
Context (Ep : param_env).
Context (s : state).
Context (key_inds          : keys).
Context (key_uparams       : keys).
Context (key_preds         : keys).
Context (key_uparams_preds : keys).
Context (key_preds_hold    : keys).
Context (key_fixs          : keys).


Fixpoint make_cparam_call_aux (s : state) (key_arg : key) (ty : term) {struct ty} : option (term * term) :=
  match view_uparams_args s kname Ep key_inds key_uparams strpos_uparams ty with
  | SPArgIsSPUparam pos_uparams loc iargs  =>
    let deb := (String.concat " | " (map string_of_nat key_preds_hold)) ^ " || " ^ (string_of_nat pos_uparams) in
    (* Some (tVar deb, tVar deb) *)
    Some ( let* s _ key_locals _ := closure_context_sep tProd s (Some "local") loc in
           mkApp (mkApps (geti_term s key_preds pos_uparams) iargs)
                 (mkApps (get_term  s key_arg) (get_terms s key_locals)),
          (* tVar deb) *)
          let* s _ key_locals _ := closure_context_sep tLambda s (Some "local") loc in
          mkApp (mkApps (geti_term s key_preds_hold pos_uparams) iargs)
                (mkApps (get_term  s key_arg) (get_terms s key_locals))
      )
  | SPArgIsInd pos_indb loc local_nuparams local_indices =>
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
      Some (let* s _ key_locals _ := closure_context_sep tProd s (Some "local") loc in
            mkApp (make_indp s pos_indb key_uparams_preds local_nuparams local_indices)
                  (mkApps (get_term s key_arg) (get_terms s key_locals)),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            let* s _ key_locals _ := closure_context_sep tLambda s (Some "local") loc in
            mkApp (mkApps (geti_term s key_fixs pos_indb) (local_nuparams ++ local_indices))
                  (mkApps (get_term s key_arg) (get_terms s key_locals)))
| SPArgIsNested xp pos_indb loc local_uparams local_nuparams_indices _ =>
    let compute_nested_rc (s : state) (x : term) : (option (term * term)) :=
      (* old *)
      let anx := mkBindAnn nAnon Relevant in
      let* s key_farg := add_fresh_var s (Some "rec_arg") anx x in
      match make_cparam_call_aux s key_farg (lift0 1 x) with
      | Some (ty, tm) => Some (tLambda anx x ty, tLambda anx x tm)
      | None => None
      end
    in
    let* s _ key_locals _ := add_old_context s (Some "local") loc in
    let rec_call := map (fun x => compute_nested_rc s x) local_uparams in
    if existsb isSome rec_call
    (* If some instatiate the parametricty  *)
    then let (lty, ltm) := add_param xp.(ep_strpos_uparams) local_uparams rec_call in
        Some ( fold_binder tProd loc (
                mkApp (mkApps (tInd (mkInd xp.(ep_cparam_kname) pos_indb) [])
                              (lty ++ local_nuparams_indices))
                      (mkApps (get_term s key_arg) (get_terms s key_locals))),
                fold_binder tLambda loc (
                mkApp (mkApps (tConst xp.(ep_fdt_kname) [])
                              (ltm ++ local_nuparams_indices))
                              (mkApps (get_term s key_arg) (get_terms s key_locals))))
    else None
| _ => None
end.


#[using="All"]
Definition make_cparam_call : key -> term -> option (term * term) :=
  fun key_arg ty => make_cparam_call_aux s key_arg ty.

End MkRecCall.