From MetaRocq.NestedElim Require Import core.

(* Add Inductive Types
- add_mdecl : kername -> nat -> mutual_inductive_body -> state -> state
*)

Definition add_mdecl : kername -> nat -> mutual_inductive_body -> state -> state :=
  fun kname nb_uparams mdecl s =>
    let rev_params := rev mdecl.(ind_params) in
    add_pdecl (
      mk_pdecl kname
               (rev (firstn nb_uparams rev_params)) nb_uparams
               (rev (skipn nb_uparams rev_params)) (mdecl.(ind_npars) - nb_uparams)
               mdecl) s.