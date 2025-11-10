From MetaRocq.NestedElim Require Export api_debruijn.

From MetaRocq.Utils Require Export utils Show.
From MetaRocq.Template Require Export All.
From MetaRocq.Template Require Import Pretty.

(* Preprocessing *)
From MetaRocq.NestedElim Require Import uniform_parameters.
From MetaRocq.NestedElim Require Import strictly_positive_uniform_parameters.

(* Generation of Recursors *)
From MetaRocq.NestedElim Require Import eliminators.

(* Generation of Functoriality *)
(* From MetaRocq.NestedElim Require Import functoriality. *)
(* From MetaRocq.NestedElim Require Import recursor_term. *)

(* Generation of Parametricity *)
From MetaRocq.NestedElim Require Import sparse_parametricity.
From MetaRocq.NestedElim Require Import local_fundamental_lemma.


From MetaRocq.Utils Require Import monad_utils.
Import MRMonadNotation.

Instance show_globref : Show global_reference := string_of_gref.
Instance show_kername : Show kername := string_of_kername.
(* Definition preprocess_uparams : kername -> mutual_inductive_body -> global_env -> nat :=
  fun _ mdecl _ => 0.

Definition debug_preprocess_uparams : kername -> mutual_inductive_body -> global_env -> list (list nat) :=
  fun _ _ _ => []. *)

(* Definition preprocess_strpos : kername -> mutual_inductive_body -> global_env -> list bool :=
  fun _ mdecl _ => repeat true mdecl.(ind_npars). *)

(* Definition error_mentry : mutual_inductive_entry :=
  Build_mutual_inductive_entry None Finite [] [] (Monomorphic_entry ContextSet.empty) false None None. *)


(* ############################
   ###  Printing functions  ###
   ############################ *)

Definition getKername (q : qualid) : TemplateMonad kername :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef (mkInd kname _) => tmReturn kname
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition from_opt {A} (o : option A) e : TemplateMonad A :=
  match o with
  | Some x => ret x
  | None => tmFail e
  end.

Section EnvironmentAccess.
  Context (Σ : global_env).

Definition ind_of_kn (kn : kername) :=
  from_opt (lookup_minductive Σ kn) ("inductive " ^ show kn ^ " not found").

Definition ind_of_gref (kn : global_reference) : TemplateMonad mutual_inductive_body :=
  match kn with
  | IndRef ind => ind_of_kn ind.(inductive_mind)
  | _ => tmFail ("[" ^ string_of_gref kn ^ "] is not an inductive")
  end.

Definition getInd (q : qualid) : TemplateMonad mutual_inductive_body :=
  kn <- tmLocate1 q ;; ind_of_gref kn.

Definition cst_of_kn kn :=
  from_opt (lookup_constant Σ kn) ("constant " ^ show kn ^ " not found").

Definition cst_of_gref (kn : global_reference) : TemplateMonad _ :=
  match kn with
  | ConstRef kn => cst_of_kn kn
  | _ => tmFail ("[" ^ show kn ^ "] is not a constant")
  end.

Definition getCst (q : qualid) (b : bool) : TemplateMonad constant_body :=
  kn <- tmLocate1 q ;; cst_of_gref kn.

Definition getCstBody (q : qualid) b : TemplateMonad (option term) :=
  x <- (getCst q b) ;;
  ret x.(cst_body).

Definition getCstType (q : qualid) b : TemplateMonad term :=
x <- (getCst q b) ;;
ret x.(cst_type).

Definition printMdecl (q : qualid): TemplateMonad unit :=
  getInd q >>= tmPrint.

Definition printMentry (q : qualid): TemplateMonad unit :=
  mdecl <- getInd q ;;
  mentry <- tmEval lazy (mind_body_to_entry mdecl) ;;
  tmPrint mentry.

Definition pp_printMdecl (q : qualid): TemplateMonad unit :=
  mdecl <- getInd q ;;
  str <- tmEval lazy (print_mib empty_global_env false false mdecl) ;;
  tmMsg str.

Definition printCstBody (q : qualid) b : TemplateMonad unit :=
  getCstBody q b >>= tmPrint.

Definition printCstType (q : qualid) b : TemplateMonad unit :=
  getCstType q b >>= tmPrint.

Definition empty_global_env_ext : global_env_ext :=
  (empty_global_env, Monomorphic_ctx).

Definition pp_printCstBody (q : qualid) b : TemplateMonad unit :=
  db <- getCstBody q b ;;
  match db with
  | Some db => tmEval lazy (print_term empty_global_env_ext [] false db) >>= tmMsg
  | None => tmPrint "None"
  end.

Definition pp_printCstType (q : qualid) b : TemplateMonad unit :=
  ty <- getCstType q b ;;
  str <- tmEval lazy (print_term empty_global_env_ext [] false ty) ;;
  tmMsg str.

  Inductive TestMode :=
  | TestRecType  : TestMode
  | TestRecTerm  : TestMode
  | TestSparseParam   : TestMode
  | StopTests    : TestMode.
    Definition print_rec_options (debug_rec_type debug_rec_term debug_cparam : bool) (m : TestMode) (q : qualid) :=
    match m with
    | TestRecType =>
      if debug_rec_type then printCstType (q ^ "_ind") true else pp_printCstType (q ^ "_ind") true
    | TestRecTerm => if debug_rec_term then printCstBody (q ^ "_ind") true else pp_printCstBody (q ^ "_ind") true
    | TestSparseParam  => if debug_cparam then printCstBody  (q ^ "_param1_term") true else pp_printMdecl (q ^ "_param1")
    | _ => tmMsg ""
    end.

End EnvironmentAccess.


(* ############################
   ###    Tests Functions   ###
   ############################ *)

Definition GetKname : qualid -> TemplateMonad kername :=
  fun q => gref <- tmLocate1 q ;;
  match gref with
  | IndRef x => tmReturn x.(inductive_mind)
  | ConstRef kname => tmReturn kname
  | _ => tmFail (String.append "Error getting kername of " q)
  end.



Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then a' <- tmEval lazy a ;; tmPrint a' else tmMsg "".



Definition UnquoteAndPrint name (x : term) : TemplateMonad unit :=
  match name with
  | Some na => tmMkDefinition na x
  | None =>
    p <- (tmUnquote x) ;;
    y <- (tmEval hnf p.(my_projT2)) ;;
    tmPrint y
  end.


About GetKname.
Print qualid.
Set Printing All.
Unset Printing Notations.
(* Given an inductive type => returns kname, medecl, kname_param1, kname_param1_term *)
(* Definition get_paramEp {A} (s : A) (Ep : param_env) : TemplateMonad unit :=
  x <- tmQuoteRec s ;;
  let '(E, tm) := x return TemplateMonad unit in
  etm <- tmEval lazy (tm : term) ;;
  let ' (hd, iargs) := decompose_app etm return TemplateMonad unit in
  match hd return TemplateMonad unit with
  | tInd (mkInd kname ind_pos) _ =>
    tmBind (ind_of_kn kname) (fun mdecl =>
    tmBind (tmEval lazy ((preprocess_uparams kname mdecl (E : global_env)) : nat)) (fun nb_uparams =>
    (* strpos <- tmEval lazy (preprocess_strpos kname mdecl nb_uparams E Ep) ;; *)
    (* type_uparams <- tmEval lazy (firstn nb_uparams (rev (map decl_type mdecl.(ind_params)))) ;; *)
    let q := snd kname in
    tmBind (B := unit) (GetKname (q ^ "ₛ")) (fun _ : kername =>
    (* cparam_kname <- tmEval lazy cparam_kname;; *)
    (* fdt_kname <- GetKname ("lfl_" ^ q ^ "ₛ") ;; *)
    (* fdt_kname <- tmEval lazy fdt_kname;; *)
    (* func_kname <- GetKname (q ^ "_func") ;;
    func_kname <- tmEval lazy func_kname;; *)
    (* tmDefinition ("kmp_" ^ q) *)
      (* (mk_one_param_env kname nb_uparams type_uparams strpos cparam_kname fdt_kname) ;; *)
      ret tt)))
  | _ => tmFail "Not an inductive"
  end. *)

Definition get_paramEp {A} (s : A) (Ep : param_env) : TemplateMonad unit :=
  ' (E, tm) <- tmQuoteRecTransp s false ;;
  let ' (hd, iargs) := decompose_app tm in
  match hd with
  | tInd (mkInd kname ind_pos) _ =>
    mdecl <- ind_of_kn E kname ;;
    mdeck <- tmEval lazy mdecl ;;
    nb_uparams <- tmEval lazy (preprocess_uparams kname mdecl E) ;;
    strpos <- tmEval lazy (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
    let type_uparams := firstn nb_uparams (rev (map decl_type mdecl.(ind_params))) in
    let q := snd kname in
    cparam_kname <- GetKname (q ^ "ₛ")%bs ;;
    fdt_kname <- GetKname ("lfl_" ^ q ^ "ₛ") ;;
    tmDefinition ("kmp_" ^ q)
      (mk_one_param_env kname nb_uparams type_uparams strpos cparam_kname fdt_kname) ;;
      ret tt
  | _ => tmFail "Not an inductive"
  end.

Section TestFunctions.
  Context (debug_uparams debug_strpos : bool).
  Context (m : TestMode).
  Context (debug_rec_type debug_rec_term : bool).
  Context (debug_func_type debug_func_term : bool).
  Context (debug_cparam debug_fth_ty debug_fth_tm : bool).
  Context (Ep : param_env).
  Context (name : option ident).
  Context (output_univ : option Sort.t).

  Definition U :=
    match output_univ with
    | None => mk_output_univ (tSort sProp) (relev_sort (tSort sProp))
    | Some u => mk_output_univ (tSort u) (relev_sort (tSort u))
    end.

  #[using="All"]
  Definition generate_options {A} (s : A) : TemplateMonad unit :=
    (* 1. Get env and term *)
    x <- tmQuoteRecTransp s false ;;
    let ' (E, tm) := x in
    (* Ena <- tmFreshName "quoted_env" ;; *)
    (* tmDefinition Ena E ;; Record the global environment as a separate definition. Stop using the (large) term afterwards.     *)
    let ' (hd, iargs) := decompose_app tm in
    (* 2. Check and get the mdecl *)
    match hd with
    | tInd (mkInd kname pos_indb) _ =>
      mdecl <- ind_of_kn E kname ;;
      mdecl <- tmEval lazy mdecl ;;
      (* 2.1 Compute uniform parameters *)
      nb_uparams <- tmEval lazy (preprocess_uparams kname mdecl E) ;;
      if debug_uparams
      then tmPrint nb_uparams ;;
           let debug_uparam := debug_preprocess_uparams kname mdecl E in
           tmPrint debug_uparams
      (* 2.2 Compute Strictly Positive Uniform Parameters *)
      else
      strpos_uparams <- tmEval lazy (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
      if debug_strpos
      then tmPrint strpos_uparams ;;
           debug_strpos <- tmEval lazy (debug_preprocess_strpos kname mdecl nb_uparams E Ep) ;;
           tmPrint debug_strpos
      (* 2.3 Check Rec Type || Rec Term || Custom Param *)
      else match m with
      | TestRecType =>
          ty_rec <- tmEval lazy (gen_rec_type kname mdecl nb_uparams U E Ep pos_indb) ;;
          if debug_rec_type then tmPrint ty_rec else UnquoteAndPrint name ty_rec
      | TestRecTerm =>
          tm_rec <- tmEval lazy (gen_rec_term kname mdecl nb_uparams U E Ep pos_indb) ;;
          if debug_rec_term then tmPrint tm_rec else UnquoteAndPrint name tm_rec
      | TestSparseParam =>
          (* Test Generation Custom Parametricty *)
          tmPrint "Custom Parametricty:" ;;
          mentry <- tmEval lazy (custom_param kname mdecl nb_uparams strpos_uparams U E Ep) ;;
          if debug_cparam then tmPrint mentry else
          tmMkInductive true mentry ;;
          knamep <- getKername ((snd kname) ^ "ₛ") ;;
          tmMsg "";;
          (* Test Generation Fundamental Theorem's Type *)
          tmPrint "Fundamental Theorem's Type:" ;;
          fth_ty <- tmEval lazy (local_fundamental_lemma_type kname mdecl nb_uparams strpos_uparams knamep U pos_indb) ;;
          if debug_fth_ty then tmPrint fth_ty else UnquoteAndPrint (Some ("type_lfl_" ^ (snd kname) ^ "ₛ")) fth_ty ;;
          tmMsg "" ;;
          (* Test Generation Fundamental Theorem *)
          tmPrint "Proof of the Fundamental Theorem:" ;;
           fth_tm <- tmEval lazy (local_fundamental_lemma_term kname mdecl nb_uparams strpos_uparams knamep U E Ep pos_indb) ;;
          if debug_fth_tm then tmPrint fth_tm else UnquoteAndPrint (Some ("lfl_" ^ (snd kname) ^ "ₛ")) fth_tm
      | _ => tmMsg ""
      end
    | _ => tmFail " is not an inductive"
    end.

End TestFunctions.




  (* DEBUG FUNCTIONS *)
(* -------------------------------------------------------------------------- *)

    (* ### Debug Preprocessing ### *)

(* Definition print_rec := print_rec_options false false false StopTests.
Definition generate {A} Ep : A -> _ := generate_options true false StopTests
                                        false false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false StopTests.
Definition generate {A} Ep : A -> _ := generate_options false true StopTests
                                        false false false false false false false Ep. *)

    (* ### Debug Recursor ### *)

(* Definition print_rec := print_rec_options true false false TestRecType.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecType
                                        true false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false true false TestRecTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecTerm
                                        false true false false false false false Ep. *)

    (* ### Debug Functoriality *)

(* Definition print_rec := print_rec_options false false false TestFuncType.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncType
                                        false false true false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false TestFuncTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncTerm
                                        false false false true false false false Ep. *)

    (* ### Debug Custom Param ### *)

(* Definition print_rec := print_rec_options false false true TestSparseParam. *)
(* Definition generate {A} Ep : A -> _ := generate_options false false TestSparseParam
                                        false false false false true false false Ep "foo" None. *)




  (* TEST FUNCTIONS *)
(* -------------------------------------------------------------------------- *)

    (* ### Test Recursors  ### *)

(* Definition print_rec := print_rec_options false false false TestRecType.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecType
                                        false false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false TestRecTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestRecTerm
                                        false false false false false false false Ep None None. *)

    (* ### Test Functoriality  ### *)

(* Definition print_rec := print_rec_options false false false TestFuncType.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncType
                                        false false false false false false false Ep. *)

(* Definition print_rec := print_rec_options false false false TestFuncTerm.
Definition generate {A} Ep : A -> _ := generate_options false false TestFuncTerm
                                        false false false false false false false Ep. *)

    (* ### Test Custom Param ### *)

(* Definition print_rec := print_rec_options true false false TestSparseParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestSparseParam
                                        false false false false false true false Ep. *)

(* Definition print_rec := print_rec_options true false false TestSparseParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestSparseParam
                                        false false false false false false true Ep. *)

(* Definition print_rec := print_rec_options true false false TestSparseParam.
Definition generate {A} Ep : A -> _ := generate_options false false TestSparseParam
                                        false false false false false false false Ep. *)

Definition generate_elim {A} Ep na u : A -> _ := generate_options false false TestRecTerm
                                        false false false false false false false Ep (Some na) (Some u).

Definition generate_sparse_parametricty {A} Ep u : A -> _ := generate_options false false TestSparseParam
                                        false false false false false false false Ep None (Some u).
