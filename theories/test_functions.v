From PluginNestedElim Require Export api_debruijn.

From MetaRocq.Utils Require Export utils.
From MetaRocq.Template Require Export All.
From MetaRocq.Template Require Import Pretty.

(* Preprocessing *)
From PluginNestedElim Require Import uniform_parameters.
From PluginNestedElim Require Import strictly_positive_uniform_parameters.

(* Generation of Recursors *)
From PluginNestedElim Require Import eliminators.

(* Generation of Functoriality *)
(* From PluginNestedElim Require Import functoriality. *)
(* From PluginNestedElim Require Import recursor_term. *)

(* Generation of Parametricity *)
From PluginNestedElim Require Import sparse_parametricity.
From PluginNestedElim Require Import local_fundamental_lemma.


From MetaRocq.Utils Require Import monad_utils.
Import MRMonadNotation.


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

Definition getInd (q : qualid) : TemplateMonad mutual_inductive_body :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => tmQuoteInductive ind.(inductive_mind)
  | _ => tmFail ("[" ^ q ^ "] is not an inductive")
  end.

Definition getCst (q : qualid) b : TemplateMonad constant_body :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => tmQuoteConstant kn b
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

Definition getCstBody (q : qualid) b : TemplateMonad (option term) :=
  x <- (getCst q b) ;;
  tmEval all x.(cst_body).

Definition getCstType (q : qualid) b : TemplateMonad term :=
x <- (getCst q b) ;;
tmEval all x.(cst_type).


Definition printMdecl (q : qualid): TemplateMonad unit :=
  getInd q >>= tmPrint.

Definition printMentry (q : qualid): TemplateMonad unit :=
  mdecl <- getInd q ;;
  mentry <- tmEval cbv (mind_body_to_entry mdecl) ;;
  tmPrint mentry.

Definition pp_printMdecl (q : qualid): TemplateMonad unit :=
  mdecl <- getInd q ;;
  str <- tmEval cbv (print_mib empty_global_env false false mdecl) ;;
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
  | Some db => tmEval cbv (print_term empty_global_env_ext [] false db) >>= tmMsg
  | None => tmPrint "None"
  end.

Definition pp_printCstType (q : qualid) b : TemplateMonad unit :=
  ty <- getCstType q b ;;
  str <- tmEval cbv (print_term empty_global_env_ext [] false ty) ;;
  tmMsg str.


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

(* Given an inductive type => returns kname, medecl, kname_param1, kname_param1_term *)
Definition get_paramEp {A} (s : A) Ep : TemplateMonad unit :=
  ' (E, tm) <- tmQuoteRec s ;;
  etm <- tmEval hnf tm ;;
  let ' (hd, iargs) := decompose_app etm in
  match hd with
  | tInd (mkInd kname ind_pos) _ =>
    mdecl <- match lookup_inductive E {| inductive_mind := kname; inductive_ind := 0 |} with Some d => ret d.1 | None => tmFail "assert false" end;;
    nb_uparams <- tmEval cbv (preprocess_uparams kname mdecl E) ;;
    strpos <- tmEval cbv (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
    type_uparams <- tmEval cbv (firstn nb_uparams (rev (map decl_type mdecl.(ind_params)))) ;;
    let q := snd kname in
    cparam_kname <- GetKname (q ^ "ₛ") ;;
    cparam_kname <- tmEval cbv cparam_kname;;
    fdt_kname <- GetKname ("lfl_" ^ q ^ "ₛ") ;;
    fdt_kname <- tmEval cbv fdt_kname;;
    (* func_kname <- GetKname (q ^ "_func") ;;
    func_kname <- tmEval cbv func_kname;; *)
      tmDefinition ("kmp_" ^ q)
      (mk_one_param_env kname nb_uparams type_uparams strpos cparam_kname fdt_kname) ;;
      ret tt
  | _ => tmFail "Not an inductive"
  end.


Definition tmPrintb {A} (b : bool) (a : A) : TemplateMonad unit :=
  if b then a' <- tmEval lazy a ;; tmPrint a' else tmMsg "".

  Inductive TestMode :=
  | TestRecType  : TestMode
  | TestRecTerm  : TestMode
  | TestSparseParam   : TestMode
  | StopTests    : TestMode.


Definition UnquoteAndPrint name (x : term) : TemplateMonad unit :=
  match name with
  | Some na => tmMkDefinition na x
  | None =>
    p <- (tmUnquote x) ;;
    y <- (tmEval hnf p.(my_projT2)) ;;
    tmPrint y
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
    etm <- tmEval hnf tm ;;
    let ' (hd, iargs) := decompose_app etm in
    (* 2. Check and get the mdecl *)
    match hd with
    | tInd (mkInd kname pos_indb) _ =>
      mdecl <- tmQuoteInductive kname ;;
      (* 2.1 Compute uniform parameters *)
      nb_uparams <- tmEval cbv (preprocess_uparams kname mdecl E) ;;
      if debug_uparams
      then tmPrint nb_uparams ;;
           debug_uparam <- tmEval cbv (debug_preprocess_uparams kname mdecl E) ;;
           tmPrint debug_uparams
      (* 2.2 Compute Strictly Positive Uniform Parameters *)
      else strpos_uparams <- tmEval cbv (preprocess_strpos kname mdecl nb_uparams E Ep) ;;
      if debug_strpos
      then tmPrint strpos_uparams ;;
           debug_strpos <- tmEval cbv (debug_preprocess_strpos kname mdecl nb_uparams E Ep) ;;
           tmPrint debug_strpos
      (* 2.3 Check Rec Type || Rec Term || Custom Param *)
      else match m with
      | TestRecType =>
          ty_rec <- tmEval cbv (gen_rec_type kname mdecl nb_uparams U E Ep pos_indb) ;;
          if debug_rec_type then tmPrint ty_rec else UnquoteAndPrint name ty_rec
      | TestRecTerm =>
          tm_rec <- tmEval cbv (gen_rec_term kname mdecl nb_uparams U E Ep pos_indb) ;;
          if debug_rec_term then tmPrint tm_rec else UnquoteAndPrint name tm_rec
      | TestSparseParam =>
          (* Test Generation Custom Parametricty *)
          tmPrint "Custom Parametricty:" ;;
          mentry <- tmEval all (custom_param kname mdecl nb_uparams strpos_uparams U E Ep) ;;
          if debug_cparam then tmPrint mentry else
          tmMkInductive true mentry ;;
          pp_printMdecl ((snd kname) ^ "ₛ") ;;
          knamep <- getKername ((snd kname) ^ "ₛ") ;;
          tmMsg "";;
          (* Test Generation Fundamental Theorem's Type *)
          tmPrint "Fundamental Theorem's Type:" ;;
          fth_ty <- tmEval cbv (local_fundamental_lemma_type kname mdecl nb_uparams strpos_uparams knamep U pos_indb) ;;
          if debug_fth_ty then tmPrint fth_ty else UnquoteAndPrint (Some ("type_lfl_" ^ (snd kname) ^ "ₛ")) fth_ty ;;
          tmMsg "" ;;
          (* Test Generation Fundamental Theorem *)
          tmPrint "Proof of the Fundamental Theorem:" ;;
           fth_tm <- tmEval cbv (local_fundamental_lemma_term kname mdecl nb_uparams strpos_uparams knamep U E Ep pos_indb) ;;
          if debug_fth_tm then tmPrint fth_tm else UnquoteAndPrint (Some ("lfl_" ^ (snd kname) ^ "ₛ")) fth_tm
      | _ => tmMsg ""
      end
    | _ => tmFail " is not an inductive"
    end.


  Definition print_rec_options (m : TestMode) (q : qualid) :=
    match m with
    | TestRecType => if debug_rec_type then printCstType (q ^ "_ind") true else pp_printCstType (q ^ "_ind") true
    | TestRecTerm => if debug_rec_term then printCstBody (q ^ "_ind") true else pp_printCstBody (q ^ "_ind") true
    | TestSparseParam  => if debug_cparam then printCstBody  (q ^ "_param1_term") true else pp_printMdecl (q ^ "_param1")
    | _ => tmMsg ""
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
