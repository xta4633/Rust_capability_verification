From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability_main Require Import generated_code_capability generated_specs_capability generated_template_Obj_get_cap_on.

Set Default Proof Using "Type".

From iris.proofmode Require Import coq_tactics .




Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.







Ltac myunfold_instantiated_evars :=
  repeat
   match goal with
   | H:=EVAR_ID ?x:_
     |- _ =>
         assert_fails is_evar x;
          unfold_instantiated_evar H;idtac "Executing myunfold_instantiated_evars..."
   end.


Ltac myliEnsureInvariant :=
  myunfold_instantiated_evars; try let_bind_envs;
   try liUnfoldSyntax.

Ltac myliRInstantiateEvars :=
  liRInstantiateEvars_hook;
  lazymatch goal with
  | |- (_ < protected ?H)%nat ∧ _ =>
    (* We would like to use [liInst H (S (protected (EVAR_ID _)))],
      but this causes a Error: No such section variable or assumption
      at Qed. time. Maybe this is related to https://github.com/coq/coq/issues/9937 *)
    instantiate_protected H ltac:(fun H => instantiate (1:=((S (protected (EVAR_ID _))))) in (value of H)) ;idtac "Executing 1.1"
  (* For some reason [solve_protected_eq] will sometimes not manage to do this.. *)
  | |- (protected ?a = ?b +:: ?c) ∧ _ =>
    instantiate_protected a ltac:(fun H =>  instantiate (1:= (protected (EVAR_ID _) +:: protected (EVAR_ID _))) in (value of H))
    ;idtac "Executing 1.2"
  (* NOTE: Important: We create new evars, instead of instantiating directly with [b] or [c].
        If [b] or [c] contains another evar, the let-definition for that will not be in scope, which can create trouble at Qed. time *)
  | |- (protected ?a = ?b -:: ?c) ∧ _ =>
    instantiate_protected a ltac:(fun H =>  instantiate (1:= (protected (EVAR_ID _) -:: protected (EVAR_ID _))) in (value of H))
    ;idtac "Executing 1.3"
  (* in this case, we do not want it to instantiate the evar for [a], but rather directly instantiate it with the only possible candidate.
     (if the other side also contains an evar, we would be instantiating less than we could otherwise) *)
  | |- (@eq (hlist _ []) _ (protected ?a)) ∧ _ =>
      instantiate_protected a ltac:(fun H => instantiate (1:= +[]) in (value of H))
    ;idtac "Executing 1.4"
      (*liInst a (+[])*)
  | |- (@eq (hlist _ []) (protected ?a) _) ∧ _ =>
      instantiate_protected a ltac:(fun H => instantiate (1 := +[]) in (value of H))
      (*liInst a (+[])*);idtac "Executing 1.5"

  (* TODO why is this sometimes not done automatically by Lithium? *)
  (*| |- (protected ?H = ?bla) ∧ _ =>*)
      (*liInst H bla*)

    (* TODO: figure out how/when to instantiate evars  *)
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, _] _ @ (protected ?H)) _) => liInst H lt ;idtac "Executing 1.6"
  | |- envs_entails _ (subsume (_ ◁ₗ[?π, ?b] ?r @ ?lt) (_ ◁ₗ[_, protected ?H] _ @ _) _) => liInst H b ;idtac "Executing 1.7"
  end.

Ltac myliRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?π ?E ?L ?s ?fn ?R ?ϝ) =>
    lazymatch s with
    | subst_stmt ?xs ?s =>
      let s' := W.of_stmt s in
      change (subst_stmt xs s) with (subst_stmt xs (W.to_stmt s'));
      refine (tac_fast_apply (tac_simpl_subst E L π _ _ fn R ϝ) _); simpl; unfold W.to_stmt, W.to_expr ;idtac "Executing subst_stmt"
    | _ =>
      let s' := W.of_stmt s in
      lazymatch s' with
      | W.AssignSE _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_assign E L π _ _ _ _ fn R _ ϝ) _) ;idtac "Executing W.AssignSE"
      | W.Return _ => notypeclasses refine (tac_fast_apply (type_return E L π _ fn R ϝ) _) ;idtac "Executing W.Return"
      | W.IfS _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_if E L π _ _ _ fn R _ ϝ) _) ;idtac "Executing IfS"
      | W.Switch _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_switch E L π _ _ _ _ _ fn R ϝ) _) ;idtac "Executing W.Switch"
      | W.Assert _ _ _ => notypeclasses refine (tac_fast_apply (type_assert E L _ _ fn π R ϝ) _) ;idtac "Executing W.Assert"
      | W.Goto ?bid => liRGoto bid ;idtac "Executing W.Goto"
      | W.ExprS _ _ => notypeclasses refine (tac_fast_apply (type_exprs E L _ _ fn R π ϝ) _) ;idtac "Executing W.ExprS"
      | W.SkipS _ => notypeclasses refine (tac_fast_apply (type_skips' E L _ fn R π ϝ) _) ;idtac "Executing W.SkipS"
      | W.StuckS => exfalso ;idtac "Executing W.StuckS"
      | W.AnnotStmt _ (StartLftAnnot ?κ ?κs) _ => notypeclasses refine (tac_fast_apply (type_startlft E L κ κs _ fn R π ϝ) _);idtac "Executing StartLftAnnot"
      | W.AnnotStmt _ (AliasLftAnnot ?κ ?κs) _ => notypeclasses refine (tac_fast_apply (type_alias_lft E L κ κs _ fn R π ϝ) _);idtac "Executing AliasLftAnnot"
      | W.AnnotStmt _ (EndLftAnnot ?κ) _ => notypeclasses refine (tac_fast_apply (type_endlft E L π κ _ fn R ϝ) _);idtac "Executing EndLftAnnot"
      | W.AnnotStmt _ (StratifyContextAnnot) _ => notypeclasses refine (tac_fast_apply (type_stratify_context_annot E L π _ fn R ϝ) _);idtac "Executing StratifyContextAnnot"
      | W.AnnotStmt _ (CopyLftNameAnnot ?n1 ?n2) _ => notypeclasses refine (tac_fast_apply (type_copy_lft_name π E L n1 n2 _ fn R ϝ) _);idtac "Executing CopyLftNameAnnot"
      | W.AnnotStmt _ (DynIncludeLftAnnot ?n1 ?n2) _ => notypeclasses refine (tac_fast_apply (type_dyn_include_lft π E L n1 n2 _ fn R ϝ) _);idtac "Executing DynIncludeLftAnnot"
      | W.AnnotStmt _ (ExtendLftAnnot ?κ) _ => notypeclasses refine (tac_fast_apply (type_extendlft E L π κ _ fn R ϝ) _);idtac "Executing ExtendLftAnnot"
      | _ => fail "do_stmt: unknown stmt" s
      end
    end
  end.


Ltac myliRExpr :=
  lazymatch goal with
  | |- environments.envs_entails ?Δ (typed_val_expr ?π ?E ?L ?e ?T) =>
        let e' := W.of_expr e in
        lazymatch e' with
        | W.Val _ => notypeclasses refine (tac_fast_apply (type_val E L _ π T) _) ;idtac "Executing W.Val"
        | W.Loc _ => notypeclasses refine (tac_fast_apply (type_val E L _ π T) _) ;idtac "Executing W.Loc"
        | W.Use _ _ true _ => notypeclasses refine (tac_fast_apply (type_use E L _ _ _ π T) _) ;idtac "Executing W.Use"
        | W.Borrow Mut _ _ _ => notypeclasses refine
        (tac_fast_apply (type_mut_bor E L T _ π _ _) _) ;idtac "Executing W.Borrow Mut"
        | W.Borrow Shr _ _ _ => notypeclasses refine (tac_fast_apply (type_shr_bor E L T _ π _ _) _) ;idtac "Executing W.Borrow Shr"
        | W.AddrOf _ _ => notypeclasses refine (tac_fast_apply (type_mut_addr_of π E L _ T) _) ;idtac "Executing W.AddrOf"
        | W.BinOp _ _ _ _ _ => notypeclasses refine
        (tac_fast_apply (type_bin_op E L _ _ _ _ _ π T) _) ;idtac "Executing W.BinOp"
        | W.UnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_un_op E L _ _ _ π T) _) ;idtac "Executing W.UnOp"
        | W.Call _ _ _ => notypeclasses refine (tac_fast_apply (type_call E L π T _ _ _) _) ;idtac "Executing W.Call"
        | W.AnnotExpr _ ?a _ => notypeclasses refine
        (tac_fast_apply (type_annot_expr E L _ a _ π T) _) ;idtac "Executing W.AnnotExpr"
        | W.StructInit ?sls ?init => notypeclasses refine
        (tac_fast_apply (type_struct_init π E L sls _ T) _) ;idtac "Executing W.StructInit"
        | W.EnumInit ?els ?variant ?rsty ?init => notypeclasses refine
        (tac_fast_apply (type_enum_init π E L els variant rsty _ T) _) ;idtac "Executing W.EnumInit"
        | W.IfE _ _ _ _ => notypeclasses refine
        (tac_fast_apply (type_ife E L _ _ _ π T) _) ;idtac "Executing W.IfE"
        | W.LogicalAnd _ _ _ _ _ => notypeclasses refine
        (tac_fast_apply (type_logical_and E L _ _ _ _ π T) _) ;idtac "Executing W.LogicalAnd"
        | W.LogicalOr _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_or E L _ _ _ _ π T) _) ;idtac "Executing W.LogicalOr"
        | _ => fail "do_expr: unknown expr" e
        end
  end
.



Ltac myliRJudgement :=
  lazymatch goal with
    (* place finish *)
    | |- envs_entails _ (typed_place_finish ?π ?E ?L _ _ _ _ _ _ _ _ _ ?T) =>
      (* simplify eqcasts and the match on strong/weak branch *)
      cbn ;idtac "Executing place finish"
    (* write *)
    | |- envs_entails _ (typed_write ?π ?E ?L _ _ _ ?ty ?r ?T) =>
        notypeclasses refine (tac_fast_apply (type_write E L T _ _ _ _ _ ty r π _) _); [ solve [refine _ ] |]
        ;idtac "Executing write"
    (* read *)
    | |- envs_entails _ (typed_read ?π ?E ?L _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_read π E L T _ _ _ _) _); [ solve [refine _ ] |]
        ;idtac "Executing read"
    (* borrow mut *)
    | |- envs_entails _ (typed_borrow_mut ?π ?E ?L _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_mut E L T _ _ _ π _ _) _); [solve [refine _] |]
        ;idtac "Executing place finish"
    (* borrow shr *)
    | |- envs_entails _ (typed_borrow_shr ?π ?E ?L _ _ _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_borrow_shr E L T _ _ _ _ π _) _); [solve [refine _] |]
        ;idtac "Executing borrow shr"
    (* addr_of mut *)
    | |- envs_entails _ (typed_addr_of_mut ?π ?E ?L _ ?T) =>
        notypeclasses refine (tac_fast_apply (type_addr_of_mut π E L _ T _ _) _); [solve [refine _] |]
        ;idtac "Executing addr_of mut"
    (* end context folding *)
    | |- envs_entails _ (typed_context_fold_end ?AI ?π ?E ?L ?acc ?T) =>
        notypeclasses refine (tac_fast_apply (type_context_fold_end AI E L π acc T) _)
        ;idtac "Executing end context folding"
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?π ?E ?L (CtxFoldStratifyAllInit) ?T) =>
        liRContextStratifyInit
        ;idtac "Executing initialize context folding "
    (* unblocking step *)
    | |- envs_entails _ (typed_context_fold_step ?AI ?π ?E ?L (CtxFoldStratifyAll) ?l ?lt ?r ?tctx ?acc ?T) =>
        liRContextStratifyStep
        ;idtac "Executing unblocking step"
    (* initialize context folding *)
    | |- envs_entails _ (typed_pre_context_fold ?π ?E ?L (CtxFoldExtractAllInit ?κ) ?T) =>
        liRContextExtractInit
        ;idtac "Executing initialize context folding"
    (* unblocking step *)
    | |- envs_entails _ (typed_context_fold_step ?AI ?π ?E ?L (CtxFoldExtractAll ?κ) ?l ?lt ?r ?tctx ?acc ?T) =>
        liRContextExtractStep
        ;idtac "Executing unblocking step"
    (* initialize OnEndlft triggers *)
    | |- envs_entails _ (typed_on_endlft_pre ?π ?E ?L ?κ ?T) =>
        liROnEndlftTriggerInit
        ;idtac "Executing OnEndlft triggers"
    (* trigger tc search *)
    | |- envs_entails _ (trigger_tc ?H ?T) =>
        notypeclasses refine (tac_fast_apply (tac_trigger_tc _ _ _ _) _); [solve [refine _] | ]
        ;idtac "Executing trigger tc search"
    (* stratification for structs *)
    | |- envs_entails _ (@stratify_ltype_struct_iter _ _ ?π ?E ?L ?mu ?mdu ?ma _ ?m ?l ?i ?sls ?rts ?lts ?rs ?k ?T) =>
        match rts with
        | [] =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_nil π E L mu mdu ma m l sls k i T) _)
        | _ :: _ =>
          notypeclasses refine (tac_fast_apply (stratify_ltype_struct_iter_cons π E L mu mdu ma m l sls i _ _ _ k _) _)
        end ;idtac "Executing stratification for structs"
  end.

Ltac myliStep :=
  first [
      liExtensible ;idtac "Executing liExtensible"
    | liSep ;idtac "Executing liSep"
    | liAnd ;idtac "Executing liAnd"
    | liWand ;idtac "Executing liWand"
    | liExist ;idtac "Executing liExist"
    | liImpl ;idtac "Executing liImpl"
    | liForall ;idtac "Executing liForall"
    | liSideCond ;idtac "Executing liSideCond"
    | liFindInContext ;idtac "Executing liFindInContext"
    | liCase ;idtac "Executing liCase"
    | liTrace ;idtac "Executing liTrace"
    | liTactic ;idtac "Executing liTactic"
    | liPersistent ;idtac "Executing liPersistent"
    | liTrue ;idtac "Executing liTrue"
    | liFalse ;idtac "Executing liFalse"
    | liAccu ;idtac "Executing liAccu"
    | liUnfoldLetGoal ;idtac "Executing liUnfoldLetGoal"
    ].

Ltac myliRIntroduceTypedStmt :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (introduce_typed_stmt ?π ?E ?L ?ϝ ?fn ?lsa ?lsv ?lya ?lyv ?R) =>
    iEval (rewrite /introduce_typed_stmt /to_runtime_function /subst_function !fmap_insert fmap_empty; simpl_subst);
      lazymatch goal with
      | |- @envs_entails ?PROP ?Δ (@typed_stmt ?Σ ?tG ?π ?E ?L ?s ?fn ?R ?ϝ) =>
        let Hfn := fresh "FN" in
        let HR := fresh "R" in
        pose (Hfn := (CODE_MARKER fn));
        pose (HR := (RETURN_MARKER R));
        change_no_check (@envs_entails PROP Δ (@typed_stmt Σ tG π E L s Hfn HR ϝ));
        iEval (simpl) (* To simplify f_init *)
        (*notypeclasses refine (tac_fast_apply (tac_simplify_elctx _ _ _ _ _ _ _ _ _) _); [simplify_elctx | ]*)
      end
  end.

Ltac myliRStep :=
  myliEnsureInvariant; try liRIntroduceLetInGoal;
   simp_ltypes; simplify_layout_goal; (first
   [ myliRInstantiateEvars;idtac "Executing liRInstantiateEvars..."
   | myliRStmt;idtac "Executing liRStmt..."
   | liRIntroduceTypedStmt; idtac "Executing liRIntroduceTypedStmt..."
   | myliRExpr;idtac "Executing liRExpr..."
   | myliRJudgement;idtac "Executing liRJudgement..."
   | myliStep;idtac "Executing liStep..."
   | lazymatch goal with
     | |- BACKTRACK_POINT ?P => change_no_check P
     end;idtac "Executing change_no_check" ]); try unfold_introduce_direct; liSimpl; idtac "**************************************************".


Section proof.
Context `{!refinedrustGS Σ}.

Lemma Obj_get_cap_on_proof (π : thread_id) :
  ref_to_loc_def -> Obj_get_cap_on_lemma π.
Proof.
  intros Htest .
  Obj_get_cap_on_prelude.
  Search (CACHED).
  iIntros "credit_store".

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  
  myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  (*start function proof*)
  myliRStep; liShow. myliRStep; liShow.

  (*annot: CopyLftNameAnnot *)
  myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. 





  (*annot: CopyLftNameAnnot *)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 

  (*local___3 <-{PtrOp} AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft11" LftNameTreeLeaf))
                         &ref{Shr,None,"vlft4"} (!{PtrOp}arg_self at{Obj_sls} "caps")*)
  myliRStep; liShow.
  

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.

  (*check block??*)

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow.

  (*ocal___6 <-{PtrOp} &raw{Shr} (!{PtrOp}arg_obj);*)

  myliRStep; liShow. 
  

(*   myliEnsureInvariant; try liRIntroduceLetInGoal;
   simp_ltypes; simplify_layout_goal. notypeclasses refine (tac_fast_apply (type_mut_addr_of π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [ϝ ⊑ₗ{ 0} []] _ GOAL) _).
  li_unfold_lets_in_context. *)
  myliRStep; liShow. 
(*   myliEnsureInvariant; try liRIntroduceLetInGoal.
  notypeclasses refine (tac_fast_apply (type_addr_of_mut π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [ϝ ⊑ₗ{ 0} []] _ (λ (L' : llctx) (v : val) (rt : Type) (ty : type rt) (r : rt),
        [{ exhale True;
           {typed_write π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] L' local___6 PtrOp v ty r
              (λ L2 : llctx,
                 introduce_with_hooks [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] L2
                   [{ exhale atime 2; {£ num_cred} }]
                   (λ L3 : llctx,
                      typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] L3
                        (annot: StartLftAnnot "llft5" ["ulft_1"]; local___5 <-{PtrOp} 
                                                                  AnnotExpr 0
                                                                    (GetLftNamesAnnot
                                                                       (LftNameTreeRef "plft13" LftNameTreeLeaf))
                                                                    &ref{Shr,None,"llft5"} local___6;
                                                                  annot: CopyLftNameAnnot "vlft6" "plft13"; annot: 
                                                                  CopyLftNameAnnot "vlft6" "plft13"; 
                                                                  local___4 <-{PtrOp} 
                                                                  AnnotExpr 0
                                                                    (GetLftNamesAnnot
                                                                       (LftNameTreeRef "plft12" LftNameTreeLeaf))
                                                                    &ref{Shr,None,"vlft6"} 
                                                                    (!{PtrOp}local___5);
                                                                  annot: CopyLftNameAnnot "vlft15" "plft12"; annot: 
                                                                  CopyLftNameAnnot "vlft14" "plft11"; 
                                                                  local___0 <-{use_op_alg' (Option_els PtrSynType)} 
                                                                  CallE
                                                                    BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc
                                                                    ["vlft15"; "vlft14"]
                                                                    [use{PtrOp} local___3; use{PtrOp} local___4];
                                                                  annot: EndLftAnnot "llft5"; 
                                                                  Goto "_bb1") FN R ϝ))}
        }]) _ _) _).
  2:{ liShow. simpl.
  { simpl. instantiate (1:= [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1]).
    solve refine _. [refine _] 
     eapply find_place_ctx_correct. *)

  myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.

 myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow.

  (*
  Search (OpenedLtype (AliasLtype _ _ _)).


  unfold test2 in Htest.
  specialize (Htest l'0).
  specialize (Htest obj).
  specialize (Htest π).
  iSelect (local___6 ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "H6").
  iSelect (l'0 ◁ₗ[_, _] _ @ _)%I (fun H => iRename H into "Hl'0").
  iApply (Htest with "[Hl'0]").
  { 


    
    iApply "Hl'0".
    
} 
  2:{ instantiate(1:= l'0).
      instantiate(1:= obj).
      instantiate(1:= π).
myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. intros.  *)


  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 

  (*annot: StartLftAnnot "llft5" [];*)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 

  (*local___5 <-{PtrOp} AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" LftNameTreeLeaf)) &ref{Shr,None,"llft5"} local___6;*)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.


  (*annot: CopyLftNameAnnot "vlft6" "plft13"; annot: CopyLftNameAnnot "vlft6" "plft13";*) 
  

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.

  (*local___4 <-{PtrOp} AnnotExpr 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" LftNameTreeLeaf)) &ref{Shr,None,"vlft6"} (!{PtrOp}local___5)*)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.



  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. 

  (*  (annot: CopyLftNameAnnot "vlft15" "plft12"; annot: CopyLftNameAnnot "vlft14" "plft11";*)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.



  (* local___0 <-{use_op_alg' (Option_els PtrSynType)} CallE
                                                       BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc
                                                       ["vlft14"; "vlft15"]
                                                       [use{PtrOp} local___3; use{PtrOp} local___4] *)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.



   myliRStep; liShow. myliRStep; liShow.



  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. 



  split. + simpl. intros. unfold_all_protected_evars. eauto.
  +




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  split. 
  { intros. simpl.
    eapply elctx_sat_app. 
    { rewrite ty_outlives_E_eq. simpl.
      unfold lfts_outlives_E. simpl.
      eapply elctx_sat_nil. }
    eapply elctx_sat_app.
    1 : { eapply elctx_sat_app.
          {
          rewrite ty_outlives_E_eq. unfold lfts_outlives_E. simpl.
          eapply elctx_sat_lft_incl.
          { simpl. eapply lctx_lft_incl_external'.
            { instantiate(1:= ϝ). eauto. Search (_ ∈ _). eapply elem_of_list_In. right. left. eauto. }
            eapply lctx_lft_incl_external. eapply elem_of_list_In. right. right. left. eauto. } 
          eapply elctx_sat_nil. }
        { rewrite ty_outlives_E_eq. unfold lfts_outlives_E. simpl.
          eapply elctx_sat_lft_incl. { eapply lctx_lft_incl_external. eapply elem_of_list_In. left. eauto. }
          eapply elctx_sat_nil.
        }}
      eapply elctx_sat_app.
      { rewrite ty_outlives_E_eq. unfold lfts_outlives_E. simpl. eapply elctx_sat_nil. }
      { rewrite ty_outlives_E_eq. unfold lfts_outlives_E. simpl.
        eapply elctx_sat_lft_incl.
          { simpl. eapply lctx_lft_incl_external'.
            { instantiate(1:= ϝ). eauto. eapply elem_of_list_In. right. left. eauto. }
            eapply lctx_lft_incl_external. eapply elem_of_list_In. right. right. left. eauto. }
        eapply elctx_sat_nil.
      }
    }

         
    



  myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.



  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. 



(* 
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer. 



  Unshelve.
  3:{ exact ∅. }
  1:{ 
      unfold lctx_lft_incl_list. simpl.
      Search ( _ -> lctx_lft_incl _ _ _ _).
      eapply lctx_lft_incl_intersect.
      2: eapply lctx_lft_incl_refl.
      Search ( _ -> lctx_lft_incl _ _ _ _).
      eapply lctx_lft_incl_external.
  
 eapply tac_lctx_lft_incl_list_augment_local_owned.
      2: instantiate(2:= 0); eauto.
      1: instantiate(3:=0); eauto.
      simpl *)

  (*Goto "_bb1"*)
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.


  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.




  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow.   

  unfold_all_protected_evars.



  instantiate (1:= l'0) . 

  myliRStep; liShow. 

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 

  
  myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

      
    

Qed.

End proof.





