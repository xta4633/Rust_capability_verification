From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.cap1.generated Require Import generated_code_cap1 generated_specs_cap1 generated_template_Obj_try_take_action_mut.

From iris.proofmode Require Import coq_tactics .
Set Default Proof Using "Type".

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

Ltac tryfalse :=
      try solve [congruence | discriminate | assumption].

Definition Htest :=
forall x y , ref_to_loc x y.

Definition ident :=
  forall (self: BTreeMap_inv_t_rt loc Cap_inv_t_rt Global_rt) (l: loc) 
    {LookupTotalInstance : LookupTotal loc (place_rfn (loc * Z)) (BTreeMap_inv_t_rt loc Cap_inv_t_rt Global_rt)}, 
    exists (x: loc * Z), self !!! l = #x.

Section proof.
Context `{!refinedrustGS Σ}.

Lemma Obj_try_take_action_mut_proof (π : thread_id) :
  Htest -> ident -> Obj_try_take_action_mut_lemma π.
Proof.
  intros Htest ident.
  Obj_try_take_action_mut_prelude.
     do 100 myliRStep; liShow. 
     do 100 myliRStep; liShow.
     do 100 myliRStep; liShow.
     do 100 myliRStep; liShow.
     do 100 myliRStep; liShow.
     do 50 myliRStep; liShow.
     do 10 myliRStep; liShow.  
    myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. 
  myliRStep; liShow. 
(*   typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [ϝ ⊑ₗ{ 0} []] (Goto "_bb0") FN R ϝ *)
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
  do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
  do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
  do 20 myliRStep; liShow. do 20 myliRStep; liShow.

myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
split. {   unfold_all_protected_evars. 
           instantiate(1:=(Global_ty )).
           instantiate(1:=(Cap_inv_t )).
           instantiate(1:=(alias_ptr_t)). eauto. }
       
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
       do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
       do 20 myliRStep; liShow. do 20 myliRStep; liShow. do 10 myliRStep; liShow.
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow. 
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow. 
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
       do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
       myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow.  myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow.
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] 
  (Goto "_bb1") FN R ϝ *)
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
       do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
        unfold_all_protected_evars. 
        instantiate(3:=(mut_ref Cap_inv_t κ)). 
        instantiate(1:=(if decide (is_Some (self !! l'0)) then Some # (self !!! l'0, x') else None)). 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
       do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
       do 20 myliRStep; liShow. do 20 myliRStep; liShow. do 10 myliRStep; liShow.
       do 100 myliRStep; liShow. 
       do 100 myliRStep; liShow. 
       do 10 myliRStep; liShow. 
       do 10 myliRStep; liShow.
      myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
      myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] 
  (Goto "_bb2") FN R ϝ *)
      myliRStep; liShow.
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []]
  (if{BoolOp}: use{BoolOp} local___10 then
     Goto "_bb3"
   else
     Goto "_bb9") FN R ϝ *)
 myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
      myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow.
           (* "_bb9"   *)2:{
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
       do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  
       do 20 myliRStep; liShow.  do 20 myliRStep; liShow.  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  
       myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
       myliRStep; liShow.   (* myliRStep; liShow.  *) 
      unfold li.bind1. unfold li.tactic; unfold li_tactic. 
        unfold interpret_rust_type_goal.
        iExists (option (place_rfn (place_rfn (loc * Z) * gname))).
        iExists (Option_ty (mut_ref Cap_inv_t ulft_1)). repeat myliRStep.
split. {   unfold_all_protected_evars.
           instantiate(3:= l'0).
           instantiate(1:= x' ).
           destruct (self !! l'0) eqn:Hkk1.
           2:{ eauto. }
           destruct p eqn:p1. 2:{ eauto. } 
           destruct (Z.land r.2 action) eqn:Hkk2;tryfalse.
                    { rewrite <- eq_None_not_Some in H126.
                      destruct (decide (is_Some (Some # r)));tryfalse.
                            {rewrite <- eq_None_not_Some in n. inversion n. }
                    }
                    { rewrite <- eq_None_not_Some in H126.
                      destruct (decide (is_Some (Some # r)));tryfalse.
                            {rewrite <- eq_None_not_Some in n. inversion n. }
                    }
      }
 
   (* 2: *){  repeat myliRStep. destruct (self !! l'0) eqn:Hkk1;tryfalse.
               { destruct p eqn:p1. 
                   {destruct (Z.land r.2 action) eqn:Hkk2;tryfalse. 
                       {  rewrite <- eq_None_not_Some in H126. 
                        destruct (decide (is_Some (Some # r)));tryfalse.
                        rewrite <- eq_None_not_Some in n. inversion n. }
                       {rewrite <- eq_None_not_Some in H126. 
                        destruct (decide (is_Some (Some # r)));tryfalse.
                        rewrite <- eq_None_not_Some in n. inversion n. }
                       {rewrite <- eq_None_not_Some in H126. 
                        destruct (decide (is_Some (Some # r)));tryfalse.
                        rewrite <- eq_None_not_Some in n. inversion n. }
              }
                        repeat myliRStep. }
                        repeat myliRStep. }
          } 


(*duoyugongzuo unfold_all_protected_evars.
           split. 2:{  myliRStep; liShow. repeat myliRStep; liShow. 
                       split. {  unfold_all_protected_evars.
                                 unfold test1 in Htest.
                                 apply Htest. }
                   myliRStep; liShow. repeat myliRStep; liShow. 
                    }
         {  Search(¬ is_Some _).
             rewrite <- eq_None_not_Some in H126.
             destruct (decide (is_Some (self !! l'0))) eqn:Hkk1.  
                 { inversion H126. }
                 { simpl. eauto.   
                   destruct(self !! Hevar ) eqn:hkk2.
                   { destruct p. { destruct (Z.land r.2 action). {
         }
} *)

(* [{ trace (TraceIfBool
            (bool_decide
               (is_Some
                  (if decide (is_Some (self !! l'0))
                   then Some # (self !!! l'0, x')
                   else None))), true);
   {typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1]
      [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] (Goto "_bb3") FN R ϝ}
}] *)



 
(*         liEnsureInvariant; try liRIntroduceLetInGoal;
      simp_ltypes; simplify_layout_goal.
      eapply tac_do_intro_pure_and. *)
       myliRStep; liShow. 
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []]
  (Goto "_bb3") FN R ϝ *)
       do 100 myliRStep; liShow. do 10 myliRStep; liShow.
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. (*  myliRStep; liShow.  *) (* myliRStep; liShow.  *)
 
       destruct (decide (is_Some (self !! l'0))) eqn:hkk1;tryfalse.
      unfold_all_protected_evars. 
       instantiate(3:=(mut_ref Cap_inv_t κ)).   
       rewrite hkk1.
       instantiate(2:= self !!! l'0). 
       instantiate(1:= x'). 
        myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. (* myliRStep; liShow. *)  (* myliRStep; liShow. *)
          unfold_all_protected_evars. 
        instantiate(3:= self !!! l'0). 
       instantiate(2:= x'). (* myliRStep; liShow. *)
       eapply tac_do_intro_pure_and.
       split. { unfold lookup_total. eauto. } 
        myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow. 
       do 10 myliRStep; liShow. do 10 myliRStep; liShow. do 10 myliRStep; liShow.
       do 20 myliRStep; liShow. do 20 myliRStep; liShow. 
       myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
       myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
       myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. (*  myliRStep; liShow.  *)
         destruct (self !!! l'0 )eqn:Hx1. 2:{ myliRStep; liShow. }

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  do 100 myliRStep; liShow. do 100 myliRStep; liShow. do 100  myliRStep; liShow.
  do 100  myliRStep; liShow. do 100 myliRStep; liShow.  do 100 myliRStep; liShow.
  do 20 myliRStep; liShow. 
       do 20 myliRStep; liShow. do 20 myliRStep; liShow.  do 20 myliRStep; liShow.
  do 20 myliRStep; liShow. do 20myliRStep; liShow. 
  myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow.
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] (Goto "_bb5") FN R ϝ *)
  myliRStep; liShow.
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []]
  (if{BoolOp}: use{BoolOp} local___15 then
     Goto "_bb6"
   else
     Goto "_bb7") FN R ϝ *)
 myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
(* [{ b', _ ← destruct x'0;
   trace (TraceIfBool x'0, b');
   {if b'
    then
     typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] 
       (Goto "_bb6") FN R ϝ
    else
     typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] 
       (Goto "_bb7") FN R ϝ}
}] *)
 
  myliRStep; liShow. 








{
(* [{ trace (TraceIfBool true, true);
   {typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] 
      (Goto "_bb6") FN R ϝ}
}] *)
 myliRStep; liShow.
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] (Goto "_bb6") FN R ϝ *)
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
   do 20 myliRStep; liShow. do 20 myliRStep; liShow. do 20 myliRStep; liShow.
   do 20 myliRStep; liShow. do 20 myliRStep; liShow. do 20 myliRStep; liShow.  
   do 20 myliRStep; liShow.  
(*  myliRStep; liShow.  *)
  unfold li.bind1. unfold li.tactic; unfold li_tactic. 
        unfold interpret_rust_type_goal.
        iExists (option (place_rfn (place_rfn (loc * Z) * gname))).
        iExists (Option_ty (mut_ref Cap_inv_t κ3)).   
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1]
  [κ3 ⊑ₗ{ 0} [κ0; ulft_1; ulft_2]; κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] (Goto "_bb10") FN R ϝ *)
myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow.  (* myliRStep; liShow. *)  (*  myliRStep; liShow.  *)

     liEnsureInvariant; try liRIntroduceLetInGoal;
      simp_ltypes; simplify_layout_goal.   (* myliRStep; liShow.  *) 
      eapply tac_do_intro_pure_and.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow.  (* myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.  myliRStep; liShow.  *)
  (*    myliRStep; liShow. *)
      split. 
   { unfold_all_protected_evars. simpl. unfold lookup. specialize (ident self ).  specialize (ident l'0 ).
     unfold lookup_total in p.
unfold lookup_total in ident.
specialize (ident map_lookup_total ). 
destruct ident.
 tryfalse.  eauto.  (* instantiate(1:= (👻 γ)).   inversion p. eauto. tryfalse. rewrite H128. *)  admit.  } 
      
myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
      do 100 myliRStep; liShow.
     do 100 myliRStep; liShow.
     do 100 myliRStep; liShow.
     do 100 myliRStep; liShow. 
     do 100 myliRStep; liShow.
   do 100 myliRStep; liShow.  
   do 100 myliRStep; liShow. 
   do 100 myliRStep; liShow. 
   do 50 myliRStep; liShow. 
   do 10 myliRStep; liShow.
myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
(* R v13 [κ3 ⊑ₗ{ 0} [κ0]; κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 0} []] *)
myliRStep; liShow.  do 10 myliRStep; liShow. repeat myliRStep; liShow.

split. {  unfold_all_protected_evars.
        instantiate(5:=(l'0)).
         destruct (self !! l'0) eqn:hkk0;tryfalse.
         { destruct p0 eqn:p00.
            { destruct (Z.land r0.2 action) eqn:Hkk1. { inversion H126. {destruct H129. tryfalse. unfold lookup in hkk0. eapply lookup_total_correct in hkk0. rewrite hkk0 in Hx1. injection Hx1. intros. rewrite H131 in Hkk1. tryfalse. } 
                                                      { inversion H129. tryfalse. }
           }
         {  instantiate(1:=x').
         instantiate(2:=x').  
         instantiate(1:=#r).
unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
         eauto.  
             rewrite hkk0 in Hx1. injection Hx1 as Heq.
rewrite Heq. eauto. }
         {
unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
         eauto.  
             rewrite hkk0 in Hx1. injection Hx1 as Heq.
rewrite Heq. eauto. }

}
                                          
     unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
unfold lookup_total in hkk0.
unfold lookup_total in Hx1.
 tryfalse. 
}

}



(* 

 inversion i. inversion H129. inversion H131. rewrite <- hkk0 in hkk1. contradiction.  congruence. inversion p00. inversion H129.                                              

             (*   Hx1 and hkk0  *)
       admit. 
     }
 *)
       do 20 myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow.
 destruct (self !! l'0) eqn:hkk0;tryfalse.
 destruct p0 eqn:p00. 
 { destruct (Z.land r0.2 action) eqn:Hkk1. 
       { 

 myliRStep; liShow. inversion H126. {destruct H129. tryfalse. unfold lookup in hkk0. eapply lookup_total_correct in hkk0. rewrite hkk0 in Hx1. injection Hx1. intros. rewrite H131 in Hkk1. tryfalse. } 
                                                      { inversion H129. tryfalse. }

}
    {  
          myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  myliRStep; liShow. repeat myliRStep; liShow.  }

    
 repeat myliRStep; liShow. }


     unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
unfold lookup_total in hkk0.
unfold lookup_total in Hx1.
 tryfalse. 

} (*bb6 bb8 bb10 *)












(* [{ trace (TraceIfBool false, false);
   {typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []] (Goto "_bb7") FN R ϝ}
}]
 *)


 myliRStep; liShow.
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2; ϝ ⊑ₑ ulft_1] [κ ⊑ₗ{ 0} [ulft_1]; ϝ ⊑ₗ{ 2} []]
  (Goto "_bb7") FN R ϝ *)
 myliRStep; liShow. myliRStep; liShow.
 myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  do 20 myliRStep; liShow.   do 20 myliRStep; liShow.  
   do 20 myliRStep; liShow.   do 20 myliRStep; liShow.    do 20 myliRStep; liShow. 
     do 20 myliRStep; liShow.    do 20 myliRStep; liShow.    do 20 myliRStep; liShow. 
  do 100 myliRStep; liShow.   do 100 myliRStep; liShow.  do 20 myliRStep; liShow.
myliRStep; liShow. myliRStep; liShow.  repeat myliRStep; liShow. (* myliRStep; liShow.    *) 
unfold li.bind1. unfold li.tactic; unfold li_tactic. 
        unfold interpret_rust_type_goal.
        iExists (option (place_rfn (place_rfn (loc * Z) * gname))). 
   iExists (Option_ty (mut_ref Cap_inv_t ulft_1)). repeat myliRStep.
  split. {
      unfold_all_protected_evars.
      instantiate(3:=l'0).
      destruct (self !! l'0) eqn:hkk0. 2:{eauto. } 
      destruct p0 eqn:p00.  2:{eauto. } 
      destruct (Z.land r0.2 action) eqn: Hx2;tryfalse.
       { inversion H126. { inversion H129. tryfalse. }
                         { inversion H129. unfold lookup in hkk0. eapply lookup_total_correct in hkk0. rewrite hkk0 in Hx1. injection Hx1 as Heq.  rewrite <- Heq in H131. tryfalse. }
       }
       { inversion H126. { inversion H129. tryfalse. }
                         { inversion H129. unfold lookup in hkk0. eapply lookup_total_correct in hkk0. rewrite hkk0 in Hx1. injection Hx1 as Heq.  rewrite <- Heq in H131. tryfalse. }

       }
       }
     myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  repeat myliRStep; liShow. 
      split.
       {  destruct (self !! l'0) eqn:hkk0;tryfalse.  
          destruct p0 eqn:p00. 
          { unfold_all_protected_evars.
              instantiate(1:=x'). eauto. }
          {      unfold lookup in hkk0. 
eapply lookup_total_correct in hkk0.
unfold lookup_total in hkk0.
unfold lookup_total in Hx1.
 tryfalse. }

}

myliRStep; liShow. 
 myliRStep; liShow. myliRStep; liShow. 
myliRStep; liShow.  
destruct (self !! l'0) eqn:hkk0;tryfalse.  
destruct p0 eqn:p00. 2:{  repeat myliRStep; liShow.  }
   destruct (Z.land r0.2 action) eqn: Hx2;tryfalse.

     {  inversion H126. { inversion H129. tryfalse. } 

          myliRStep; liShow. repeat myliRStep; liShow. }  
 {repeat myliRStep; liShow. } 
{ repeat myliRStep; liShow. } 

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer. 
 { rewrite <- eq_None_not_Some in H126.
   
   destruct (decide (is_Some (self !! l'0))) in H126. { inversion H126. }
   
    rewrite <- eq_None_not_Some in n. 
    destruct (self !! l'0 ) eqn:Hx2;tryfalse.
    rewrite Hx2.
 eauto. }

{    simpl in hkk1.
unfold lookup_total in Hx1.
destruct (self !! l'0) eqn:hkk0;tryfalse.
unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
unfold lookup_total in hkk0. eauto.  rewrite hkk0 in Hx1. inversion Hx1. tryfalse.
inversion p.
 tryfalse. admit.

}
{
admit. }
{
inversion p. admit. }
{
admit. }


{unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
rewrite hkk0 in Hx1. injection Hx1 as Heq.  rewrite <- Heq. eauto.
}
{unfold lookup in hkk0.
eapply lookup_total_correct in hkk0.
rewrite hkk0 in Hx1. injection Hx1 as Heq.  rewrite <- Heq. eauto.
}

 Unshelve. all: print_remaining_sidecond.


Qed.
End proof.
 

(* Definition Obj_try_take_action_mut_def (BTreeMap_KVA_get_mut_constObj_Cap_std_alloc_Global_constObj_loc : loc) (Cap_contains_loc : loc) (Option_T_is_some_mutCap_loc : loc) (Option_T_unwrap_mutCap_loc : loc) : function := {|
 f_args := [
  ("self", void* : layout);
  ("obj", void* : layout);
  ("action", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("cap_on_obj", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__5", void* : layout);
  ("__6", void* : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", (layout_of unit_sl) : layout);
  ("__10", bool_layout : layout);
  ("__11", void* : layout);
  ("__12", (layout_of unit_sl) : layout);
  ("tem_cap", void* : layout);
  ("__14", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__15", bool_layout : layout);
  ("__16", void* : layout);
  ("__17", (it_layout USize) : layout);
  ("__18", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft18" "ulft_2"; (* initialization *)
   annot: CopyLftNameAnnot "plft17" "ulft_1"; (* initialization *)
   annot: StartLftAnnot "llft4" ["plft17"]; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["BTreeMap_inv_t"] [RSTLitType ["alias_ptr_t"] []; RSTLitType ["Cap_inv_t"] []; RSTLitType ["Global_ty"] []]), "llft4" } ((!{ PtrOp } ( "self" )) at{ Obj_sls } "caps"));
   "__8" <-{ PtrOp } &raw{ Shr } (!{ PtrOp } ( "obj" ));
   annot: StartLftAnnot "llft5" ["llft4" ;"ulft_1"]; (* borrow *)
   "__7" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft22" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft5" } ("__8"));
   annot: CopyLftNameAnnot "vlft6" "plft22"; (* composite *)
   annot: CopyLftNameAnnot "vlft6" "plft22"; (* borrow *)
   "__6" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft21" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft6" } (!{ PtrOp } ( "__7" )));
   annot: CopyLftNameAnnot "vlft30" "plft21"; (* function_call *)
   annot: CopyLftNameAnnot "vlft29" "plft20"; (* function_call *)
   "cap_on_obj" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE BTreeMap_KVA_get_mut_constObj_Cap_std_alloc_Global_constObj_loc ["vlft30"; "vlft29"] [@{expr} use{ PtrOp } ("__5"); use{ PtrOp } ("__6")];
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft5"; (* endlft *)
   annot: StartLftAnnot "llft7" [ "llft4";"plft17";"ulft_1"]; (* borrow *)
   "__11" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft23" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } ("cap_on_obj"));
(*    annot: AliasLftAnnot "vlft31" ["plft24"; "plft23"]; (* function_call *) *)
(*    annot: CopyLftNameAnnot "vlft8" "plft24"; (* function_call *) *)
   "__10" <-{ BoolOp } CallE Option_T_is_some_mutCap_loc ["llft7"] [@{expr} use{ PtrOp } ("__11")];
   annot: EndLftAnnot "llft7"; (* endlft *)
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   if{ BoolOp }: use{ BoolOp } ("__10") then
    Goto "_bb3"
   else
    Goto "_bb9"
  ]>%E $
  <[
  "_bb3" :=
   "__14" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("cap_on_obj");
(*    annot: CopyLftNameAnnot "vlft9" "plft26"; (* function_call *) *)
   "tem_cap" <-{ PtrOp } AnnotExpr (* function_call *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft25" (LftNameTreeLeaf))) (CallE Option_T_unwrap_mutCap_loc [] [@{expr} use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__14")]);
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   annot: StartLftAnnot "llft10" ["plft25";"ulft_1";"ulft_2"]; (* borrow *)
   "__16" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft27" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft10" } (!{ PtrOp } ( "tem_cap" )));
   "__17" <-{ IntOp USize } use{ IntOp USize } ("action");
   annot: CopyLftNameAnnot "vlft32" "plft27"; (* function_call *)
   "__15" <-{ BoolOp } CallE Cap_contains_loc ["vlft32"] [@{expr} use{ PtrOp } ("__16"); use{ IntOp USize } ("__17")];
   annot: EndLftAnnot "llft10"; (* endlft *)
   Goto "_bb5"
  ]>%E $
  <[
  "_bb5" :=
   if{ BoolOp }: use{ BoolOp } ("__15") then
    Goto "_bb6"
   else
    Goto "_bb7"
  ]>%E $
  <[
  "_bb6" :=
   annot: StartLftAnnot "llft11" ["plft25";"ulft_1";"ulft_2"]; (* borrow *)
   "__18" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft28" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Cap_inv_t"] []), "llft11" } (!{ PtrOp } ( "tem_cap" )));
(*    annot: CopyLftNameAnnot "vlft12" "plft28"; (* composite *) *)
    annot: ExtendLftAnnot "llft4";
    annot: ExtendLftAnnot "llft11";
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "Some" (RSTLitType ["Option_ty"] [RSTRef Mut "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_Some_sls ((PtrSynType))) [("0", use{ PtrOp } ("__18") : expr)]);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb7" :=
   annot: EndLftAnnot "llft4"; (* endlft *)
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "None" (RSTLitType ["Option_ty"] [RSTRef Mut "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_None_sls ((PtrSynType))) []);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb8" :=
   Goto "_bb10"
  ]>%E $
  <[
  "_bb9" :=
   annot: EndLftAnnot "llft4"; (* endlft *)
   "__9" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "None" (RSTLitType ["Option_ty"] [RSTRef Mut "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_None_sls ((PtrSynType))) []);
   Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   return (use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

 *)



















