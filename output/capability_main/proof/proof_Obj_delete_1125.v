From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability_main Require Import generated_code_capability generated_specs_capability generated_template_Obj_delete.
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
     end;idtac "Executing change_no_check" ]); try unfold_introduce_direct; liSimpl; 
         idtac "**************************************************".

Ltac tryfalse :=
            try solve [congruence | discriminate | assumption]. 

Lemma Obj_delete_proof (π : thread_id) :
  Obj_delete_lemma π.
Proof.
  Obj_delete_prelude.
  
  do 100 myliRStep;liShow.  
  do 100 myliRStep;liShow.
  do 100 myliRStep;liShow.  
  do 100 myliRStep;liShow.
  do 40 myliRStep;liShow.
  do 10 myliRStep; liShow. 
  myliRStep; liShow. 
(* typed_stmt π [ϝ ⊑ₑ ulft_1; ϝ ⊑ₑ ulft_2] [ϝ ⊑ₗ{ 0} []] (Goto "_bb0") FN R ϝ *)
  myliRStep; liShow. 
  do 100 myliRStep;liShow.  
  do 100 myliRStep;liShow.
  do 100 myliRStep;liShow.  
  do 100 myliRStep;liShow.
  do 40 myliRStep;liShow.
  do 10 myliRStep; liShow. 

  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. 
  myliRStep; liShow. myliRStep; liShow. myliRStep; liShow. myliRStep; liShow.
  destruct (self !! x') eqn: Hx.
  {
    destruct p.
    2:{
      repeat myliRStep; liShow.
      unfold_all_protected_evars.    
      instantiate(3:= (mut_ref Cap_inv_t κ)).
      instantiate(1:= None).
      repeat myliRStep; liShow.
      unfold_all_protected_evars.   
      instantiate(1:= x').
      split.  { rewrite Hx. eauto. }
      rewrite Hx. 
      repeat myliRStep; liShow.
      Unshelve. all: sidecond_solver.
      Unshelve. all: sidecond_hammer.
    }

    {
      destruct (Z.land r.2 16) eqn:Hxx.
      2:{
        repeat myliRStep; liShow.
        2:{
          unfold_all_protected_evars.
          instantiate(1:= x').
          split.  { rewrite Hx. rewrite Hxx. eauto. }
          repeat myliRStep; liShow.
          rewrite Hx. rewrite Hxx.
          repeat myliRStep; liShow.
          Unshelve. all: sidecond_solver.
          Unshelve. all: sidecond_hammer.
        }
        {
          iExists [ϝ ⊑ₗ{ 1} [ulft_1]]. iExists [].
          iSplit. 
          { 
          iPureIntro. unfold llctx_find_llft.
          exists []. exists [ϝ ⊑ₗ{ 1} [ulft_1]]. exists (Some 0).
          split;simpl;eauto.
          }
          repeat myliRStep; liShow.
          unfold_all_protected_evars.   
          instantiate(1:= x').
          split.  { rewrite Hx. rewrite Hxx. eauto. }
          repeat myliRStep; liShow.
          rewrite Hx. rewrite Hxx.
          repeat myliRStep; liShow.
          Unshelve. all: sidecond_solver.
          Unshelve. all: sidecond_hammer.
        }

      }
      2:{
        assert ((Z.neg p < 0)%Z). { lia. }
        rewrite <- Hxx in H114.
        Search (Z.land _ _ ).
        rewrite Z.land_neg in H114.
        destruct H114. tryfalse.
      }

      repeat myliRStep; liShow.
      unfold_all_protected_evars.    
      instantiate(3:= (mut_ref Cap_inv_t κ)).
      instantiate(1:= None).
      
      assert (forall γ v, Obs γ v -∗ ( ⌜(PlaceGhost γ : place_rfn Cap_inv_t_rt) = (PlaceIn v : place_rfn Cap_inv_t_rt )⌝ ∗ ⌜True⌝%I )).
      {
        eauto.
      }
      iRename select (Obs x'0 _) into "Hx'".
      iRename select (Obs γ _) into "Hγ'".
      iPoseProof (H115 with "Hx'") as "#Hkkk".
      (* iDestruct "Hkkk" as %[H444 _].
      rewrite  H444. *)
      
      do 500 myliRStep; liShow.
      do 200 myliRStep; liShow.
      do 50 myliRStep; liShow.
      do 50 myliRStep; liShow.
      do 20 myliRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow. liRStep; liShow.
    


      unfold_all_protected_evars.   
      instantiate(1:= x').
      split.
      { rewrite Hx. rewrite Hxx. 
        Search (lookup _ _ ). 
        unfold BTreeMap_inv_t_rt in self.
        eapply insert_id with (m:= self ).
        eapply Hx.
      }
      eauto. }
      {
        repeat myliRStep; liShow.
      }
      
    }
  }

  

  do 10 myliRStep;liShow.
  myliRStep; liShow. 
  destruct(self !! x' ) eqn:hx1. 2:{   repeat myliRStep; liShow. unfold_all_protected_evars.    
   instantiate(3:= (mut_ref Cap_inv_t κ)).
   instantiate(1:= None).
  repeat myliRStep;liShow. 
  split. {  unfold_all_protected_evars. 
            instantiate(2:= x').
            destruct(self !! x');tryfalse. }
  repeat myliRStep;liShow.
       destruct(self !! x');tryfalse.
       repeat myliRStep;liShow.
 }

       repeat myliRStep;liShow.
       destruct p;tryfalse. { 
   destruct (Z.land r.2 16) eqn:Hc1;tryfalse.
{   repeat myliRStep;liShow. 
  unfold_all_protected_evars.  
   instantiate(3:= (mut_ref Cap_inv_t κ)).
   instantiate(1:= None). repeat myliRStep;liShow.  
   split.  { unfold_all_protected_evars. 
             instantiate(3:= x'0).
             instantiate(1:= x').
             destruct(self !! x') eqn:Hx1;tryfalse. 
             destruct p eqn:p0;tryfalse. 
                destruct (Z.land r0.2 16)eqn:Heq;tryfalse.  admit. 
          }
          repeat myliRStep;liShow.
          destruct(self !! x');tryfalse.
          destruct p;tryfalse. 
          destruct (Z.land r0.2 16) eqn:Hc2;tryfalse.
          repeat myliRStep;liShow.
 }





{   do 100 myliRStep;liShow.
    do 100 myliRStep;liShow.
    do 100 myliRStep;liShow.
    do 10 myliRStep; liShow. 
    do 10 myliRStep; liShow. 
    myliRStep; liShow. 
    myliRStep; liShow. 
    repeat myliRStep; liShow. 
    { iExists [ϝ ⊑ₗ{ 1} []]. iExists [].
      iSplit. 
      { 
      iPureIntro. unfold llctx_find_llft.
      exists []. exists [ϝ ⊑ₗ{ 1} []]. exists (Some 0).
      split;simpl;eauto.
      } 
     }
   split. 
     {  unfold_all_protected_evars. 
        instantiate(3:= x'0).
        instantiate(1:= x').
        destruct(self !! x') eqn:Hx1;tryfalse. 
            destruct p0 eqn:p00;tryfalse. 
              destruct (Z.land r0.2 16)eqn:Heq;tryfalse.
     }

     {     unfold_all_protected_evars. 
           destruct(self !! x') eqn:Hx1;tryfalse. 
           destruct p0 eqn:p00;tryfalse. 
              destruct (Z.land r0.2 16)eqn:Heq;tryfalse. 
              destruct (Z.land r0.2 right1 ) eqn:hd1;tryfalse.
               {repeat myliRStep; liShow. } {repeat myliRStep; liShow. } {repeat myliRStep; liShow. }
      } 
}






 repeat myliRStep; liShow.
{  repeat myliRStep; liShow.
 iExists [ϝ ⊑ₗ{ 1} []]. iExists [].
  iSplit. 
  { 
    iPureIntro. unfold llctx_find_llft.
    exists []. exists [ϝ ⊑ₗ{ 1} []]. exists (Some 0).
    split;simpl;eauto.
  } }
split.
{ 
unfold_all_protected_evars. 
   instantiate(3:= x'0).
   instantiate(1:= x').
   destruct(self !! x') eqn:Hx1;tryfalse. 
       destruct p0;tryfalse. 
              destruct (Z.land r0.2 16)eqn:Heq;tryfalse. }


  repeat myliRStep;liShow.
   destruct(self !! x') eqn:Hx1;tryfalse. 
         destruct p0 eqn:p00;tryfalse. 
              destruct (Z.land r0.2 16)eqn:Heq;tryfalse. 
              destruct (Z.land r0.2 right1 ) eqn:hd1;tryfalse.
{repeat myliRStep; liShow. } {repeat myliRStep; liShow. } {repeat myliRStep; liShow. }
}



  repeat myliRStep; liShow.
unfold_all_protected_evars. 
   instantiate(3:= (mut_ref Cap_inv_t κ)).
   instantiate(1:= None). repeat myliRStep;liShow.
split. { unfold_all_protected_evars. 
        instantiate(3:= x'0).
        instantiate(1:= x').
        destruct(self !! x') eqn:Hx1;tryfalse. 
       destruct p;tryfalse. } 
 myliRStep; liShow. 
  repeat myliRStep; liShow.
destruct(self !! x') eqn:Hx1;tryfalse. 
         destruct p eqn:p00;tryfalse. 
         repeat myliRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer. 
 Unshelve. all: print_remaining_sidecond.

(*Definition Obj_delete_def (Cap_contains_loc : loc) (Obj_try_take_action_mut_loc : loc) (Option_T_is_some_mutCap_loc : loc) (Option_T_unwrap_mutCap_loc : loc) : function := {|
 f_args := [
  ("self", void* : layout);
  ("to_delete", void* : layout);
  ("right", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("cap_on_to_delete", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__5", void* : layout);
  ("__6", void* : layout);
  ("__7", bool_layout : layout);
  ("__8", void* : layout);
  ("cap_unwrap", void* : layout);
  ("__10", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__11", bool_layout : layout);
  ("__12", void* : layout);
  ("__13", (it_layout USize) : layout);
  ("__14", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft11" "ulft_2"; (* initialization *)
   annot: CopyLftNameAnnot "plft10" "ulft_1"; (* initialization *)
   annot: StartLftAnnot "llft4" ["plft10"]; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Obj_inv_t"] []), "llft4" } (!{ PtrOp } ( "self" )));
   annot: StartLftAnnot "llft5" ["plft11";"llft4" ]; (* borrow *)
   "__6" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft14" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Obj_inv_t"] []), "llft5" } (!{ PtrOp } ( "to_delete" )));
   annot: CopyLftNameAnnot "vlft21" "plft14"; (* function_call *)
   annot: CopyLftNameAnnot "vlft20" "plft13"; (* function_call *)
   "cap_on_to_delete" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE Obj_try_take_action_mut_loc ["vlft20"; "vlft21"] [@{expr} use{ PtrOp } ("__5"); use{ PtrOp } ("__6"); I2v (16) U64];
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft5"; (* endlft *)
   annot: StartLftAnnot "llft6" ["ulft_1";"ulft_2";"llft4"]; (* borrow *) (*xiugai*)
   "__8" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft6" } ("cap_on_to_delete"));
(*    annot: AliasLftAnnot "vlft22" ["plft15"; "plft16"]; (* function_call *)
   annot: CopyLftNameAnnot "vlft7" "plft16"; (* function_call *) *)
   "__7" <-{ BoolOp } CallE Option_T_is_some_mutCap_loc ["llft6"] [@{expr} use{ PtrOp } ("__8")];
   annot: EndLftAnnot "llft6"; (* endlft *)
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   if{ BoolOp }: use{ BoolOp } ("__7") then
    Goto "_bb3"
   else
    Goto "_bb9"
  ]>%E $
  <[
  "_bb3" :=
   "__10" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("cap_on_to_delete");
(*    annot: CopyLftNameAnnot "vlft8" "plft18"; (* function_call *) *)
   "cap_unwrap" <-{ PtrOp } AnnotExpr (* function_call *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft17" (LftNameTreeLeaf))) (CallE Option_T_unwrap_mutCap_loc [] [@{expr} use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__10")]);
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   annot: StartLftAnnot "llft9" ["plft17"]; (* borrow *)
   "__12" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft19" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft9" } (!{ PtrOp } ( "cap_unwrap" )));
   "__13" <-{ IntOp USize } use{ IntOp USize } ("right");
   annot: CopyLftNameAnnot "vlft23" "plft19"; (* function_call *)
   "__11" <-{ BoolOp } CallE Cap_contains_loc ["vlft23"] [@{expr} use{ PtrOp } ("__12"); use{ IntOp USize } ("__13")];
   annot: EndLftAnnot "llft9"; (* endlft *)
   Goto "_bb5"
  ]>%E $
  <[
  "_bb5" :=
   if{ BoolOp }: use{ BoolOp } ("__11") then
    Goto "_bb6"
   else
    Goto "_bb7"
  ]>%E $
  <[
  "_bb6" :=
   "__14" <-{ IntOp USize } use{ IntOp USize } ("right");
   (!{ PtrOp } ( "cap_unwrap" )) at{ Cap_sls } "rights" <-{ IntOp USize } (use{ IntOp USize } ((!{ PtrOp } ( "cap_unwrap" )) at{ Cap_sls } "rights")) ^{ IntOp USize , IntOp USize } (use{ IntOp USize } ("__14"));
   annot: EndLftAnnot "llft4"; (* endlft *)
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb8"
  ]>%E $
  <[
  "_bb7" :=
   annot: EndLftAnnot "llft4"; (* endlft *)
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb8"
  ]>%E $
  <[
  "_bb8" :=
   Goto "_bb10"
  ]>%E $
  <[
  "_bb9" :=
   annot: EndLftAnnot "llft4"; (* endlft *)
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}. *)




