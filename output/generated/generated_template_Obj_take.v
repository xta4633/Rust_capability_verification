From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability Require Import generated_code_capability generated_specs_capability.
From stdlib.option.option.generated Require Export generated_specs_option.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.
From stdlib.btreemap.btreemap.generated Require Export generated_specs_btreemap.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Definition Obj_take_lemma (π : thread_id) : Prop :=
  ∀ (Obj_try_merge_cap_loc : loc) (Obj_try_take_action_loc : loc) (Option_T_is_some_Cap_loc : loc) , 
  syn_type_is_layoutable ((Cap_sls : syn_type)) →
  syn_type_is_layoutable (((Option_els ((PtrSynType))) : syn_type)) →
  syn_type_is_layoutable ((Obj_sls : syn_type)) →
  Obj_try_merge_cap_loc ◁ᵥ{π} Obj_try_merge_cap_loc @ function_ptr [PtrSynType; PtrSynType] (type_of_Obj_try_merge_cap ) -∗
  Obj_try_take_action_loc ◁ᵥ{π} Obj_try_take_action_loc @ function_ptr [PtrSynType; PtrSynType; IntSynType USize] (type_of_Obj_try_take_action ) -∗
  Option_T_is_some_Cap_loc ◁ᵥ{π} Option_T_is_some_Cap_loc @ function_ptr [PtrSynType] (type_of_Option_T_is_some ((place_rfn Cap_inv_t_rt)) (PtrSynType)) -∗
  typed_function π (Obj_take_def Obj_try_merge_cap_loc  Obj_try_take_action_loc  Option_T_is_some_Cap_loc  ) [UnitSynType; BoolSynType; PtrSynType; ((Option_els ((PtrSynType))) : syn_type); PtrSynType; PtrSynType; PtrSynType; PtrSynType] (type_of_Obj_take ).
End proof.

Ltac Obj_take_prelude :=
  unfold Obj_take_lemma;
  set (FN_NAME := FUNCTION_NAME "Obj_take");
  intros;
  iStartProof;
  let ulft_1 := fresh "ulft_1" in
  let ulft_2 := fresh "ulft_2" in
  let ulft_3 := fresh "ulft_3" in
  start_function "Obj_take" ( [ [ [ [] ulft_1] ulft_2] ulft_3] ) ( [ [ [ [  self obj_to_take ] cap_to_take ] γ1 ] γ2 ] );
  set (loop_map := BB_INV_MAP (PolyNil));
  intros arg_self arg_obj_to_take arg_cap_to_take local___0 local___4 local___5 local___6 local___7 local___8 local___9 local___10;
  prepare_parameters ( self obj_to_take cap_to_take γ1 γ2 );
  init_lfts (named_lft_update "ulft_1" ulft_1 $ named_lft_update "ulft_2" ulft_2 $ named_lft_update "ulft_3" ulft_3 $ ∅ );
  init_tyvars ( ∅ ).
