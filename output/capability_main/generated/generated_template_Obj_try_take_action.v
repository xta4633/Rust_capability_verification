From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability_main Require Import generated_code_capability generated_specs_capability.
From stdlib.option.option.generated Require Export generated_specs_option.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.
From stdlib.btreemap.btreemap.generated Require Export generated_specs_btreemap.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Definition Obj_try_take_action_lemma (π : thread_id) : Prop :=
  ∀ (BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc : loc) (Cap_contains_loc : loc) (Option_T_is_some_Cap_loc : loc) (Option_T_unwrap_Cap_loc : loc) , 
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable (((BTreeMap_sls ((PtrSynType)) ((Cap_st)) (((Global_sls : syn_type)))) : syn_type)) →
  syn_type_is_layoutable (((Option_els ((PtrSynType))) : syn_type)) →
  syn_type_is_layoutable ((Cap_sls : syn_type)) →
  syn_type_is_layoutable ((Obj_sls : syn_type)) →
  BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc ◁ᵥ{π} BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc @ function_ptr [PtrSynType; PtrSynType] (type_of_BTreeMap_KVA_get (loc) (PtrSynType) (Cap_inv_t_rt) (Cap_st) (Global_rt) ((Global_sls : syn_type)) (* (loc) (PtrSynType) *)) -∗
  Cap_contains_loc ◁ᵥ{π} Cap_contains_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_Cap_contains ) -∗
  Option_T_is_some_Cap_loc ◁ᵥ{π} Option_T_is_some_Cap_loc @ function_ptr [PtrSynType] (type_of_Option_T_is_some ((place_rfn Cap_inv_t_rt)) (PtrSynType)) -∗
  Option_T_unwrap_Cap_loc ◁ᵥ{π} Option_T_unwrap_Cap_loc @ function_ptr [((Option_els ((PtrSynType))) : syn_type)] (type_of_Option_T_unwrap ((place_rfn Cap_inv_t_rt)) (PtrSynType)) -∗
  typed_function π (Obj_try_take_action_def BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc  Cap_contains_loc  Option_T_is_some_Cap_loc  Option_T_unwrap_Cap_loc  ) [((Option_els ((PtrSynType))) : syn_type); ((Option_els ((PtrSynType))) : syn_type); PtrSynType; PtrSynType; PtrSynType; PtrSynType; UnitSynType; BoolSynType; PtrSynType; UnitSynType; PtrSynType; ((Option_els ((PtrSynType))) : syn_type); BoolSynType; PtrSynType; IntSynType USize; PtrSynType] (type_of_Obj_try_take_action ).
End proof.

Ltac Obj_try_take_action_prelude :=
  unfold Obj_try_take_action_lemma;
  set (FN_NAME := FUNCTION_NAME "Obj_try_take_action");
  intros;
  iStartProof;
  let ulft_2 := fresh "ulft_2" in
  let ulft_1 := fresh "ulft_1" in
  start_function "Obj_try_take_action" ( [ [ [] ulft_2] ulft_1] ) ( [ [ [  self obj ] action ] γ ] );
  set (loop_map := BB_INV_MAP (PolyNil));
  intros arg_self arg_obj arg_action local___0 local_cap_on_obj local___5 local___6 local___7 local___8 local___9 local___10 local___11 local___12 local_tem_cap local___14 local___15 local___16 local___17 local___18;
  prepare_parameters ( self obj action γ );
  init_lfts (named_lft_update "ulft_2" ulft_2 $ named_lft_update "ulft_1" ulft_1 $ ∅ );
  init_tyvars ( ∅ ).
