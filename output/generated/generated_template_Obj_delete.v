From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability Require Import generated_code_capability generated_specs_capability.
From stdlib.btreemap.btreemap.generated Require Export generated_specs_btreemap.
From stdlib.option.option.generated Require Export generated_specs_option.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Definition Obj_delete_lemma (π : thread_id) : Prop :=
  ∀ (Cap_contains_loc : loc) (Obj_try_take_action_mut_loc : loc) (Option_T_is_some_mutCap_loc : loc) (Option_T_unwrap_mutCap_loc : loc) , 
  syn_type_is_layoutable (((Option_els ((PtrSynType))) : syn_type)) →
  syn_type_is_layoutable ((Obj_sls : syn_type)) →
  syn_type_is_layoutable ((Cap_sls : syn_type)) →
  Cap_contains_loc ◁ᵥ{π} Cap_contains_loc @ function_ptr [PtrSynType; IntSynType USize] (type_of_Cap_contains ) -∗
  Obj_try_take_action_mut_loc ◁ᵥ{π} Obj_try_take_action_mut_loc @ function_ptr [PtrSynType; PtrSynType; IntSynType USize] (type_of_Obj_try_take_action_mut ) -∗
  Option_T_is_some_mutCap_loc ◁ᵥ{π} Option_T_is_some_mutCap_loc @ function_ptr [PtrSynType] (type_of_Option_T_is_some (((place_rfn Cap_inv_t_rt) * gname)%type) (PtrSynType)) -∗
  Option_T_unwrap_mutCap_loc ◁ᵥ{π} Option_T_unwrap_mutCap_loc @ function_ptr [((Option_els ((PtrSynType))) : syn_type)] (type_of_Option_T_unwrap (((place_rfn Cap_inv_t_rt) * gname)%type) (PtrSynType)) -∗
  typed_function π (Obj_delete_def Cap_contains_loc  Obj_try_take_action_mut_loc  Option_T_is_some_mutCap_loc  Option_T_unwrap_mutCap_loc  ) [UnitSynType; ((Option_els ((PtrSynType))) : syn_type); PtrSynType; PtrSynType; BoolSynType; PtrSynType; PtrSynType; ((Option_els ((PtrSynType))) : syn_type); BoolSynType; PtrSynType; IntSynType USize; IntSynType USize] (type_of_Obj_delete ).
End proof.

Ltac Obj_delete_prelude :=
  unfold Obj_delete_lemma;
  set (FN_NAME := FUNCTION_NAME "Obj_delete");
  intros;
  iStartProof;
  let ulft_2 := fresh "ulft_2" in
  let ulft_1 := fresh "ulft_1" in
  start_function "Obj_delete" ( [ [ [] ulft_2] ulft_1] ) ( [ [ [ [  self γ1 ] to_delete ] γ2 ] right1 ] );
  set (loop_map := BB_INV_MAP (PolyNil));
  intros arg_self arg_to_delete arg_right local___0 local_cap_on_to_delete local___5 local___6 local___7 local___8 local_cap_unwrap local___10 local___11 local___12 local___13 local___14;
  prepare_parameters ( self γ1 to_delete γ2 right1 );
  init_lfts (named_lft_update "ulft_2" ulft_2 $ named_lft_update "ulft_1" ulft_1 $ ∅ );
  init_tyvars ( ∅ ).
