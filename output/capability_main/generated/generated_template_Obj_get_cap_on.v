From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability_main Require Import generated_code_capability generated_specs_capability.
From stdlib.btreemap.btreemap.generated Require Export generated_specs_btreemap.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.
From stdlib.option.option.generated Require Export generated_specs_option.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Definition Obj_get_cap_on_lemma (π : thread_id) : Prop :=
  ∀ (BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc : loc) , 
  syn_type_is_layoutable (((Option_els ((PtrSynType))) : syn_type)) →
  syn_type_is_layoutable ((Cap_sls : syn_type)) →
  syn_type_is_layoutable ((Global_sls : syn_type)) →
  syn_type_is_layoutable (((BTreeMap_sls ((PtrSynType)) ((Cap_st)) (((Global_sls : syn_type)))) : syn_type)) →
  syn_type_is_layoutable ((Obj_sls : syn_type)) →
  BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc ◁ᵥ{π} BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc @ function_ptr [PtrSynType; PtrSynType] (type_of_BTreeMap_KVA_get (loc) (PtrSynType) (Cap_inv_t_rt) (Cap_st) (Global_rt) ((Global_sls : syn_type)) ) -∗
  typed_function π (Obj_get_cap_on_def BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc  ) [((Option_els ((PtrSynType))) : syn_type); PtrSynType; PtrSynType; PtrSynType; PtrSynType] (type_of_Obj_get_cap_on ).
End proof.

Ltac Obj_get_cap_on_prelude :=
  unfold Obj_get_cap_on_lemma;
  set (FN_NAME := FUNCTION_NAME "Obj_get_cap_on");
  intros;
  iStartProof;
  let ulft_2 := fresh "ulft_2" in
  let ulft_1 := fresh "ulft_1" in
  start_function "Obj_get_cap_on" ( [ [ [] ulft_2] ulft_1] ) ( [ [  self obj ] γ ] );
  set (loop_map := BB_INV_MAP (PolyNil));
  intros arg_self arg_obj local___0 local___3 local___4 local___5 local___6;
  prepare_parameters ( self obj γ );
  init_lfts (named_lft_update "ulft_2" ulft_2 $ named_lft_update "ulft_1" ulft_1 $ ∅ );
  init_tyvars ( ∅ ).
