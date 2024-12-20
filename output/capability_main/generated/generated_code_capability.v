From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From stdlib.option.option.generated Require Export generated_specs_option.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.
From stdlib.btreemap.btreemap.generated Require Export generated_specs_btreemap.
Section Cdt_sls.
  Context `{!refinedrustGS Σ}.

  Definition Cdt_sls  : struct_layout_spec := mk_sls "Cdt" [] StructReprRust.
  Definition Cdt_st  : syn_type := Cdt_sls .
End Cdt_sls.

Section Cap_sls.
  Context `{!refinedrustGS Σ}.

  Definition Cap_sls  : struct_layout_spec := mk_sls "Cap" [
    ("obj", PtrSynType);
    ("rights", IntSynType USize);
    ("cdt", Cdt_st)] StructReprRust.
  Definition Cap_st  : syn_type := Cap_sls .
End Cap_sls.

Section Obj_sls.
  Context `{!refinedrustGS Σ}.

  Definition Obj_sls  : struct_layout_spec := mk_sls "Obj" [
    ("caps", ((BTreeMap_sls ((PtrSynType)) ((Cap_st)) (((Global_sls : syn_type)))) : syn_type))] StructReprRust.
  Definition Obj_st  : syn_type := Obj_sls .
End Obj_sls.

Section code.
Context `{!refinedrustGS Σ}.
Open Scope printing_sugar.

Definition Cap_contains_def  : function := {|
 f_args := [
  ("self", void* : layout);
  ("bit_position", (it_layout USize) : layout)
 ];
 f_local_vars := [
  ("__0", bool_layout : layout);
  ("__3", (it_layout USize) : layout);
  ("__4", (it_layout USize) : layout);
  ("__5", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft3" "ulft_1"; (* initialization *)
   "__4" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "self" )) at{ Cap_sls } "rights");
   "__5" <-{ IntOp USize } use{ IntOp USize } ("bit_position");
   "__3" <-{ IntOp USize } (use{ IntOp USize } ("__4")) &b{ IntOp USize , IntOp USize } (use{ IntOp USize } ("__5"));
   "__0" <-{ BoolOp } (use{ IntOp USize } ("__3")) != { IntOp USize , IntOp USize , U8 } (I2v (0) U64);
   return (use{ BoolOp } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Obj_new_def (BTreeMap_KV_new_constObj_Cap_loc : loc) : function := {|
 f_args := [
  
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (Obj_st)) : layout);
  ("__1", (use_layout_alg' (((BTreeMap_sls ((PtrSynType)) ((Cap_st)) (((Global_sls : syn_type)))) : syn_type))) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   "__1" <-{ (use_op_alg' (((BTreeMap_sls ((PtrSynType)) ((Cap_st)) (((Global_sls : syn_type)))) : syn_type))) } CallE BTreeMap_KV_new_constObj_Cap_loc [] [@{expr} ];
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   "__0" <-{ (use_op_alg' (Obj_st)) } StructInit Obj_sls [("caps", use{ (use_op_alg' (((BTreeMap_sls ((PtrSynType)) ((Cap_st)) (((Global_sls : syn_type)))) : syn_type))) } ("__1") : expr)];
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   return (use{ (use_op_alg' (Obj_st)) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.



Definition Obj_get_cap_on_def (BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc : loc) : function := {|
 f_args := [
  ("self", void* : layout);
  ("obj", void* : layout)
 ];
 f_local_vars := [
  ("__0", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__3", void* : layout);
  ("__4", void* : layout);
  ("__5", void* : layout);
  ("__6", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft10" "ulft_2"; (* initialization *)
   annot: CopyLftNameAnnot "plft9" "ulft_1"; (* initialization *)
   annot: CopyLftNameAnnot "vlft4" "plft9"; (* composite *)
   annot: CopyLftNameAnnot "vlft4" "plft9"; (* borrow *)
   "__3" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft11" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft4" } ((!{ PtrOp } ( "self" )) at{ Obj_sls } "caps"));
   "__6" <-{ PtrOp } &raw{ Shr } (!{ PtrOp } ( "obj" ));
   annot: StartLftAnnot "llft5" []; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft13" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft5" } ("__6"));
   annot: CopyLftNameAnnot "vlft6" "plft13"; (* composite *)
   annot: CopyLftNameAnnot "vlft6" "plft13"; (* borrow *)
   "__4" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft12" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft6" } (!{ PtrOp } ( "__5" )));
   annot: CopyLftNameAnnot "vlft15" "plft12"; (* function_call *)
   annot: CopyLftNameAnnot "vlft14" "plft11"; (* function_call *)
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc ["vlft15"; "vlft14"] [@{expr} use{ PtrOp } ("__3"); use{ PtrOp } ("__4")];
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft5"; (* endlft *)
   return (use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Obj_take_def (Obj_try_merge_cap_loc : loc) (Obj_try_take_action_loc : loc) (Option_T_is_some_Cap_loc : loc) : function := {|
 f_args := [
  ("self", void* : layout);
  ("obj_to_take", void* : layout);
  ("cap_to_take", void* : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("__4", bool_layout : layout);
  ("__5", void* : layout);
  ("__6", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", void* : layout);
  ("__10", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft13" "ulft_3"; (* initialization *)
   annot: CopyLftNameAnnot "plft12" "ulft_2"; (* initialization *)
   annot: CopyLftNameAnnot "plft11" "ulft_1"; (* initialization *)
   annot: StartLftAnnot "llft5" ["plft11";"ulft_2"]; (* borrow *)
   "__7" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft17" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft5" } (!{ PtrOp } ( "self" )));
   annot: StartLftAnnot "llft6" ["llft5"]; (* borrow *) (* 6<5 ,return lft > all  param lft*) 
   "__8" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft18" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Obj_inv_t"] []), "llft6" } (!{ PtrOp } ( "obj_to_take" )));
   annot: CopyLftNameAnnot "vlft21" "plft17"; (* function_call *)
   annot: CopyLftNameAnnot "vlft22" "plft18"; (* function_call *)                                         
   "__6" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE Obj_try_take_action_loc ["vlft21"; "vlft22"] [@{expr} use{ PtrOp } ("__7"); use{ PtrOp } ("__8"); I2v (1) U64];
   annot: EndLftAnnot "llft6"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft6"; (* endlft *)
   annot: StartLftAnnot "llft7" ["llft5"]; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft14" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } ("__6"));
   (* annot: CopyLftNameAnnot "vlft8" "plft15"; *) (* function_call *)
   (* annot: AliasLftAnnot "vlft23" ["plft14"(* ; "plft15" *)]; *) (* function_call *)
   "__4" <-{ BoolOp } CallE Option_T_is_some_Cap_loc ["plft14"] [@{expr} use{ PtrOp } ("__5")];
   annot: EndLftAnnot "llft7"; (* endlft *)
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   if{ BoolOp }: use{ BoolOp } ("__4") then
    Goto "_bb3"
   else
    Goto "_bb5"
  ]>%E $
  <[
  "_bb3" :=
   annot: StartLftAnnot "llft9" ["plft11";"plft13" ]; (* borrow *) (* (!!!!) *)
   "__9" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft19" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Obj_inv_t"] []), "llft9" } (!{ PtrOp } ( "self" )));
   annot: CopyLftNameAnnot "vlft10" "plft13"; (* composite *)
   annot: CopyLftNameAnnot "vlft10" "plft13"; (* borrow *)
   "__10" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft10" } (!{ PtrOp } ( "cap_to_take" )));
   annot: CopyLftNameAnnot "vlft24" "plft19"; (* function_call *)
   annot: CopyLftNameAnnot "vlft25" "plft20"; (* function_call *)
   "__0" <-{ StructOp unit_sl [] } CallE Obj_try_merge_cap_loc ["vlft24"; "vlft25"] [@{expr} use{ PtrOp } ("__9"); use{ PtrOp } ("__10")];
   annot: EndLftAnnot "llft9"; (* endlft *)
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   annot: EndLftAnnot "llft9"; (* endlft *)
   Goto "_bb6"
  ]>%E $
  <[
  "_bb5" :=
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb6"
  ]>%E $
  <[
  "_bb6" :=
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

(* Definition Obj_try_take_action_def (BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc : loc) (Cap_contains_loc : loc) (Option_T_is_some_Cap_loc : loc) (Option_T_unwrap_Cap_loc : loc) : function := {|
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
   annot: CopyLftNameAnnot "vlft4" "plft17"; (* composite *)
   annot: CopyLftNameAnnot "vlft4" "plft17"; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft4" } ((!{ PtrOp } ( "self" )) at{ Obj_sls } "caps"));
   "__8" <-{ PtrOp } &raw{ Shr } (!{ PtrOp } ( "obj" ));
   annot: StartLftAnnot "llft5" []; (* borrow *)
   "__7" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft22" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft5" } ("__8"));
   annot: CopyLftNameAnnot "vlft6" "plft22"; (* composite *)
   annot: CopyLftNameAnnot "vlft6" "plft22"; (* borrow *)
   "__6" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft21" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft6" } (!{ PtrOp } ( "__7" )));
   annot: CopyLftNameAnnot "vlft30" "plft21"; (* function_call *)
   annot: CopyLftNameAnnot "vlft29" "plft20"; (* function_call *)
   "cap_on_obj" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc ["vlft29"; "vlft30"] [@{expr} use{ PtrOp } ("__5"); use{ PtrOp } ("__6")];
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft5"; (* endlft *)
   annot: StartLftAnnot "llft7" []; (* borrow *)
   "__11" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft23" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } ("cap_on_obj"));
   annot: CopyLftNameAnnot "vlft8" "plft24"; (* function_call *)
   annot: AliasLftAnnot "vlft31" ["plft24"; "plft23"]; (* function_call *)
   "__10" <-{ BoolOp } CallE Option_T_is_some_Cap_loc ["vlft31"] [@{expr} use{ PtrOp } ("__11")];
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
   annot: CopyLftNameAnnot "vlft9" "plft26"; (* function_call *)
   "tem_cap" <-{ PtrOp } AnnotExpr (* function_call *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft25" (LftNameTreeLeaf))) (CallE Option_T_unwrap_Cap_loc [] [@{expr} use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__14")]);
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   annot: CopyLftNameAnnot "vlft10" "plft25"; (* composite *)
   annot: CopyLftNameAnnot "vlft10" "plft25"; (* borrow *)
   "__16" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft27" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft10" } (!{ PtrOp } ( "tem_cap" )));
   "__17" <-{ IntOp USize } use{ IntOp USize } ("action");
   annot: CopyLftNameAnnot "vlft32" "plft27"; (* function_call *)
   "__15" <-{ BoolOp } CallE Cap_contains_loc ["vlft32"] [@{expr} use{ PtrOp } ("__16"); use{ IntOp USize } ("__17")];
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
   annot: CopyLftNameAnnot "vlft11" "plft25"; (* composite *)
   annot: CopyLftNameAnnot "vlft11" "plft25"; (* borrow *)
   "__18" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft28" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft11" } (!{ PtrOp } ( "tem_cap" )));
   annot: CopyLftNameAnnot "vlft12" "plft28"; (* composite *)
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "Some" (RSTLitType ["Option_ty"] [RSTRef Shr "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_Some_sls ((PtrSynType))) [("0", use{ PtrOp } ("__18") : expr)]);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb7" :=
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "None" (RSTLitType ["Option_ty"] [RSTRef Shr "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_None_sls ((PtrSynType))) []);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb8" :=
   Goto "_bb10"
  ]>%E $
  <[
  "_bb9" :=
   "__9" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "None" (RSTLitType ["Option_ty"] [RSTRef Shr "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_None_sls ((PtrSynType))) []);
   Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   return (use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}. *)

Definition Obj_try_take_action_def (BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc : loc) (Cap_contains_loc : loc) (Option_T_is_some_Cap_loc : loc) (Option_T_unwrap_Cap_loc : loc) : function := {|
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
   annot: CopyLftNameAnnot "vlft4" "plft17"; (* composite *)
   annot: CopyLftNameAnnot "vlft4" "plft17"; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft4" } ((!{ PtrOp } ( "self" )) at{ Obj_sls } "caps"));
   "__8" <-{ PtrOp } &raw{ Shr } (!{ PtrOp } ( "obj" ));
   annot: StartLftAnnot "llft5" ["plft17"]; (* borrow *)
   "__7" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft22" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft5" } ("__8"));
   annot: CopyLftNameAnnot "vlft6" "plft22"; (* composite *)
   annot: CopyLftNameAnnot "vlft6" "plft22"; (* borrow *)
   "__6" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft21" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft6" } (!{ PtrOp } ( "__7" )));
   annot: CopyLftNameAnnot "vlft30" "plft21"; (* function_call *)
   annot: CopyLftNameAnnot "vlft29" "plft20"; (* function_call *)
   "cap_on_obj" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE BTreeMap_KVA_get_constObj_Cap_std_alloc_Global_constObj_loc ["vlft30"; "vlft29"] [@{expr} use{ PtrOp } ("__5"); use{ PtrOp } ("__6")];
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft5"; (* endlft *)
   annot: StartLftAnnot "llft7" ["plft17"]; (* borrow *)
   "__11" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft23" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } ("cap_on_obj"));
   (* annot: AliasLftAnnot "vlft31" ["plft23"(* ; "plft24" *)]; *) (* function_call *)
   (* annot: CopyLftNameAnnot "vlft8" "plft24"; *) (* function_call *)
   "__10" <-{ BoolOp } CallE Option_T_is_some_Cap_loc ["llft7"] [@{expr} use{ PtrOp } ("__11")];
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
   (* annot: CopyLftNameAnnot "vlft9" "plft26"; *) (* function_call *)
   "tem_cap" <-{ PtrOp } AnnotExpr (* function_call *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft25" (LftNameTreeLeaf))) (CallE Option_T_unwrap_Cap_loc [] [@{expr} use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__14")]);
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   annot: CopyLftNameAnnot "vlft10" "plft25"; (* composite *)
   annot: CopyLftNameAnnot "vlft10" "plft25"; (* borrow *)
   "__16" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft27" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft10" } (!{ PtrOp } ( "tem_cap" )));
   "__17" <-{ IntOp USize } use{ IntOp USize } ("action");
   annot: CopyLftNameAnnot "vlft32" "plft27"; (* function_call *)
   "__15" <-{ BoolOp } CallE Cap_contains_loc ["vlft32"] [@{expr} use{ PtrOp } ("__16"); use{ IntOp USize } ("__17")];
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
   annot: CopyLftNameAnnot "vlft11" "plft25"; (* composite *)
   annot: CopyLftNameAnnot "vlft11" "plft25"; (* borrow *)
   "__18" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft28" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft11" } (!{ PtrOp } ( "tem_cap" )));
   (* annot: CopyLftNameAnnot "vlft12" "plft28"; *) (* composite *)
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "Some" (RSTLitType ["Option_ty"] [RSTRef Shr "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_Some_sls ((PtrSynType))) [("0", use{ PtrOp } ("__18") : expr)]);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb7" :=
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "None" (RSTLitType ["Option_ty"] [RSTRef Shr "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_None_sls ((PtrSynType))) []);
   Goto "_bb8"
  ]>%E $
  <[
  "_bb8" :=
   Goto "_bb10"
  ]>%E $
  <[
  "_bb9" :=
   "__9" <-{ StructOp unit_sl [] } zst_val;
   "__0" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } EnumInit (Option_els ((PtrSynType))) "None" (RSTLitType ["Option_ty"] [RSTRef Shr "placeholder_lft" (RSTLitType ["Cap_inv_t"] [])]) (StructInit (Option_None_sls ((PtrSynType))) []);
   Goto "_bb10"
  ]>%E $
  <[
  "_bb10" :=
   return (use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Obj_try_take_action_mut_def (BTreeMap_KVA_get_mut_constObj_Cap_std_alloc_Global_constObj_loc : loc) (Cap_contains_loc : loc) (Option_T_is_some_mutCap_loc : loc) (Option_T_unwrap_mutCap_loc : loc) : function := {|
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


Definition Obj_try_merge_cap_def (BTreeMap_KVA_get_mut_constObj_Cap_std_alloc_Global_constObj_loc : loc) (BTreeMap_KVA_insert_constObj_Cap_std_alloc_Global_loc : loc) (Cap_clone_loc : loc) (Option_T_is_some_mutCap_loc : loc) (Option_T_unwrap_mutCap_loc : loc) : function := {|
 f_args := [
  ("self", void* : layout);
  ("cap_to_merge", void* : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("obj_ptr", void* : layout);
  ("__4", void* : layout);
  ("prev_cap", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__6", void* : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("issome", bool_layout : layout);
  ("__10", void* : layout);
  ("__11", bool_layout : layout);
  ("tempright1", (it_layout USize) : layout);
  ("mutcap", void* : layout);
  ("__14", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("tempright2", (it_layout USize) : layout);
  ("tempright3", (it_layout USize) : layout);
  ("__17", (it_layout USize) : layout);
  ("__18", (it_layout USize) : layout);
  ("__19", (it_layout USize) : layout);
  ("__20", (use_layout_alg' (((Option_els ((Cap_st))) : syn_type))) : layout);
  ("__21", void* : layout);
  ("__22", void* : layout);
  ("__23", (use_layout_alg' (Cap_st)) : layout);
  ("__24", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft13" "ulft_2"; (* initialization *)
   annot: CopyLftNameAnnot "plft12" "ulft_1"; (* initialization *)
   "__4" <-{ PtrOp } use{ PtrOp } ((!{ PtrOp } ( "cap_to_merge" )) at{ Cap_sls } "obj");
   "obj_ptr" <-{ PtrOp } use{ PtrOp } ("__4");
   annot: StartLftAnnot "llft4" ["plft12"]; (* borrow *)
   "__6" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft15" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["BTreeMap_inv_t"] [RSTLitType ["alias_ptr_t"] []; RSTLitType ["Cap_inv_t"] []; RSTLitType ["Global_ty"] []]), "llft4" } ((!{ PtrOp } ( "self" )) at{ Obj_sls } "caps"));
   annot: StartLftAnnot "llft5" []; (* borrow *)
   "__8" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft17" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft5" } ("obj_ptr"));
   annot: CopyLftNameAnnot "vlft6" "plft17"; (* composite *)
   annot: CopyLftNameAnnot "vlft6" "plft17"; (* borrow *)
   "__7" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft16" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft6" } (!{ PtrOp } ( "__8" )));
   annot: CopyLftNameAnnot "vlft25" "plft16"; (* function_call *)
   annot: CopyLftNameAnnot "vlft24" "plft15"; (* function_call *)
   "prev_cap" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE BTreeMap_KVA_get_mut_constObj_Cap_std_alloc_Global_constObj_loc ["vlft24"; "vlft25"] [@{expr} use{ PtrOp } ("__6"); use{ PtrOp } ("__7")];
   annot: EndLftAnnot "llft5"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft5"; (* endlft *)
   annot: StartLftAnnot "llft7" []; (* borrow *)
   "__10" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft18" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } ("prev_cap"));
   annot: CopyLftNameAnnot "vlft8" "plft19"; (* function_call *)
   annot: AliasLftAnnot "vlft26" ["plft19"; "plft18"]; (* function_call *)
   "issome" <-{ BoolOp } CallE Option_T_is_some_mutCap_loc ["vlft26"] [@{expr} use{ PtrOp } ("__10")];
   annot: EndLftAnnot "llft7"; (* endlft *)
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   annot: EndLftAnnot "llft7"; (* endlft *)
   "__11" <-{ BoolOp } use{ BoolOp } ("issome");
   if{ BoolOp }: use{ BoolOp } ("__11") then
    Goto "_bb3"
   else
    Goto "_bb5"
  ]>%E $
  <[
  "_bb3" :=
   "tempright1" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "cap_to_merge" )) at{ Cap_sls } "rights");
   "__14" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("prev_cap");
   annot: CopyLftNameAnnot "vlft9" "plft21"; (* function_call *)
   "mutcap" <-{ PtrOp } AnnotExpr (* function_call *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (CallE Option_T_unwrap_mutCap_loc [] [@{expr} use{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } ("__14")]);
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   "tempright2" <-{ IntOp USize } use{ IntOp USize } ((!{ PtrOp } ( "mutcap" )) at{ Cap_sls } "rights");
   "__17" <-{ IntOp USize } use{ IntOp USize } ("tempright1");
   "__18" <-{ IntOp USize } use{ IntOp USize } ("tempright2");
   "tempright3" <-{ IntOp USize } (use{ IntOp USize } ("__17")) |{ IntOp USize , IntOp USize } (use{ IntOp USize } ("__18"));
   "__19" <-{ IntOp USize } use{ IntOp USize } ("tempright3");
   (!{ PtrOp } ( "mutcap" )) at{ Cap_sls } "rights" <-{ IntOp USize } use{ IntOp USize } ("__19");
   annot: EndLftAnnot "llft4"; (* endlft *)
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb8"
  ]>%E $
  <[
  "_bb5" :=
   annot: EndLftAnnot "llft4"; (* endlft *)
   annot: StartLftAnnot "llft10" ["plft12"]; (* borrow *)
   "__21" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft22" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["BTreeMap_inv_t"] [RSTLitType ["alias_ptr_t"] []; RSTLitType ["Cap_inv_t"] []; RSTLitType ["Global_ty"] []]), "llft10" } ((!{ PtrOp } ( "self" )) at{ Obj_sls } "caps"));
   "__22" <-{ PtrOp } use{ PtrOp } ("obj_ptr");
   annot: CopyLftNameAnnot "vlft11" "plft13"; (* composite *)
   annot: CopyLftNameAnnot "vlft11" "plft13"; (* borrow *)
   "__24" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft23" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft11" } (!{ PtrOp } ( "cap_to_merge" )));
   annot: CopyLftNameAnnot "vlft27" "plft23"; (* function_call *)
   "__23" <-{ (use_op_alg' (Cap_st)) } CallE Cap_clone_loc ["vlft27"] [@{expr} use{ PtrOp } ("__24")];
   Goto "_bb6"
  ]>%E $
  <[
  "_bb6" :=
   annot: CopyLftNameAnnot "vlft28" "plft22"; (* function_call *)
   "__20" <-{ (use_op_alg' (((Option_els ((Cap_st))) : syn_type))) } CallE BTreeMap_KVA_insert_constObj_Cap_std_alloc_Global_loc ["vlft28"] [@{expr} use{ PtrOp } ("__21"); use{ PtrOp } ("__22"); use{ (use_op_alg' (Cap_st)) } ("__23")];
   annot: EndLftAnnot "llft10"; (* endlft *)
   Goto "_bb7"
  ]>%E $
  <[
  "_bb7" :=
   annot: EndLftAnnot "llft10"; (* endlft *)
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb8"
  ]>%E $
  <[
  "_bb8" :=
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Obj_grant_def (Obj_try_merge_cap_loc : loc) (Obj_try_take_action_loc : loc) (Option_T_is_some_Cap_loc : loc) : function := {|
 f_args := [
  ("self", void* : layout);
  ("to_grant", void* : layout);
  ("cap_to_grant", void* : layout)
 ];
 f_local_vars := [
  ("__0", (layout_of unit_sl) : layout);
  ("__4", bool_layout : layout);
  ("__5", void* : layout);
  ("__6", (use_layout_alg' (((Option_els ((PtrSynType))) : syn_type))) : layout);
  ("__7", void* : layout);
  ("__8", void* : layout);
  ("__9", void* : layout);
  ("__10", void* : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   annot: CopyLftNameAnnot "plft13" "ulft_3"; (* initialization *)
   annot: CopyLftNameAnnot "plft12" "ulft_2"; (* initialization *)
   annot: CopyLftNameAnnot "plft11" "ulft_1"; (* initialization *)
   annot: CopyLftNameAnnot "vlft5" "plft11"; (* composite *)
   annot: CopyLftNameAnnot "vlft5" "plft11"; (* borrow *)
   "__7" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft17" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft5" } (!{ PtrOp } ( "self" )));
   annot: StartLftAnnot "llft6" ["plft12";"ulft_1"]; (* borrow *)
   "__8" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft18" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Obj_inv_t"] []), "llft6" } (!{ PtrOp } ( "to_grant" )));
   annot: CopyLftNameAnnot "vlft22" "plft18"; (* function_call *)
   annot: CopyLftNameAnnot "vlft21" "plft17"; (* function_call *)
   "__6" <-{ (use_op_alg' (((Option_els ((PtrSynType))) : syn_type))) } CallE Obj_try_take_action_loc ["vlft21"; "vlft22"] [@{expr} use{ PtrOp } ("__7"); use{ PtrOp } ("__8"); I2v (2) U64];
   annot: EndLftAnnot "llft6"; (* endlft *)
   Goto "_bb1"
  ]>%E $
  <[
  "_bb1" :=
   annot: EndLftAnnot "llft6"; (* endlft *)
   annot: StartLftAnnot "llft7" ["ulft_1";"ulft_2"]; (* borrow *)
   "__5" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft14" (LftNameTreeLeaf))) (&ref{ Shr, None, "llft7" } ("__6"));
(*    annot: AliasLftAnnot "vlft23" ["plft14"; "plft15"]; (* function_call *) *)
(*    annot: CopyLftNameAnnot "vlft8" "plft15"; (* function_call *) *)
   "__4" <-{ BoolOp } CallE Option_T_is_some_Cap_loc ["llft7"] [@{expr} use{ PtrOp } ("__5")];
   annot: EndLftAnnot "llft7"; (* endlft *)
   Goto "_bb2"
  ]>%E $
  <[
  "_bb2" :=
   if{ BoolOp }: use{ BoolOp } ("__4") then
    Goto "_bb3"
   else
    Goto "_bb5"
  ]>%E $
  <[
  "_bb3" :=
   annot: StartLftAnnot "llft9" ["plft12";"plft13";"ulft_3"]; (* borrow *)
   "__9" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft19" (LftNameTreeLeaf))) (&ref{ Mut, Some (RSTLitType ["Obj_inv_t"] []), "llft9" } (!{ PtrOp } ( "to_grant" )));
   annot: CopyLftNameAnnot "vlft10" "plft13"; (* composite *)
   annot: CopyLftNameAnnot "vlft10" "plft13"; (* borrow *)
   "__10" <-{ PtrOp } AnnotExpr (* assignment *) 0 (GetLftNamesAnnot (LftNameTreeRef "plft20" (LftNameTreeLeaf))) (&ref{ Shr, None, "vlft10" } (!{ PtrOp } ( "cap_to_grant" )));
   annot: CopyLftNameAnnot "vlft25" "plft20"; (* function_call *)
   annot: CopyLftNameAnnot "vlft24" "plft19"; (* function_call *)
   "__0" <-{ StructOp unit_sl [] } CallE Obj_try_merge_cap_loc ["vlft24"; "vlft25"] [@{expr} use{ PtrOp } ("__9"); use{ PtrOp } ("__10")];
   annot: EndLftAnnot "llft9"; (* endlft *)
   Goto "_bb4"
  ]>%E $
  <[
  "_bb4" :=
   annot: EndLftAnnot "llft9"; (* endlft *)
   Goto "_bb6"
  ]>%E $
  <[
  "_bb5" :=
   "__0" <-{ StructOp unit_sl [] } zst_val;
   Goto "_bb6"
  ]>%E $
  <[
  "_bb6" :=
   return (use{ StructOp unit_sl [] } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

Definition Obj_delete_def (Cap_contains_loc : loc) (Obj_try_take_action_mut_loc : loc) (Option_T_is_some_mutCap_loc : loc) (Option_T_unwrap_mutCap_loc : loc) : function := {|
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
|}.


Definition Obj_turn_on_all_rights_def  : function := {|
 f_args := [
  
 ];
 f_local_vars := [
  ("__0", (it_layout USize) : layout);
  ("__1", (it_layout USize) : layout);
  ("__2", (it_layout USize) : layout)
 ];
 f_code :=
  <[
  "_bb0" :=
   "__2" <-{ IntOp USize } (I2v (1) U64) |{ IntOp USize , IntOp USize } (I2v (2) U64);
   "__1" <-{ IntOp USize } (use{ IntOp USize } ("__2")) |{ IntOp USize , IntOp USize } (I2v (4) U64);
   "__0" <-{ IntOp USize } (use{ IntOp USize } ("__1")) |{ IntOp USize , IntOp USize } (I2v (16) U64);
   return (use{ IntOp USize } ("__0"))
  ]>%E $
  ∅;
 f_init := "_bb0";
|}.

End code.