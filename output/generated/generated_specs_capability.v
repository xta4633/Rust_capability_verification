From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.capability_main Require Export generated_code_capability.
From stdlib.option.option.generated Require Export generated_specs_option.
From stdlib.alloc.alloc.generated Require Export generated_specs_alloc.
From stdlib.btreemap.btreemap.generated Require Export generated_specs_btreemap.
Section Cdt_ty.
  Context `{!refinedrustGS Σ}.


  Definition Cdt_ty : type (plist place_rfn []).
  Proof using  . exact (struct_t Cdt_sls +[]). Defined.
  Definition Cdt_rt : Type.
  Proof using  . let __a := eval hnf in (rt_of Cdt_ty) in exact __a. Defined.
  Global Typeclasses Transparent Cdt_ty.
  Global Typeclasses Transparent Cdt_rt.
End Cdt_ty.
Global Arguments Cdt_rt : clear implicits.

Section Cap_ty.
  Context `{!refinedrustGS Σ}.


  Definition Cap_ty : type (plist place_rfn [loc : Type; Z : Type; Cdt_rt : Type]).
  Proof using  . exact (struct_t Cap_sls +[alias_ptr_t;(int USize);Cdt_ty]). Defined.
  Definition Cap_rt : Type.
  Proof using  . let __a := eval hnf in (rt_of Cap_ty) in exact __a. Defined.
  Global Typeclasses Transparent Cap_ty.
  Global Typeclasses Transparent Cap_rt.
End Cap_ty.
Global Arguments Cap_rt : clear implicits.

Section Cap_inv_t.
  Context `{!refinedrustGS Σ}.

  Program Definition Cap_inv_t_inv_spec : ex_inv_def (Cap_rt) ( loc * Z) := mk_ex_inv_def
    (λ π inner_rfn '(obj, Right), ∃ (cdt : _), ⌜inner_rfn = -[#(obj); #(Right); #(cdt)]⌝ ∗ True)%I
    (λ π κ inner_rfn '(obj, Right), ∃ (cdt : _), ⌜inner_rfn = -[#(obj); #(Right); #(cdt)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition Cap_inv_t : type ( loc * Z) :=
    ex_plain_t _ _ Cap_inv_t_inv_spec Cap_ty.
  Global Typeclasses Transparent Cap_inv_t.
  Definition Cap_inv_t_rt : Type.
  Proof using  . let __a := eval hnf in (rt_of Cap_inv_t) in exact __a. Defined.
  Global Typeclasses Transparent Cap_inv_t_rt.
End Cap_inv_t.
Global Arguments Cap_inv_t_rt : clear implicits.

Section Obj_ty.
  Context `{!refinedrustGS Σ}.


  Definition Obj_ty : type (plist place_rfn [(BTreeMap_inv_t_rt (loc) (Cap_inv_t_rt) (Global_rt)) : Type]).
  Proof using  . exact (struct_t Obj_sls +[(BTreeMap_inv_t ((alias_ptr_t)) ((Cap_inv_t)) ((Global_ty)))]). Defined.
  Definition Obj_rt : Type.
  Proof using  . let __a := eval hnf in (rt_of Obj_ty) in exact __a. Defined.
  Global Typeclasses Transparent Obj_ty.
  Global Typeclasses Transparent Obj_rt.
End Obj_ty.
Global Arguments Obj_rt : clear implicits.

Section Obj_inv_t.
  Context `{!refinedrustGS Σ}.

  Program Definition Obj_inv_t_inv_spec : ex_inv_def (Obj_rt) (BTreeMap_inv_t_rt loc Cap_inv_t_rt Global_rt) := mk_ex_inv_def
    (λ π inner_rfn 'caps, ⌜inner_rfn = -[#(caps)]⌝ ∗ True)%I
    (λ π κ inner_rfn 'caps, ⌜inner_rfn = -[#(caps)]⌝ ∗ True)%I
    ([])
    ([])
    _ _ _
  .
  Next Obligation. ex_t_solve_persistent. Qed.
  Next Obligation. ex_plain_t_solve_shr_mono. Qed.
  Next Obligation. ex_plain_t_solve_shr. Qed.

  Definition Obj_inv_t : type (BTreeMap_inv_t_rt loc Cap_inv_t_rt Global_rt) :=
    ex_plain_t _ _ Obj_inv_t_inv_spec Obj_ty.
  Global Typeclasses Transparent Obj_inv_t.
  Definition Obj_inv_t_rt : Type.
  Proof using  . let __a := eval hnf in (rt_of Obj_inv_t) in exact __a. Defined.
  Global Typeclasses Transparent Obj_inv_t_rt.
End Obj_inv_t.
Global Arguments Obj_inv_t_rt : clear implicits.

Inductive ref_to_loc : loc -> (BTreeMap_inv_t_rt loc Cap_inv_t_rt Global_rt) -> Prop :=
  | ref x y : False ->
              ref_to_loc x y.

Section specs.
Context `{!refinedrustGS Σ}.

Definition type_of_Cap_contains  :=
  fn(∀ ((), ulft_1) : 1 | (self, bit_position) : (_ * _), (λ ϝ, []); #self @ (shr_ref Cap_inv_t ulft_1), bit_position @ (int USize); (λ π : thread_id, True))
    → ∃ (j) : (bool), j @ bool_t; (λ π : thread_id, (⌜ (j = true ∧ (Z.land (self.2) bit_position ≠ 0) )  ∨ (j = false ∧ (Z.land (self.2) bit_position = 0))⌝)).
Definition type_of_Obj_new  :=
  fn(∀ (()) : 0 | _ : unit, (λ ϝ, []); (λ π : thread_id, True))
    → ∃ (x) : (_), x @ Obj_inv_t; (λ π : thread_id, True).
Definition type_of_Obj_get_cap_on  :=
  fn(∀ ((), ulft_2, ulft_1) : 2 | (self, obj, γ) : (_ * _ * _), (λ ϝ, []); #self @ (shr_ref Obj_inv_t ulft_1), (#obj,γ) @ (mut_ref Obj_inv_t ulft_2); (λ π : thread_id, True))
    → ∃ (x) : (loc), <#>@{option} (self !! x) @ (Option_ty (((shr_ref Cap_inv_t ulft_1)))); (λ π : thread_id, (⌜ref_to_loc x obj⌝)).
Definition type_of_Obj_take  :=
  fn(∀ ((), ulft_1, ulft_2, ulft_3) : 3 | (self, obj_to_take, cap_to_take, γ1, γ2) : (_ * _ * _ * _ * _), (λ ϝ, []); (#self,γ1) @ (mut_ref Obj_inv_t ulft_1), (#obj_to_take,γ2) @ (mut_ref Obj_inv_t ulft_2), #cap_to_take @ (shr_ref Cap_inv_t ulft_3); (λ π : thread_id, True))
    → ∃ (x) : (loc), () @ unit_t; (λ π : thread_id, (gvar_pobs γ1 (match (self !! x) with                   
                        |Some #y => match (Z.land  (snd y) 1) with
                                    | 0 => self
                                    | _ => match self !! (fst cap_to_take) with
                                           | Some #z => <[ (fst cap_to_take) := #(fst cap_to_take , (Z.lor (snd cap_to_take) (snd z) ))  ]> self    
                                           | _   => <[ (fst cap_to_take) := #cap_to_take ]> self          
                                           end  
                                    end   
                        | _ => self  
                       end
                )) ∗ (gvar_pobs γ2 (obj_to_take)) ∗ (⌜ref_to_loc x obj_to_take⌝)).
Definition type_of_Obj_try_take_action  :=
  fn(∀ ((), ulft_2, ulft_1) : 2 | (self, obj, action, γ) : (_ * _ * _ * _), (λ ϝ, []); #self @ (shr_ref Obj_inv_t ulft_1), (#obj,γ) @ (mut_ref Obj_inv_t ulft_2), action @ (int USize); (λ π : thread_id, (⌜(action)%Z < 32⌝)))
    → ∃ (x) : (loc), <#>@{option} (match (self !! x) with
                | Some #y => match (Z.land action (snd y)) with
                                | 0 => None
                                | _ => Some #y 
                                end
                | _ => None
                end ) @ (Option_ty (((shr_ref Cap_inv_t ulft_1)))); (λ π : thread_id, (gvar_pobs γ (obj)) ∗ (⌜ref_to_loc x obj⌝)).
Definition type_of_Obj_try_take_action_mut  :=
  fn(∀ ((), ulft_2, ulft_1) : 2 | (self, obj, action, γ1, γ2) : (_ * _ * _ * _ * _), (λ ϝ, []); (#self,γ1) @ (mut_ref Obj_inv_t ulft_1), (#obj,γ2) @ (mut_ref Obj_inv_t ulft_2), action @ (int USize); (λ π : thread_id, True))
    → ∃ (x, γi) : (loc * gname), <#>@{option} (match self !! x  with                     
                                |Some #y =>match (Z.land (snd y) action) with 
                                                |0 => None         
                                                |_ => Some (#y, γi)
                                                end 
                                |_ =>None                    
                            end)
                    @ (Option_ty (((mut_ref Cap_inv_t ulft_1)))); (λ π : thread_id, (gvar_pobs γ1 (match self !! x with   
                            | Some #y => <[x := PlaceGhost γi ]> self                
                            | _ => self  
                        end)) ∗ (gvar_pobs γ2 (obj)) ∗ (match self !! x with   
                            | Some #y => match (Z.land (snd y) action ) with 
                                             | 0 => gvar_pobs γi y
                                             | _ => True
                                            end 
                            | _ => True
                            end
                    ) ∗ (⌜ref_to_loc x obj⌝)).
Definition type_of_Obj_try_merge_cap  :=
  fn(∀ ((), ulft_2, ulft_1) : 2 | (self, cap_to_merge, γ) : (_ * _ * _), (λ ϝ, []); (#self,γ) @ (mut_ref Obj_inv_t ulft_1), #cap_to_merge @ (shr_ref Cap_inv_t ulft_2); (λ π : thread_id, True))
    → ∃ _ : unit, () @ unit_t; (λ π : thread_id, (gvar_pobs γ ((match self !! (fst cap_to_merge) with
                        | Some #y => <[(fst cap_to_merge) := #(fst cap_to_merge , (Z.lor (snd cap_to_merge) (snd y)))]> self
                        | _ => <[(fst cap_to_merge) := #cap_to_merge ]> self
                        end)
    ))).
Definition type_of_Obj_grant  :=
  fn(∀ ((), ulft_1, ulft_2, ulft_3) : 3 | (self, to_grant, γ, cap_to_grant) : (_ * _ * _ * _), (λ ϝ, []); #self @ (shr_ref Obj_inv_t ulft_1), (#to_grant,γ) @ (mut_ref Obj_inv_t ulft_2), #cap_to_grant @ (shr_ref Cap_inv_t ulft_3); (λ π : thread_id, True))
    → ∃ (x) : (_), () @ unit_t; (λ π : thread_id, (gvar_pobs γ (match self !! x with
                            |Some #y => match (Z.land y.2  2) with
                                            | 0  => to_grant  
                                            | _  => match to_grant !! (fst cap_to_grant)  with
                                                        | Some #z => <[(fst cap_to_grant) := #(fst cap_to_grant , (Z.lor (snd cap_to_grant) (snd z) ))  ]> to_grant                                                                            
                                                        |  _      => <[(fst cap_to_grant) := #cap_to_grant ]> to_grant                     
                                                        end
                                            end             
                            |_ => to_grant
                            end
                    )) ∗ (⌜ref_to_loc x to_grant⌝)).
Definition type_of_Obj_delete  :=
  fn(∀ ((), ulft_2, ulft_1) : 2 | (self, γ1, to_delete, γ2, right1) : (_ * _ * _ * _ * _), (λ ϝ, []); (#self,γ1) @ (mut_ref Obj_inv_t ulft_1), (#to_delete,γ2) @ (mut_ref Obj_inv_t ulft_2), right1 @ (int USize); (λ π : thread_id, True))
    → ∃ (x, γ') : (loc * _), () @ unit_t; (λ π : thread_id, (gvar_pobs γ1 (match self !! x with   
                            | Some #y => match (Z.land (snd y) 16) with 
                                        | 0 => self  
                                        | _ => <[x := PlaceGhost γ' ]> self
                                        end             
                            | _ => self  
                            end)) ∗ (gvar_pobs γ2 (to_delete)) ∗ (match self !! x with   
                        | Some #y =>  match (Z.land (snd y) 16) with 
                                      | 0 =>  True
                                      | _ => gvar_pobs γ' match (Z.land (snd y) right1) with
                                                          | 0 =>  y
                                                          | _ => ((fst y) , Z.lxor (snd y) right1)
                                                          end
                                      end             
                        | _ => True
                    end) ∗ (⌜ref_to_loc x to_delete⌝)).
Definition type_of_Obj_turn_on_all_rights  :=
  fn(∀ (()) : 0 | _ : unit, (λ ϝ, []); (λ π : thread_id, True))
    → ∃ _ : unit, 23 @ (int USize); (λ π : thread_id, True).
Definition type_of_Cap_clone  :=
  fn(∀ ((), ulft_1) : 1 | (self) : (_), (λ ϝ, []); #self @ (shr_ref Cap_inv_t ulft_1); (λ π : thread_id, True))
    → ∃ _ : unit, self @ Cap_inv_t; (λ π : thread_id, True).

End specs.