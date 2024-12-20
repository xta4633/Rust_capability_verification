#![allow(dead_code)]


#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![feature(allocator_api)]
#![rr::coq_prefix("refinedrust.examples","stdlib.btreemap")]
#![rr::include("alloc")]
#![rr::include("btreemap")]
#![rr::include("option")]

#![allow(unused)]


//use bitflags::bitflags;
use std::collections::BTreeMap;
use std::cell::RefCell;
//use std::ptr::addr_of_mut;
use std::rc::Rc;

const TAKE: usize = 1;
const GRANT: usize = 1 << 1;
const CREATE: usize = 1 << 2;
const OTHERS: usize = 1 << 3;
const DELETE: usize = 1 << 4;

#[derive(Clone, Debug)]
struct Cdt ;

#[rr::refined_by("(obj, Right)" : " loc * Z")]
#[rr::exists("cdt")]
#[derive(Clone, Debug)]
struct Cap {
    #[rr::field("obj")]
    obj: *mut Obj,
    #[rr::field("Right")]
    rights: usize,
    #[rr::field("cdt")]
    cdt: Cdt,
}

#[derive(Clone, Debug)]
#[rr::refined_by("caps" : "BTreeMap_inv_t_rt loc Cap_inv_t_rt Global_rt")]
struct Obj {
    #[rr::field("caps")]
    pub(crate) caps: BTreeMap<*const Obj, Cap>,
}


impl Cap {

    #[rr::params("self", "bit_position")]
    #[rr::args("#self", "bit_position")]
 //   #[rr::requires("(self.2)%Z < 32")]
    #[rr::exists("j" : "bool")]
    #[rr::returns("j")]
    #[rr::ensures(" (j = true ∧ (Z.land (self.2) bit_position ≠ 0) )  ∨ (j = false ∧ (Z.land (self.2) bit_position = 0))")]
    pub fn contains(&self, bit_position: usize) -> bool {
        (self.rights & bit_position) != 0
    }

    #[rr::only_spec]
    #[rr::params("self")]
    #[rr::args("#self")]
    #[rr::returns("self")]
    fn clone(&self) -> Self {
        unimplemented!(); 
    }


}



impl Obj {

    #[rr::exists("x")]
    #[rr::returns("x")]
    pub fn new() -> Self {
        Self {
            caps: BTreeMap::new(),
        }
    }

    /* 
    #[rr::params("self","obj", "obj_ref")]
    #[rr::args("#self", "#obj", "obj_ref")]
    #[rr::returns("<#>@{option} (self !! borrow_from obj)")]
    #[inline]
    pub fn insert_cap_on(&mut self, obj: &Obj,  obj_ref:  &mut Obj )  {
 
        let obj_ptr = {
            obj_ref as *mut Obj
        };
        let new_cap = Cap {
            obj: obj_ptr,
            rights:1,
            cdt: Cdt,
        };
        self.caps.insert((obj as _), new_cap);
    }
    */

    #[rr::params("self","obj", "γ")]
    #[rr::args("#self", "(#obj,γ)")]
    #[rr::exists("x": "loc")]
   // #[rr::requires("ident x obj")]
    #[rr::returns("<#>@{option} (self !! x)")]
    #[rr::ensures("ref_to_loc x obj")]
    #[inline]
    pub fn get_cap_on(&self, obj: &mut Obj) -> Option<&Cap> {
        self.caps.get(&(obj as (*const Obj)))
    }


    #[rr::params("self","obj_to_take", "cap_to_take",  "γ1" , "γ2")]
    #[rr::args("(#self,γ1)","(#obj_to_take,γ2)","#cap_to_take" )]
    #[rr::exists("x":"loc")] 
    #[rr::observe("γ1":"match (self !! x) with                   
                        |Some #y => match (Z.land  (snd y) 1) with
                                    | 0 => self
                                    | _ => match self !! (fst cap_to_take) with
                                           | Some #z => <[ (fst cap_to_take) := #(fst cap_to_take , (Z.lor (snd cap_to_take) (snd z) ))  ]> self    
                                           | _   => <[ (fst cap_to_take) := #cap_to_take ]> self          
                                           end  
                                    end   
                        | _ => self  
                       end
                ")]
    #[rr::observe("γ2":"obj_to_take")]
    #[rr::ensures("ref_to_loc x obj_to_take")]
    pub fn take(&mut self, obj_to_take: &mut Obj, cap_to_take: &Cap) {
        if self.try_take_action(obj_to_take, TAKE).is_some() {
            self.try_merge_cap(cap_to_take)
        }
    }
 
/*
    #[rr::params("self","obj" ,"action", "γ")]
    #[rr::args("#self", "(#obj,γ)" ,"action")]
    #[rr::requires("(action)%Z < 32")]
    #[rr::exists("x": "loc")]
    #[rr::returns("<#>@{option} (match (self !! x) with
                   | Some #y => match (Z.land action (snd y)) with
                                  | 0 => None
                                  | _ => Some #y 
                                  end
                   | _ => None
                    end )")] 
    #[rr::ensures("ref_to_loc x obj")]
    fn try_take_action(&self, obj: &mut Obj, action: usize) -> Option<&Cap> {
        let (cap_on_obj) = self.caps.get(&(obj as _));
        if (cap_on_obj.is_some()) { 
            return if cap_on_obj.unwrap().contains(action) { //unwrap 会返回 Some 包含的值。如果值为 None，则会触发 panic! 
                (cap_on_obj)
            } else {
                None
            };
        }
        None
    }
*/

    #[rr::params("self","obj" ,"action", "γ")]
    #[rr::args("#self", "(#obj,γ)" ,"action")]
    #[rr::requires("(action)%Z < 32")]
    #[rr::exists("x": "loc")]
    #[rr::returns("<#>@{option} (match (self !! x) with
                | Some #y => match (Z.land action (snd y)) with
                                | 0 => None
                                | _ => Some #y 
                                end
                | _ => None
                end )")]
    #[rr::observe("γ": "obj")]
    #[rr::ensures("ref_to_loc x obj")]
    fn try_take_action(&self, obj: &mut Obj, action: usize) -> Option<&Cap> {
        let (cap_on_obj) = self.caps.get(&(obj as _));
        if (cap_on_obj.is_some()) { 
            let tem_cap = cap_on_obj.unwrap();
            return if tem_cap.contains(action){
                Some(tem_cap)
            } else {
                None
            };
        }
        None
    }


    #[rr::params("self","obj" ,"action","γ1","γ2")]
    #[rr::args("(#self,γ1)","(#obj,γ2)","action")]
    #[rr::exists("x":"loc","γi":"gname")]       
    #[rr::returns("<#>@{option} (match self !! x  with                     
                                |Some #y =>match (Z.land (snd y) action) with 
                                                |0 => None         
                                                |_ => Some (#y, γi)
                                                end 
                                |_ =>None                    
                            end)
                   ")]
    #[rr::observe("γ1":"match self !! x with   
                            | Some #y => <[x := PlaceGhost γi ]> self                
                            | _ => self  
                        end"
                    )]
    #[rr::observe("γ2":"obj")]
    #[rr::ensures(#iris "match self !! x with   
                            | Some #y => match (Z.land (snd y) action ) with 
                                             | 0 => gvar_pobs γi y
                                             | _ => True
                                            end 
                            | _ => True
                            end
                    ")]
    #[rr::ensures("ref_to_loc x obj")]
    fn try_take_action_mut(&mut self, obj: &mut Obj, action: usize) -> Option<&mut Cap> { 
        let cap_on_obj =self.caps.get_mut(&(obj as _));  //self是&mut Obj类型，caps是BTreeMap<*const Obj, Cap>类型，&(obj as _)是&(*const Obj)类型
        if cap_on_obj.is_some() {                        //cap_on_obj是Option<&mut Cap>类型，返回true或者false
            let tem_cap =cap_on_obj.unwrap();            //tem_cap是&mut Cap类型                                    
            return if tem_cap.contains(action) {
                Some(tem_cap)                            //返回类型是Option<&mut Cap>类型
            } else {
                None
            };
        }
        None
    }
/*
    fn try_merge_cap(&mut self, cap_to_merge: &Cap) {
        let obj_ptr = cap_to_merge.obj as *const Obj;
        // if there already exists cap points to the same obj as `cap_to_merge`, their rights will be merged
        // otherwise, new entry will be created
        self.caps
            .entry(obj_ptr)
            .and_modify(|prev_cap| prev_cap.rights |= cap_to_merge.rights)
            .or_insert(cap_to_merge.clone());

    }
*/

    #[rr::params("self", "cap_to_merge",/*"global_map",*/ "γ")]
    #[rr::args("(#self,γ)", "#cap_to_merge" , /*"#global_map"*/)]
    //#[rr::exists("x")]
    //#[rr::ensures("ref_to_loc x cap_to_merge")]
    #[rr::observe("γ": "(match self !! (fst cap_to_merge) with
                        | Some #y => <[(fst cap_to_merge) := #(fst cap_to_merge , (Z.lor (snd cap_to_merge) (snd y)))]> self
                        | _ => <[(fst cap_to_merge) := #cap_to_merge ]> self
                        end)
    ")]

    fn try_merge_cap(&mut self, cap_to_merge: &Cap , /*global_map : &GlobalMap*/) {
        let mut obj_ptr = cap_to_merge.obj as *const Obj;
        // if there already exists cap points to the same obj as `cap_to_merge`, their rights will be merged
        // otherwise, new entry will be created

        let prev_cap = self.caps.get_mut(&obj_ptr);
        let issome = prev_cap.is_some(); 
        if issome {
            // If it exists, merge the rights
            let tempright1 = cap_to_merge.rights;
            let mutcap = prev_cap.unwrap();

            let tempright2 = mutcap.rights;
            let tempright3 = tempright1 | tempright2;
            mutcap.rights = tempright3;

            //prev_cap.unwrap().rights |= cap_to_merge.rights;
        } else {
            // If it doesn't exist, insert the new cap
            self.caps.insert(obj_ptr, cap_to_merge.clone());
        }
    }

    #[rr::params("self","to_grant","γ","cap_to_grant")]
    #[rr::args("#self","(#to_grant,γ)","#cap_to_grant")]
    #[rr::exists("x")]
    #[rr::observe("γ":"match self !! x with
                            |Some #y => match (Z.land y.2 2) with
                                            | 0  => to_grant  
                                            | _  => match to_grant !! (fst cap_to_grant)  with
                                                        | Some #z => <[(fst cap_to_grant) := #(fst cap_to_grant , (Z.lor (snd cap_to_grant) (snd z) ))  ]> to_grant                                                                            
                                                        |  _      => <[(fst cap_to_grant) := #cap_to_grant ]> to_grant                     
                                                        end
                                            end             
                            |_ => to_grant
                            end
                    ")]
    #[rr::ensures("ref_to_loc x to_grant")]
    pub fn grant(&self, to_grant: &mut Obj, cap_to_grant: &Cap) {
        if self.try_take_action(to_grant, GRANT).is_some() {
            to_grant.try_merge_cap(cap_to_grant)            
                                                            
        }
    }

    #[rr::params("self","γ1","to_delete","γ2","right1")]
    #[rr::args("(#self,γ1)","(#to_delete,γ2)","right1")]
    #[rr::exists("x":"loc", "γ'")]
    #[rr::observe("γ1":"match self !! x with   
                            | Some #y => match (Z.land (snd y) 16) with 
                                        | 0 => self  
                                        | _ => <[x := PlaceGhost γ' ]> self
                                        end             
                            | _ => self  
                            end"
                        )]
    #[rr::observe("γ2":"to_delete")]
    #[rr::ensures( #iris "match self !! x with   
                        | Some #y =>  match (Z.land (snd y) 16) with 
                                      | 0 =>  True
                                      | _ => gvar_pobs γ' match (Z.land (snd y) right1) with
                                                          | 0 =>  y
                                                          | _ => ((fst y) , Z.lxor (snd y) right1)
                                                          end
                                      end             
                        | _ => True
                    end"
                )]
    #[rr::ensures("ref_to_loc x to_delete")]
    pub fn delete(&mut self, to_delete: &mut Obj, right: usize) {
        let cap_on_to_delete = self.try_take_action_mut(to_delete, DELETE); //返回Option<&mut Cap>或者None或者None
        if cap_on_to_delete.is_some(){ 
            let cap_unwrap = cap_on_to_delete.unwrap(); //cap_unwrap是&mut Cap类型
            if cap_unwrap.contains(right) {
                cap_unwrap.rights ^= right;
            }
        }
    }

/*
    #[rr::params("self", "γ")]
    #[rr::args("(#self,γ)")]
    #[rr::exists("x": "loc" , "new_obj")]
    #[rr::observe("γ":"(match self !! x with
                        | Some #y => <[x := #(x ,Z.lor( Z.lor (Z.lor (Z.lor (Z.lor (Z.lor 1 2) 4) 8) 16) (snd y)))]> self
                        | _ => <[x := #(x,Z.lor (Z.lor (Z.lor (Z.lor 1 2) 4) 8) 16)) ]> self
                        end)
    ")]
    #[rr::returns("# new_obj")]
    #[rr::ensures("ref_to_loc x new_obj")]
*/
    pub fn create(&mut self) -> Rc<RefCell<Obj>> {
        let new_obj = Rc::new(RefCell::new(Self::new()));
        let obj_ptr = {
            let obj_ref: &mut Obj = &mut new_obj.borrow_mut();
            obj_ref as *mut Obj
        };
        let new_cap = Cap {
            obj: obj_ptr,
            rights: Self::turn_on_all_rights(),
            cdt: Cdt,
        };
        self.try_merge_cap(&new_cap);
        new_obj
    }


    fn turn_on_all_rights() -> usize {
        TAKE | GRANT | CREATE | DELETE
    } 
}


#[allow(non_snake_case)]
#[cfg(test)]
mod tests {
    use crate::Obj;


    #[test]
    fn create_and_grant() {
        let mut root = Obj::new();
        let A = root.create();
        let B = A.borrow_mut().create();
        let C = A.borrow_mut().create();

        {
            let A_ref = A.borrow();
            let a_cap_on_c = A_ref.get_cap_on(&mut C.borrow_mut()).unwrap();
            A.borrow().grant(&mut B.borrow_mut(), a_cap_on_c);
            println!("A grants C to B -> {:?}", B);
        }

        {
            let D = B.borrow_mut().create();
            let b_ref = B.borrow();
            let b_cap_on_d = b_ref.get_cap_on(&mut D.borrow_mut()).unwrap();
            A.borrow_mut().take(&D.borrow(), b_cap_on_d);
            println!("A takes D from B -> {:?}", A);
            assert_eq!(A.borrow().caps.len(), 2);
        }

    }
}

