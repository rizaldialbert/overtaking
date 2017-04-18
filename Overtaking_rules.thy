theory Overtaking_rules
imports 
  Main Overtaking_Aux Environment_Executable "./safe_distance/Safe_Distance_Isar"
begin   
    
section "Trace"    
\<comment> \<open>Represent the state of a (dynamic) road user as a record.\<close>

datatype vehicle = Pedestrian | Cyclist | Motorised

record raw_state = rectangle +   (* position is represented as the centre of the rectangle *)
  velocity     :: "real2"        (* velocity vector     *)
  acceleration :: "real2"        (* acceleration vector *)
    
\<comment> \<open>predicate to check whether a number is the supremum in a dimension.\<close>  
definition is_sup :: "(real2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real2 set \<Rightarrow> bool" where
  "is_sup sel r occ \<equiv> (\<forall>p \<in> occ. sel p \<le> r)"  
  
definition is_sup_x :: "real \<Rightarrow> real2 set \<Rightarrow> bool" where
  "is_sup_x \<equiv> is_sup fst"

definition is_sup_y :: "real \<Rightarrow> real2 set \<Rightarrow> bool" where
  "is_sup_y \<equiv> is_sup snd"
  
type_synonym runs = "vehicle \<times> raw_state list"    
type_synonym black_boxes = "runs \<times> runs list"    
  
subsection "Example of runs"
  
definition rectangle_ex :: "rectangle" where
  "rectangle_ex \<equiv> \<lparr>  Xcoord = 0.0,  Ycoord = 0.0,  Orient = 0.0, Length = 5.0,  Width = 1.5\<rparr>"
  
definition raw_state_ex :: "raw_state" where
  "raw_state_ex \<equiv> rectangle.extend rectangle_ex \<lparr>velocity = (10,10), acceleration = (5,5)\<rparr>"  

lemma "rectangle.truncate raw_state_ex = rectangle_ex"
  unfolding raw_state_ex_def rectangle_ex_def rectangle.truncate_def rectangle.extend_def
  by auto
      
section "LTL with finite trace"  
  
subsection "Syntax"                

datatype (atoms_fin: 'a) ltlf = 
    True_ltlf                             ("true\<^sub>f")
  | False_ltlf                            ("false\<^sub>f")
  | Prop_ltlf 'a                          ("prop\<^sub>f'(_')")
  | Not_ltlf "'a ltlf"                    ("not\<^sub>f _" [85] 85)
  | And_ltlf "'a ltlf" "'a ltlf"          ("_ and\<^sub>f _" [82,82] 81)
  | Or_ltlf "'a ltlf" "'a ltlf"           ("_ or\<^sub>f _" [81,81] 80)
  | Implies_ltlf "'a ltlf" "'a ltlf"      ("_ implies\<^sub>f _" [81,81] 80)
  | Next_ltlf "'a ltlf"                   ("X\<^sub>f _" [88] 87) 
  | Final_ltlf "'a ltlf"                  ("F\<^sub>f _" [88] 87)
  | Global_ltlf "'a ltlf"                 ("G\<^sub>f _" [88] 87)
  | Until_ltlf "'a ltlf" "'a ltlf"        ("_ U\<^sub>f _" [84,84] 83)
  | Release_ltlf "'a ltlf" "'a ltlf"      ("_ V\<^sub>f _" [83,83] 82)
    

definition Iff_ltlf ("_ iff\<^sub>f _" [81,81] 80)
where
  "\<phi> iff\<^sub>f \<psi> \<equiv> (\<phi> implies\<^sub>f \<psi>) and\<^sub>f (\<psi> implies\<^sub>f \<phi>)"     
    
subsection "Semantics"    
                                     
definition suffix_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"  
  where "suffix_list k xs \<equiv> drop k xs"
    
primrec semantics_ltlf :: "['a set list, 'a ltlf] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>f _" [80,80] 80)
where                           
  "\<xi> \<Turnstile>\<^sub>f true\<^sub>f = True"    
| "\<xi> \<Turnstile>\<^sub>f false\<^sub>f = False"                         
| "\<xi> \<Turnstile>\<^sub>f prop\<^sub>f(q) = (q \<in> (\<xi> ! 0))"               
| "\<xi> \<Turnstile>\<^sub>f not\<^sub>f \<phi> = (\<not> \<xi> \<Turnstile>\<^sub>f \<phi>)"      
| "\<xi> \<Turnstile>\<^sub>f \<phi> and\<^sub>f \<psi> = (\<xi> \<Turnstile>\<^sub>f \<phi> \<and> \<xi> \<Turnstile>\<^sub>f \<psi>)"
| "\<xi> \<Turnstile>\<^sub>f \<phi> or\<^sub>f \<psi> = (\<xi> \<Turnstile>\<^sub>f \<phi> \<or> \<xi> \<Turnstile>\<^sub>f \<psi>)"
| "\<xi> \<Turnstile>\<^sub>f \<phi> implies\<^sub>f \<psi> = (\<xi> \<Turnstile>\<^sub>f \<phi> \<longrightarrow> \<xi> \<Turnstile>\<^sub>f \<psi>)"
| "\<xi> \<Turnstile>\<^sub>f X\<^sub>f \<phi> = (suffix_list 1 \<xi> \<Turnstile>\<^sub>f \<phi>)"                    
| "\<xi> \<Turnstile>\<^sub>f F\<^sub>f \<phi> = (\<exists>i. i < length \<xi> \<and> suffix_list i \<xi> \<Turnstile>\<^sub>f \<phi>)"
| "\<xi> \<Turnstile>\<^sub>f G\<^sub>f \<phi> = (\<forall>i. i < length \<xi> \<longrightarrow> suffix_list i \<xi> \<Turnstile>\<^sub>f \<phi>)"
| "\<xi> \<Turnstile>\<^sub>f \<phi> U\<^sub>f \<psi> = (\<exists>i. i < length \<xi> \<and> suffix_list i \<xi> \<Turnstile>\<^sub>f \<psi> \<and> (\<forall>j<i. suffix_list j \<xi> \<Turnstile>\<^sub>f \<phi>))"
| "\<xi> \<Turnstile>\<^sub>f \<phi> V\<^sub>f \<psi> = (\<forall>i. i < length \<xi> \<longrightarrow> suffix_list i \<xi> \<Turnstile>\<^sub>f \<psi> \<or> (\<exists>j<i. suffix_list j \<xi> \<Turnstile>\<^sub>f \<phi>))"
  
lemma semantics_ltlc_sugar [simp]:
  "\<xi> \<Turnstile>\<^sub>f \<phi> iff\<^sub>f \<psi> = (\<xi> \<Turnstile>\<^sub>f \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>f \<psi>)"
  "\<xi> \<Turnstile>\<^sub>f F\<^sub>f \<phi> = \<xi> \<Turnstile>\<^sub>f (true\<^sub>f U\<^sub>f \<phi>)"  
  "\<xi> \<Turnstile>\<^sub>f G\<^sub>f \<phi> = \<xi> \<Turnstile>\<^sub>f (false\<^sub>f V\<^sub>f \<phi>)"  
  by (auto simp add: Iff_ltlf_def)
  
lemma ltl_true_or_con[simp]:
  "\<xi> \<Turnstile>\<^sub>f prop\<^sub>f(p) or\<^sub>f (not\<^sub>f prop\<^sub>f(p)) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>f true\<^sub>f"
  by auto
    
lemma ltl_false_true_con[simp]:
  "\<xi> \<Turnstile>\<^sub>f not\<^sub>f true\<^sub>f \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>f false\<^sub>f"
  by auto
    
lemma ltl_Next_Neg_con[simp]:
  "\<xi> \<Turnstile>\<^sub>f X\<^sub>f (not\<^sub>f \<phi>) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>f not\<^sub>f X\<^sub>f \<phi>"
  by auto  
    
lemma ltl_Release_Until_con:
 "\<xi> \<Turnstile>\<^sub>f \<phi> V\<^sub>f \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile>\<^sub>f (not\<^sub>f \<phi>) U\<^sub>f (not\<^sub>f \<psi>))"
  by auto
    
section "Representing overtaking traffic rules in LTL with finite trace"
  
  
\<comment>\<open>traffic rules atoms\<close>
datatype tr_atom = overtaking_atom  | on_fastlane_atom  | sd_rear_atom  |  sd_front_atom  | 
                   surpassing_atom  | safe_side_atom  |  larger_safe_side_atom  | motorised_atom  | 
                   safe_to_return_atom  |  merging_atom  | original_lane_atom 
                                                            
\<comment> \<open>abbreviations for meaningful names\<close>                              
abbreviation overtaking :: "tr_atom ltlf" where "overtaking \<equiv> prop\<^sub>f(overtaking_atom)"                               
abbreviation on_fastlane :: "tr_atom ltlf" where "on_fastlane \<equiv> prop\<^sub>f(on_fastlane_atom)"                               
abbreviation sd_rear :: "tr_atom ltlf" where "sd_rear \<equiv> prop\<^sub>f(sd_rear_atom)"                               
abbreviation sd_front :: "tr_atom ltlf" where "sd_front \<equiv> prop\<^sub>f(sd_front_atom)"                               
abbreviation surpassing :: "tr_atom ltlf" where "surpassing \<equiv> prop\<^sub>f(surpassing_atom)"                               
abbreviation safe_side :: "tr_atom ltlf" where "safe_side \<equiv> prop\<^sub>f(safe_side_atom)"                               
abbreviation larger_safe_side :: "tr_atom ltlf" where "larger_safe_side \<equiv> prop\<^sub>f(larger_safe_side_atom)"                               
abbreviation motorised :: "tr_atom ltlf" where "motorised \<equiv> prop\<^sub>f(motorised_atom)"                               
abbreviation safe_to_return :: "tr_atom ltlf" where "safe_to_return \<equiv> prop\<^sub>f(safe_to_return_atom)"
abbreviation merging :: "tr_atom ltlf" where "merging \<equiv> prop\<^sub>f(merging_atom)"                               
abbreviation original_lane :: "tr_atom ltlf" where "original_lane \<equiv> prop\<^sub>f(original_lane_atom)"
                                     
subsection "Formalised Traffic Rules in LTL interpreted over finite trace"
  
definition \<Phi>1 :: "tr_atom ltlf" where
  "\<Phi>1 \<equiv> G\<^sub>f (overtaking and\<^sub>f on_fastlane implies\<^sub>f sd_front and\<^sub>f sd_rear)"

definition \<Phi>2 :: "tr_atom ltlf" where
  "\<Phi>2 \<equiv> G\<^sub>f (overtaking and\<^sub>f (surpassing and\<^sub>f motorised) implies\<^sub>f safe_side)"
  
definition \<Phi>2' :: "tr_atom ltlf" where
  "\<Phi>2' \<equiv> G\<^sub>f (overtaking and\<^sub>f (surpassing and\<^sub>f not\<^sub>f motorised) implies\<^sub>f larger_safe_side)"
  
definition \<Phi>3 :: "tr_atom ltlf" where
  "\<Phi>3 \<equiv> G\<^sub>f (overtaking and\<^sub>f (on_fastlane and\<^sub>f merging) implies\<^sub>f safe_to_return)"
                            
definition \<Phi>4 :: "tr_atom ltlf" where
  "\<Phi>4 \<equiv> G\<^sub>f (overtaking and\<^sub>f original_lane implies\<^sub>f sd_rear)"
         
subsection "Checker for atomic propositions"
  
type_synonym lane_type = "((real \<times> real) \<times> real \<times> real) list list"  
  
fun bb_to_rects :: "black_boxes \<Rightarrow> rectangle list" where
  "bb_to_rects bb = (let ego_run = fst bb; ego_raw_trace = snd ego_run in
                                          map rectangle.truncate ego_raw_trace)"  
    
definition rects_to_words :: "(rectangle list \<Rightarrow> bool list) \<Rightarrow> tr_atom \<Rightarrow> rectangle list \<Rightarrow> tr_atom set list" 
  where
  "rects_to_words f atom rects = map (\<lambda>x. if x then {atom} else {}) (f rects)"
    
definition overtaking_checker :: "black_boxes \<Rightarrow> lane_type \<Rightarrow> tr_atom set list" where
  "overtaking_checker bb env \<equiv> 
                  rects_to_words (\<lambda>x. lane.overtaking_trace env x) overtaking_atom (bb_to_rects bb)"  

definition onfastlane_checker :: "black_boxes \<Rightarrow> lane_type \<Rightarrow> tr_atom set list" where
  "onfastlane_checker bb env \<equiv> 
                  rects_to_words (\<lambda>x. lane.fast_lane_trace env x) on_fastlane_atom (bb_to_rects bb)"

definition merging_checker :: "black_boxes \<Rightarrow> lane_type \<Rightarrow> tr_atom set list" where
  "merging_checker bb env \<equiv> 
                        rects_to_words (\<lambda>x. lane.merging_trace env x) merging_atom (bb_to_rects bb)"  
  
definition original_lane_checker :: "black_boxes \<Rightarrow> lane_type \<Rightarrow> tr_atom set list" where
  "original_lane_checker bb env \<equiv> 
            rects_to_words (\<lambda>x. lane.original_lane_trace env x) original_lane_atom (bb_to_rects bb)"
  
  
    
    
end