theory Test_Code_Generation_Real_Approx
imports
  Environment_Executable
  "~~/src/HOL/Library/Code_Real_Approx_By_Float"
begin                                                          

type_synonym segment = "(real*real)*real*real"

text \<open>TODO: missing in \<open>Code_Real_Approx_By_Float\<close> or is there some deeper reason?
  Perhaps Florians recent (March/April 2017) changes to codegen?\<close>

lemmas
  real_less_eq_code[code del]
  real_less_code[code del]

text \<open>TODO: adapt \<open>Code_Real_Approx_By_Float\<close> and its @{const \<open>Realfract\<close>}
    to the "new" \<open>Code_Target_Int\<close> setup using @{typ integer}\<close>

definition Realfract :: "integer \<Rightarrow> integer \<Rightarrow> real"
  where "Realfract p q = real_of_integer p / real_of_integer q"

lemma [code]: "Ratreal r = (case (quotient_of r) of (x, y) \<Rightarrow>
  Realfract (integer_of_int x) (integer_of_int y))"
  by (cases r)
     (simp add: Realfract_def quotient_of_Fract of_rat_rat
       real_of_integer_def)

ML \<open>val segment_intersection = @{code segment_intersection}\<close>
ML \<open>
val segment1 = ((0.0,0.0), (5.0,0.0));
val segment2 = ((0.0,0.0), (5.0,1.0));
\<close>
ML \<open>segment_intersection segment1 segment2\<close>
  
fun polychain2 :: "('a \<times> 'a) list \<Rightarrow> bool" where
  "polychain2 [] = True" | 
  "polychain2 [x] = True" | 
  "polychain2 (x # y # zs) = (if snd x = fst y then polychain2 (y # zs) else False)"

theorem univ_unfold_at_0:
  assumes "1 < m" 
  shows "(\<forall>i::nat. Suc i < m \<longrightarrow> P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i::nat. 1 \<le> i \<and> Suc i < m \<longrightarrow> P i))"  
proof 
  assume 0: "\<forall>i. Suc i < m \<longrightarrow> P i"
  with assms have c1: "P 0" by auto
  with assms 0 have c2: "(\<forall>i::nat. 1 \<le> i \<and> Suc i < m \<longrightarrow> P i)" by auto      
  with c1 show " P 0 \<and> (\<forall>i. 1 \<le> i \<and> Suc i < m \<longrightarrow> P i)" by auto
next
  show "P 0 \<and> (\<forall>i. 1 \<le> i \<and> Suc i < m \<longrightarrow> P i) \<Longrightarrow> \<forall>i. Suc i < m \<longrightarrow> P i" using assms 
      by (metis One_nat_def le_add2 le_add_same_cancel2 le_eq_less_or_eq le_simps(3))
qed

lemma polychain_polychain2[code]: 
  "polychain xs = polychain2 xs"
proof (induction xs rule:polychain2.induct)
  case 1
  then show ?case by auto
next
  case (2 x)
  then show ?case by auto
next
  case (3 x y zs)  
  note case3 = this  
  have "1 < length (x # y # zs)" by auto  
  have "polychain (x # y # zs) = (snd ((x # y # zs) ! 0) = fst ((x # y # zs) ! Suc 0) \<and> 
                                 (\<forall>i. 1 \<le> i \<and> Suc i < length (x # y # zs) \<longrightarrow> snd ((x # y # zs) ! i) = fst ((x # y # zs) ! Suc i)))"
    unfolding polychain_def univ_unfold_at_0[OF `1 < length (x # y # zs)`, where P="\<lambda>i. snd ((x # y # zs) ! i) = (fst ((x # y # zs) ! Suc i))"]
    by auto
  also have "... = (snd x = fst y \<and> polychain (y # zs))" unfolding polychain_def by auto
  finally have "polychain (x # y # zs) = (snd x = fst y \<and> polychain (y # zs))" by auto
  with case3 show ?case  by auto  
qed
  
definition points_le :: "segment list" where
  "points_le = [((0,0), (1,0)), ((1,0), (2,0)), ((2,0), (3,0))]"
    
theorem pple: "polychain points_le" unfolding points_le_def by eval
      
theorem univ_unfold_at_0':
  assumes "0 < m"
  shows "(\<forall>i::nat. i < m \<longrightarrow> P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i::nat. 1 \<le> i \<and> i < m \<longrightarrow> P i))"    
proof     
  assume 0: "\<forall>i<m. P i"
  with assms have "P 0" by auto
  from 0 have "(\<forall>i::nat. 1 \<le> i \<and> i < m \<longrightarrow> P i)" by auto
  with `P 0` show "P 0 \<and> (\<forall>i. 1 \<le> i \<and> i < m \<longrightarrow> P i)" by auto
next
  assume " P 0 \<and> (\<forall>i. 1 \<le> i \<and> i < m \<longrightarrow> P i)"
  with assms show "\<forall>i<m. P i" 
    by (metis less_one not_less)  
qed
  
fun monotone_polychain2 :: "((real \<times> real) \<times> real \<times> real) list \<Rightarrow> bool" where
  "monotone_polychain2 [] = True" | 
  "monotone_polychain2 (x # xs) = (if fst (fst x) < fst (snd x) then monotone_polychain2 xs else False)"

lemma monotone_polychain2:
  "(\<forall>i<length xs. fst (fst (xs ! i)) < fst (snd (xs ! i))) = monotone_polychain2 xs"  
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  note case_cons = this
  have "0 < length (a # xs)" by auto  
  have "(\<forall>i<length (a # xs). fst (fst ((a # xs) ! i)) < fst (snd ((a # xs) ! i))) = 
    (fst (fst a) < fst (snd a) \<and> (\<forall>i < length xs. fst (fst (xs ! i)) < fst (snd (xs ! i))))"
    unfolding univ_unfold_at_0'[OF `0 < length (a #xs)`, where P="\<lambda>x. fst (fst ((a # xs) ! x)) < fst (snd ((a # xs) ! x))"]
    by auto
  with case_cons show ?case by auto 
qed

lemma monotone_polychain_monotone_polychain2 [code]:  
  "monotone_polychain xs = (polychain2 xs \<and> monotone_polychain2 xs)"    
  unfolding monotone_polychain_def polychain_polychain2 monotone_polychain2 by auto

theorem mple: "monotone_polychain points_le" unfolding points_le_def by eval  

global_interpretation llsb: lanelet_simple_boundary points_le
  defines left_rectangle_intersect = llsb.rectangle_intersect
  using points_le_def by (unfold_locales) (auto simp add:pple mple)
    
definition points_ri :: "segment list" where
  "points_ri = [((0,1), (1,1)), ((1,1), (2,1)), ((2,1), (3,1))]"    
  
theorem ppri: "polychain points_ri" unfolding points_ri_def by eval  
theorem mpri: "monotone_polychain points_ri" unfolding points_ri_def by eval
    
global_interpretation rlsb: lanelet_simple_boundary points_ri
  defines right_rectangle_intersect = rlsb.rectangle_intersect
  using points_ri_def by (unfold_locales) (auto simp add:ppri mpri)
    
theorem pathstart_boundary [code]:
  "pathstart_boundary [x] = fst x"
  "pathstart_boundary (x # y # zs) = fst x"
  unfolding pathstart_boundary_def points_path2_def by auto  
    
theorem pathfinish_boundary [code]:
  "pathfinish_boundary [x] = snd x"
  "pathfinish_boundary (x # y # zs) = pathfinish_boundary (y # zs)"
  unfolding pathfinish_boundary_def points_path2_def by auto
        
theorem "pathfinish_boundary points_ri = (3,1)" by eval  
    
value [code] "above_and_inside_polychains points_le (3,1)"    
 
global_interpretation l: lanelet points_ri points_le
  defines right = l.direction_right and pida = l.point_in_drivable_area and 
          vertices_inside = l.vertices_inside and
          intersect_left_boundary = l.intersect_left_boundary and
          intersect_right_boundary = l.intersect_right_boundary and
          intersect_boundaris = l.intersect_boundaries and
          lines_inside = l.lines_inside and rect_inside = l.rectangle_inside
  by (unfold_locales) (eval+) 
    
value [code] "right"    
value [code] "pida (1,0.5)"
  
term "rotation_matrix'" 
           
term "rotate_rect"

definition rectangle_test :: "rectangle" where
  "rectangle_test \<equiv> \<lparr>Xcoord = 0.0, Ycoord = 0.0, Orient = 0.0, Length = 3.0, Width = 1.5\<rparr>"

ML \<open>
val get_vertices = @{code get_vertices}  
val rectangle_test = @{code rectangle_test}
val vertices = get_vertices rectangle_test
\<close>  
  
value [code] "rect_inside rectangle_test"  
value [code] "right_rectangle_intersect rectangle_test"  
value [code] "left_rectangle_intersect rectangle_test"  
  
  
definition bound0 where "bound0 = points_le"
definition bound1 where "bound1 = points_ri"
definition bound2 :: "segment list" where
  "bound2 = [((0,2), (1,2)), ((1,2), (2,2)), ((2,2), (3,2))]"
definition bound3 :: "segment list" where
  "bound3 = [((0,3), (1,3)), ((1,3), (2,3)), ((2,3), (3,3))]"
  
definition boundaries where "boundaries = [bound0, bound1, bound2]"  

theorem lb: "lane boundaries" unfolding lane_def by eval
        
global_interpretation l2': lane2' bound0 bound1 bound2
  defines lane_detection = l2'.Lane.lane_detection and 
  in_lane = l2'.in_lane2  and 
  in_lane' = l2'.Lane.in_lane and 
  lines_inside0 = l2'.lane0.lines_inside and
  lines_inside1 = l2'.lane1.lines_inside and
  intersect_boundaries0 = l2'.lane0.intersect_boundaries and
  intersect_boundaries1 = l2'.lane1.intersect_boundaries and
  intersect_right_boundary0 = l2'.lane0.intersect_right_boundary and
  intersect_right_boundary1 = l2'.lane1.intersect_right_boundary and  
  intersect_left_boundary0 = l2'.lane0.intersect_left_boundary and 
  intersect_left_boundary1 = l2'.lane1.intersect_left_boundary and   
  rectangle_inside0 = l2'.lane0.rectangle_inside and
  rectangle_inside1 = l2'.lane1.rectangle_inside and
  lane_boundaries_touched = l2'.Lane.lane_boundaries_touched and
  point_in_drivable_area0 = l2'.lane0.point_in_drivable_area and
  point_in_drivable_area1 = l2'.lane1.point_in_drivable_area and
  direction_right0 = l2'.lane0.direction_right and
  direction_right1 = l2'.lane1.direction_right and
  rectangle_intersect0 = l2'.bound0.rectangle_intersect and 
  rectangle_intersect1 = l2'.bound1.rectangle_intersect and 
  rectangle_intersect2 = l2'.bound2.rectangle_intersect and 
  vertices_inside0 = l2'.lane0.vertices_inside and
  lane_boundaries_touched2 = l2'.lane_boundaries_touched2 and
  vertices_inside1 = l2'.lane1.vertices_inside and 
  initial_lane = l2'.Lane.initial_lane and 
  start_inc_lane = l2'.Lane.start_inc_lane and 
  finish_inc_lane = l2'.Lane.finish_inc_lane and
  increase_lane = l2'.Lane.increase_lane and 
  decrease_lane = l2'.Lane.decrease_lane and
  start_dec_lane = l2'.Lane.start_dec_lane and
  finish_dec_lane = l2'.Lane.finish_dec_lane and 
  overtaking = l2'.Lane.overtaking and 
  time_points_to_ov_bools = l2'.Lane.time_points_to_ov_bools and
  time_points_to_fl_bools = l2'.Lane.time_points_to_fl_bools and
  time_points_to_merge_bools = l2'.Lane.time_points_to_merge_bools and 
  time_points_to_ori_bools = l2'.Lane.time_points_to_ori_bools
  by (unfold_locales) (eval+)  

lemma [code]: "start_dec_lane uu i num =
  (case i of
    0 \<Rightarrow> None
  | Suc v \<Rightarrow>
    case uu of
     [] \<Rightarrow> None
  | (rect # rects) \<Rightarrow> 
    (case lane_detection rect of Outside \<Rightarrow> None
     | Lane n \<Rightarrow>
         if n = Suc v then start_dec_lane rects n (num + 1) else None
     | Boundaries ns \<Rightarrow>
         if tl ns = [] \<and> hd ns = Suc v then Some (num, rects)
         else None))"
  by (auto split: nat.splits list.splits)

lemma [code]: "finish_dec_lane uu i num =
  (case i of
    0 \<Rightarrow> None
  | Suc v \<Rightarrow>
    case uu of
      [] \<Rightarrow> None
   | (rect # rects) \<Rightarrow>
  (case lane_detection rect of Outside \<Rightarrow> None
   | Lane n \<Rightarrow> if n = Suc v - 1 then Some (num, rects) else None
   | Boundaries ns \<Rightarrow>
       if tl ns = [] \<and> hd ns = Suc v
       then finish_dec_lane rects (Suc v) (num + 1) else None))"
  by (auto split: nat.splits list.splits)

value [code] "decrease_lane"
     
end