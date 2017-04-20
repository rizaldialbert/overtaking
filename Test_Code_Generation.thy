theory Test_Code_Generation
imports
  Environment_Executable
begin                                                        

section "Code generation for segment intersection"  

type_synonym segment = "(real*real)*real*real"
definition segment1::segment where
  "segment1 = ((0.0,0.0), (5.0,0.0))"
definition segment2::segment where
  "segment2 = ((0.0,0.0), (5.0,1.0))"
definition "reoi x = (real_of_int (int_of_integer x))"
definition "raoi i j = reoi i / reoi j"
    
ML \<open>
val segment_intersection = @{code segment_intersection}
val segment1 = @{code segment1}
val segment2 = @{code segment2}
val reoi = @{code reoi}
val raoi = @{code raoi}
fun mk_segment a b c d = ((reoi a, reoi b), (reoi c, reoi d))
val segment3 = mk_segment 0 1 2 3
\<close>
ML \<open>segment_intersection segment1 segment2\<close>
ML \<open>segment_intersection segment1 segment3\<close>

section "Code generation for point in drivable area"
  
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
  using points_le_def by (unfold_locales) (auto simp add:pple mple)
    
definition points_ri :: "segment list" where
  "points_ri = [((0,1), (1,1)), ((1,1), (2,1)), ((2,1), (3,1))]"    
  
theorem ppri: "polychain points_ri" unfolding points_ri_def by eval  
theorem mpri: "monotone_polychain points_ri" unfolding points_ri_def by eval
    
global_interpretation rlsb: lanelet_simple_boundary points_ri
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
  defines right = l.direction_right and pida = l.point_in_drivable_area
  by (unfold_locales) (eval+) 
    
value [code] "right"    
value [code] "pida (1,0.5)"
  
term "rotation_matrix'"  
    
  
end