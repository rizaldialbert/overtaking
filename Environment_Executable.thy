theory Environment_Executable
imports
  Main Physical_Trace Overtaking_Aux
  "$AFP/Affine_Arithmetic/Polygon"
begin

section "Lanelets"

definition points_path2 :: "(real2 \<times> real2) list \<Rightarrow> (real \<Rightarrow> real2) list" where
  "points_path2 points \<equiv> map (\<lambda>p. linepath (fst p) (snd p)) points"
    
fun curve_eq3 :: "(real \<Rightarrow> real2) list \<Rightarrow> real \<Rightarrow> real2" where
  "curve_eq3 [x] = x" | 
  "curve_eq3 (x # xs) = x +++ curve_eq3 xs"
    
theorem pathstart_curve_eq:
  "pathstart (curve_eq3 (x # xs)) = pathstart x"  
  by (metis (no_types, lifting) curve_eq3.elims list.discI list.sel(1) pathstart_join)    
      
theorem curve_eq_cont:
  fixes points :: "(real2 \<times> real2) list"
  assumes "points \<noteq> []"
  assumes "polychain points"
  assumes "points_path2 points = paths"    
  shows "continuous_on {0..1} (curve_eq3 paths)"
  using assms
proof (induction paths arbitrary:points rule:curve_eq3.induct)
  case (1 x)
  then show ?case unfolding points_path2_def 
    by (auto simp add:continuous_on_linepath)
next
  case (2 x v va)
  note case_two = this    
  from case_two(4) obtain x' v' va' where "points = x' # v' # va'" and
    "linepath (fst x') (snd x') = x" and "linepath (fst v') (snd v') = v"
    and 0: "points_path2 (v' # va') = v # va"
    unfolding points_path2_def
    by auto
  with case_two(3) have "polychain (v' # va')" by (simp add: polychain_Cons)  
  from case_two(1)[OF _ this 0] have 1:"continuous_on {0..1} (curve_eq3 (v # va))" by auto
  then show ?case unfolding curve_eq3.simps(2)
  proof (intro continuous_on_joinpaths)      
    from \<open>linepath (fst x') (snd x') = x\<close> show "continuous_on {0..1} x" 
      using continuous_on_linepath by auto
  next
    from 1 show "continuous_on {0..1} (curve_eq3 (v # va))" .
  next
    have 0: "pathstart (curve_eq3 (v # va)) = pathstart v" using pathstart_curve_eq by auto  
    from \<open>polychain points\<close> and \<open>points = x' # v' # va'\<close> have "snd x' = fst v'" 
      unfolding polychain_def by auto
    moreover have "pathfinish x = snd x'" using \<open>linepath (fst x') (snd x') = x\<close> 
      using pathfinish_linepath by auto
    moreover have "pathstart v = fst v'" using \<open>linepath (fst v') (snd v') = v\<close>        
      using pathstart_linepath by auto
    ultimately show "pathfinish x = pathstart (curve_eq3 (v # va))" using 0 by auto       
  qed
next
  case 3
  then show ?case unfolding points_path2_def by auto
qed    
  
subsection "Lanelet curve"  
            
locale lanelet_curve = 
  fixes points :: "(real2 \<times> real2) list" 
  assumes nonempty_points: "points \<noteq> []"  
  assumes poly_points: "polychain points"    
begin
abbreviation points_path :: "(real \<Rightarrow> real2) list" where
  "points_path \<equiv> points_path2 points"  
  
abbreviation curve_eq :: "real \<Rightarrow> real2" where
  "curve_eq \<equiv> curve_eq3 points_path"        

text 
  \<open>Proof that lanelent curve is a refinement of a curve. The proof is obtained via sublocale proof.\<close>       
  
interpretation lc: curve "curve_eq" "{0..1}" 
proof (unfold_locales)
  show "convex {(0::real)..1}" by auto
next      
  show "compact {(0::real)..1}" by auto        
next
  show "continuous_on {0..1} curve_eq"
    using curve_eq_cont[OF nonempty_points poly_points] by auto      
qed 
end
     
subsection "Lanelet's simple boundary"
  
definition "monotone_polychain xs \<longleftrightarrow>  
            polychain (xs :: (real2 \<times> real2) list) \<and> (\<forall>i < length xs. fst (fst (xs ! i)) < fst (snd (xs ! i)))"  
   
lemma monotone_polychain_ConsD:
  assumes "monotone_polychain (x # xs)"
  shows "monotone_polychain xs"
  using assms polychain_Cons[of "x" "xs"] unfolding monotone_polychain_def
  by (metis Suc_mono length_Cons nth_Cons_Suc polychain_Nil)
    
lemma monotone_polychainD:
  assumes "monotone_polychain xs"
  shows "polychain xs"
  using assms unfolding monotone_polychain_def by auto
          
lemma strict_mono_in_joinpaths:
  assumes "strict_mono_in f {0..1}"
  assumes "strict_mono_in g {0..1}"
  assumes "pathfinish f = pathstart g"  
  shows "strict_mono_in (f +++ g) {0..1}"
proof
  fix x y :: real
  assume xr: "x \<in> {0..1}"
  assume yr: "y \<in> {0..1}"
  assume "x < y"  
  consider "x \<le> 0.5 \<and> y \<le> 0.5"
         | "x \<le> 0.5 \<and> y > 0.5"
         | "x > 0.5 \<and> y \<le> 0.5"
         | "x > 0.5 \<and> y > 0.5" by fastforce  
  thus "(f +++ g) x < (f +++ g) y"
  proof (cases)
    case 1
    note case_one = this
    hence l: "(f +++ g) x = f (2 * x)" and r: "(f +++ g) y = f (2 * y)" unfolding joinpaths_def 
      by auto
    from \<open>x < y\<close> have "2 * x < 2 * y" by auto
    from case_one xr yr have "0 \<le> 2 * x \<and> 2 * x \<le> 1" and "0 \<le> 2 * y \<and> 2 * y \<le> 1" by auto
    with \<open>2 * x < 2 * y\<close> and assms(1) have "f (2 * x) < f (2 * y)" unfolding strict_mono_in_def 
      by auto        
    then show ?thesis using l r by auto
  next
    case 2
    note case_two = this
    hence l:"(f +++ g) x = f (2 * x)" and r: "(f +++ g) y = g (2 * y - 1)"
      unfolding joinpaths_def by auto
    from assms(1) have "mono_in f {0..1}" using strict_mono_in_mono_in by auto        
    from case_two have "0 \<le> 2 * x \<and> 2 * x \<le> 1" using xr and yr by auto
    with \<open>mono_in f {0..1}\<close> have "f (2 * x) \<le> f 1" unfolding mono_in_def by auto          
    also have "... = g 0" using assms(3) unfolding pathfinish_def pathstart_def by auto
    finally have "f (2 * x) \<le> g 0" by auto
    from case_two have "0 < 2 * y - 1 \<and> 2 * y - 1 \<le> 1" using xr and yr by auto
    with assms(2) have "g 0 < g (2 * y - 1)" unfolding strict_mono_in_def by auto
    with \<open>f (2 * x) \<le> g 0\<close> have "f (2 * x) < g (2 * y - 1)" by auto        
    then show ?thesis using l and r by auto
  next
    case 3
    with \<open>x < y\<close> have "False" by auto  
    then show ?thesis by auto
  next
    case 4
    note case_four = this
    hence l: "(f +++ g) x = g (2 * x - 1)" and r: "(f +++ g) y = g (2 * y - 1)" unfolding joinpaths_def
      by auto
    from \<open>x < y\<close> have "2 * x < 2 * y" by auto
    from case_four xr yr have "0 \<le> 2 * x - 1 \<and> 2 * x - 1 \<le> 1" and "0 \<le> 2 * y - 1 \<and> 2 * y - 1 \<le> 1"
      by auto
    with \<open>2 * x < 2 * y\<close> and assms(2) have "g (2 * x - 1) < g (2 * y - 1)" 
      unfolding strict_mono_in_def  by auto    
    then show ?thesis using l r by auto
  qed    
qed
  
lemma mono_in_joinpaths:
  assumes "mono_in f {0..1}"
  assumes "mono_in g {0..1}"
  assumes "pathfinish f = pathstart g"  
  shows "mono_in (f +++ g) {0..1}"    
proof
  fix x y :: real
  assume xr: "x \<in> {0..1}"
  assume yr: "y \<in> {0..1}"
  assume "x \<le> y"  
  consider "x \<le> 0.5 \<and> y \<le> 0.5"
         | "x \<le> 0.5 \<and> y > 0.5"
         | "x > 0.5 \<and> y \<le> 0.5"
         | "x > 0.5 \<and> y > 0.5" by fastforce  
  thus "(f +++ g) x \<le> (f +++ g) y"
  proof (cases)
    case 1
    note case_one = this
    hence l: "(f +++ g) x = f (2 * x)" and r: "(f +++ g) y = f (2 * y)" unfolding joinpaths_def 
      by auto
    from \<open>x \<le> y\<close> have "2 * x \<le> 2 * y" by auto
    from case_one xr yr have "0 \<le> 2 * x \<and> 2 * x \<le> 1" and "0 \<le> 2 * y \<and> 2 * y \<le> 1" by auto
    with \<open>2 * x \<le> 2 * y\<close> and assms(1) have "f (2 * x) \<le> f (2 * y)" unfolding mono_in_def by auto        
    then show ?thesis using l r by auto
  next
    case 2
    note case_two = this
    hence l:"(f +++ g) x = f (2 * x)" and r: "(f +++ g) y = g (2 * y - 1)"
      unfolding joinpaths_def by auto
    from case_two have "0 \<le> 2 * x \<and> 2 * x \<le> 1" using xr and yr by auto
    with assms(1) have "f (2 * x) \<le> f 1" unfolding mono_in_def by auto
    also have "... = g 0" using assms(3) unfolding pathfinish_def pathstart_def by auto
    finally have "f (2 * x) \<le> g 0" by auto
    from case_two have "0 \<le> 2 * y - 1 \<and> 2 * y - 1 \<le> 1" using xr and yr by auto
    with assms(2) have "g 0 \<le> g (2 * y - 1)" unfolding mono_in_def by auto
    with \<open>f (2 * x) \<le> g 0\<close> have "f (2 * x) \<le> g (2 * y - 1)" by auto        
    then show ?thesis using l and r by auto
  next
    case 3
    with \<open>x \<le> y\<close> have "False" by auto  
    then show ?thesis by auto
  next
    case 4
    note case_four = this
    hence l: "(f +++ g) x = g (2 * x - 1)" and r: "(f +++ g) y = g (2 * y - 1)" unfolding joinpaths_def
      by auto
    from \<open>x \<le> y\<close> have "2 * x \<le> 2 * y" by auto
    from case_four xr yr have "0 \<le> 2 * x - 1 \<and> 2 * x - 1 \<le> 1" and "0 \<le> 2 * y - 1 \<and> 2 * y - 1 \<le> 1"
      by auto
    with \<open>2 * x \<le> 2 * y\<close> and assms(2) have "g (2 * x - 1) \<le> g (2 * y - 1)" unfolding mono_in_def 
      by auto    
    then show ?thesis using l r by auto
  qed    
qed
  
theorem strict_mono_in_curve_eq3:
  assumes "monotone_polychain points"
  assumes "points_path2 points = paths"
  assumes "points \<noteq> []"
  shows "strict_mono_in (fst \<circ> curve_eq3 paths) {0..1}"
  using assms
proof (induction paths arbitrary:points rule:curve_eq3.induct)
  case (1 x)
  note case_one = this
  then obtain x' where "points = [x']" and "linepath (fst x') (snd x') = x" 
    unfolding points_path2_def by auto
  with \<open>monotone_polychain points\<close> have 0: "fst (fst x') < fst (snd x')" unfolding monotone_polychain_def
    by auto
  from \<open>linepath (fst x') (snd x') = x\<close> have "x = (\<lambda>x. (1 - x) *\<^sub>R (fst x') + x *\<^sub>R (snd x'))"
    unfolding linepath_def by auto
  hence "fst \<circ> x = (\<lambda>x. (1 - x) * fst (fst x') + x * fst (snd x'))" by auto
  with 0 have "strict_mono_in (fst \<circ> x) {0..1}" unfolding strict_mono_in_def 
    by (smt left_diff_distrib' real_mult_le_cancel_iff2)
  then show ?case unfolding curve_eq3.simps .
next
  case (2 x v va)
  note case_two = this
  then obtain x' and v' and va' where "points = x' # v' # va'" and ppt: "points_path2 (v' # va') = v # va"
    and lpx: "linepath (fst x') (snd x') = x" and lpv: "linepath (fst v') (snd v') = v"
    unfolding points_path2_def by auto
  with \<open>monotone_polychain points\<close> have "monotone_polychain (v' # va')" 
    using monotone_polychain_ConsD by auto
  from case_two(1)[OF this ppt] have "strict_mono_in (fst \<circ> curve_eq3 (v # va)) {0..1}" by blast
  from \<open>monotone_polychain points\<close> and \<open>points = x' # v' # va'\<close> have 0: "fst (fst x') < fst (snd x')"
    unfolding monotone_polychain_def by auto
  from lpx have "x = (\<lambda>x. (1 - x) *\<^sub>R (fst x') + x *\<^sub>R (snd x'))" unfolding linepath_def by auto  
  hence "fst \<circ> x = (\<lambda>x. (1 - x) * fst (fst x') + x * fst (snd x'))" by auto
  with 0 have "strict_mono_in (fst \<circ> x) {0..1}" unfolding strict_mono_in_def 
    by (smt mult_diff_mult mult_strict_right_mono)   
  have "fst \<circ> curve_eq3 (x # v # va) = fst \<circ> (x +++ curve_eq3 (v # va))" by auto
  also have "... = (fst \<circ> x) +++ (fst \<circ> curve_eq3 (v # va))" by (simp add: path_compose_join)      
  finally have helper:"fst \<circ> curve_eq3 (x # v # va) = (fst \<circ> x) +++ (fst \<circ> curve_eq3 (v # va))" by auto
  have "strict_mono_in ((fst \<circ> x) +++ (fst \<circ> curve_eq3 (v # va))) {0..1}"
  proof (rule strict_mono_in_joinpaths)
    from \<open>strict_mono_in (fst \<circ> x) {0..1}\<close> show "strict_mono_in (fst \<circ> x) {0..1}" .   
  next
    from \<open>strict_mono_in (fst \<circ> curve_eq3 (v # va)) {0..1}\<close> 
      show "strict_mono_in (fst \<circ> curve_eq3 (v # va)) {0..1}" .
  next
    from \<open>monotone_polychain points\<close> have "polychain points" using monotone_polychainD by auto
    with \<open>points = x' # v' # va'\<close> have "snd x' = fst v'" unfolding polychain_def by auto
    hence 1: "fst (snd x') = fst (fst v')" by auto
    from lpx and lpv have "pathfinish x = snd x'" and "pathstart v = fst v'" by auto            
    with 1 show "pathfinish (fst \<circ> x) = pathstart (fst \<circ> curve_eq3 (v # va))" 
      by (simp add: pathfinish_compose pathstart_compose pathstart_curve_eq)
  qed        
  then show ?case using helper by auto
next
  case 3
  then show ?case unfolding points_path2_def by auto
qed
        
theorem mono_in_curve_eq3:
  assumes "monotone_polychain points"
  assumes "points_path2 points = paths"
  assumes "points \<noteq> []"
  shows "mono_in (fst \<circ> curve_eq3 paths) {0..1}"
  using assms
proof (induction paths arbitrary:points rule:curve_eq3.induct)
  case (1 x)
  note case_one = this
  then obtain x' where "points = [x']" and "linepath (fst x') (snd x') = x" 
    unfolding points_path2_def by auto
  with \<open>monotone_polychain points\<close> have 0: "fst (fst x') < fst (snd x')" unfolding monotone_polychain_def
    by auto
  from \<open>linepath (fst x') (snd x') = x\<close> have "x = (\<lambda>x. (1 - x) *\<^sub>R (fst x') + x *\<^sub>R (snd x'))"
    unfolding linepath_def by auto
  hence "fst \<circ> x = (\<lambda>x. (1 - x) * fst (fst x') + x * fst (snd x'))" by auto
  with 0 have "mono_in (fst \<circ> x) {0..1}" unfolding mono_in_def 
    by (smt left_diff_distrib' mult_left_mono)    
  then show ?case unfolding curve_eq3.simps .
next
  case (2 x v va)
  note case_two = this
  then obtain x' and v' and va' where "points = x' # v' # va'" and ppt: "points_path2 (v' # va') = v # va"
    and lpx: "linepath (fst x') (snd x') = x" and lpv: "linepath (fst v') (snd v') = v"
    unfolding points_path2_def by auto
  with \<open>monotone_polychain points\<close> have "monotone_polychain (v' # va')" 
    using monotone_polychain_ConsD by auto
  from case_two(1)[OF this ppt] have "mono_in (fst \<circ> curve_eq3 (v # va)) {0..1}" by blast
  from \<open>monotone_polychain points\<close> and \<open>points = x' # v' # va'\<close> have 0: "fst (fst x') < fst (snd x')"
    unfolding monotone_polychain_def by auto
  from lpx have "x = (\<lambda>x. (1 - x) *\<^sub>R (fst x') + x *\<^sub>R (snd x'))" unfolding linepath_def by auto  
  hence "fst \<circ> x = (\<lambda>x. (1 - x) * fst (fst x') + x * fst (snd x'))" by auto
  with 0 have "mono_in (fst \<circ> x) {0..1}" unfolding mono_in_def 
    by (smt left_diff_distrib' mult_left_mono)   
  have "fst \<circ> curve_eq3 (x # v # va) = fst \<circ> (x +++ curve_eq3 (v # va))" by auto
  also have "... = (fst \<circ> x) +++ (fst \<circ> curve_eq3 (v # va))" by (simp add: path_compose_join)      
  finally have helper:"fst \<circ> curve_eq3 (x # v # va) = (fst \<circ> x) +++ (fst \<circ> curve_eq3 (v # va))" by auto
  have "mono_in ((fst \<circ> x) +++ (fst \<circ> curve_eq3 (v # va))) {0..1}"
  proof (rule mono_in_joinpaths)
    from \<open>mono_in (fst \<circ> x) {0..1}\<close> show "mono_in (fst \<circ> x) {0..1}" .   
  next
    from \<open>mono_in (fst \<circ> curve_eq3 (v # va)) {0..1}\<close> show "mono_in (fst \<circ> curve_eq3 (v # va)) {0..1}" .
  next
    from \<open>monotone_polychain points\<close> have "polychain points" using monotone_polychainD by auto
    with \<open>points = x' # v' # va'\<close> have "snd x' = fst v'" unfolding polychain_def by auto
    hence 1: "fst (snd x') = fst (fst v')" by auto
    from lpx and lpv have "pathfinish x = snd x'" and "pathstart v = fst v'" by auto            
    with 1 show "pathfinish (fst \<circ> x) = pathstart (fst \<circ> curve_eq3 (v # va))" 
      by (simp add: pathfinish_compose pathstart_compose pathstart_curve_eq)
  qed        
  then show ?case using helper by auto
next
  case 3
  then show ?case unfolding points_path2_def by auto
qed    

lemma inj_scale_2:
  "inj_on (op * (2::real)) s"
  using injective_scaleR[of "2"] 
  by (simp add: inj_onI)
        
lemma inj_scale2_shift1: 
  "inj_on (op + (-1 :: real) \<circ> op * (2 :: real)) s"
  using inj_scale_2 comp_inj_on[of "op * (2::real)" _ "op + (-1::real)"]
  by (simp add: inj_onI)
        
theorem inj_on_curve_eq:
  assumes "monotone_polychain points"
  assumes "points_path2 points = paths"
  assumes "points \<noteq> []"
  assumes "curve_eq3 paths = curve_eq"
  shows "inj_on curve_eq {0..1}"
proof -
  from assms have "strict_mono_in (fst \<circ> curve_eq3 paths) {0..1}" using strict_mono_in_curve_eq3
    by auto
  hence "inj_on (fst \<circ> curve_eq) {0..1}" using strict_imp_inj_on assms by auto    
  thus ?thesis  using inj_on_imageI2 by blast    
qed
        
locale lanelet_simple_boundary = lanelet_curve +
  assumes monotone: "monotone_polychain xs"  
begin
  
lemma curve_eq_is_curve: 
  "curve curve_eq {0..1}"
proof (unfold_locales)
  show "convex {(0::real)..1}" by auto
next      
  show "compact {(0::real)..1}" by auto        
next
  show "continuous_on {0..1} curve_eq"
    using curve_eq_cont[OF nonempty_points poly_points] by auto
qed  
  
interpretation lsc: simple_boundary "curve_eq" "{0..1}"
proof (unfold_locales)
  show "convex {(0::real)..1}" by auto
next      
  show "compact {(0::real)..1}" by auto        
next
  show "continuous_on {0..1} curve_eq"
    using curve_eq_cont[OF nonempty_points poly_points] by auto  
next
  show "inj_on curve_eq {0..1}"
    using inj_on_curve_eq[OF monotone _ nonempty_points] by auto 
next
  have eq:"curve.curve_eq_x curve_eq = (fst \<circ> curve_eq)" 
    unfolding curve.curve_eq_x_def[OF curve_eq_is_curve] by auto    
  show "bij_betw (curve.curve_eq_x curve_eq) {0..1} (curve.setX curve_eq {0..1})"
    unfolding bij_betw_def
  proof 
    from strict_mono_in_curve_eq3[OF monotone _ nonempty_points]
      have "strict_mono_in (fst \<circ> curve_eq) {0..1}" by auto
    hence "inj_on (fst \<circ> curve_eq) {0..1}" using strict_imp_inj_on by auto
    with eq show "inj_on (curve.curve_eq_x curve_eq) {0..1}" by auto
  next
    show "curve.curve_eq_x curve_eq ` {0..1} = curve.setX curve_eq {0..1}"
      unfolding eq curve.setX_def[OF curve_eq_is_curve] by auto
  qed    
qed  
end

(* text "This function simply finds the first segment which intersect with vertical lines x."  
  
fun find_segment :: "(real2 \<times> real2)list \<Rightarrow> real \<Rightarrow> (real2 \<times> real2) option" where
  "find_segment [] x = None" | 
  "find_segment (p # ps) x = (if fst (fst p) \<le> x \<and> x \<le> fst (snd p) then Some p else find_segment ps x)"  

definition solve_x :: "real2 \<Rightarrow> real2 \<Rightarrow> real \<Rightarrow> real" where
  "solve_x p1 p2 x \<equiv> (snd p2 - snd p1) / (fst p2 - fst p1) * (x - fst p1) + snd p1"  
  
definition find_intersection :: "(real2 \<times> real2) list \<Rightarrow> real \<Rightarrow> real option" where
  "find_intersection ps x \<equiv> (case find_segment ps x of 
                               None \<Rightarrow> None 
                             | Some segment \<Rightarrow> Some (solve_x (fst segment) (snd segment) x))"  

definition above_initially :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> bool" where
  "above_initially polychain1 polychain2 \<equiv> (let leftmost1_x = fst (fst (hd polychain1)); 
                                                leftmost2_x = fst (fst (hd polychain2)) 
                                            in 
                                              if leftmost1_x \<le> leftmost2_x then 
                                                 (case find_intersection polychain1 leftmost2_x of
                                                    None \<Rightarrow> ))"   *)
  
locale lanelet = le: lanelet_simple_boundary points_le + ri: lanelet_simple_boundary points_ri
  for points_le and points_ri +
  assumes above: "snd (fst (hd points_le)) > snd (fst (hd points_ri))"
  assumes non_intersecting: "\<forall>t \<in> {0..1}. le.curve_eq t \<noteq> ri.curve_eq t"
begin  

    
interpretation lsr: simple_road "le.curve_eq" "ri.curve_eq" "{0..1}"
proof (unfold_locales)


qed
  
  
    
end
  
    
end