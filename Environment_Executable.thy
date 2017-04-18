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

theorem curve_eq_cons:
  "ps \<noteq> [] \<Longrightarrow> curve_eq3 (points_path2 (p # ps)) = (linepath (fst p) (snd p)) +++ curve_eq3 (points_path2 ps)"
  "ps = [] \<Longrightarrow> curve_eq3 (points_path2 (p # ps)) = linepath (fst p) (snd p)" 
proof -
  assume "ps \<noteq> []"
  then have "points_path2 ps \<noteq> []" using points_path2_def by auto
  moreover have "points_path2 (p # ps) = (linepath (fst p) (snd p)) # points_path2 ps" using points_path2_def by auto
  ultimately show "curve_eq3 (points_path2 (p # ps)) = (linepath (fst p) (snd p)) +++ curve_eq3 (points_path2 ps)" using hd_Cons_tl by force
next
  assume "ps = []"
  then show "curve_eq3 (points_path2 (p # ps)) = linepath (fst p) (snd p)" unfolding points_path2_def by auto
qed
  
theorem pathstart_curve_eq:
  "pathstart (curve_eq3 (x # xs)) = pathstart x"  
  by (metis (no_types, lifting) curve_eq3.elims list.discI list.sel(1) pathstart_join)

theorem pathfinish_curve_eq:
  assumes "xs \<noteq> []"
  shows "pathfinish (curve_eq3 xs) = pathfinish (last xs)"
  using assms
proof (induction xs rule:curve_eq3.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 x v va)
  note case_two = this
  have "pathfinish (curve_eq3 (x # v # va)) = pathfinish (curve_eq3 (v # va))"
    by auto
  moreover have "pathfinish (last (x # v # va)) = pathfinish (last (v # va))"
    by auto
  ultimately show ?case using case_two by auto      
next
  case 3
  then show ?case by auto
qed
      
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
  
subsection "Lanelet's curve"  
            
locale lanelet_curve = 
  fixes points :: "(real2 \<times> real2) list" 
  assumes nonempty_points: "points \<noteq> []"  
  assumes poly_points: "polychain points"    
begin
  
abbreviation points_path :: "(real \<Rightarrow> real2) list" where
  "points_path \<equiv> points_path2 points"  
  
abbreviation curve_eq :: "real \<Rightarrow> real2" where
  "curve_eq \<equiv> curve_eq3 points_path" 

lemma curve_eq_imp_linepath': "points \<noteq> [] \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> 
  \<exists>i < length points. \<exists>t' \<in> {0..1}. curve_eq t = linepath (fst (points ! i)) (snd (points ! i)) t'" 
proof (induction points arbitrary: t)
  case (Cons p ps)
  {
    assume "ps = []"
    then have "curve_eq3 (points_path2 (p # ps)) t = linepath (fst ((p # ps) ! 0)) (snd ((p # ps) ! 0)) t" 
      using curve_eq_cons by auto
    then have ?case using Cons by blast
  }
  moreover {
    assume "ps \<noteq> []"
    {
      assume "t \<le> 1/2"
      then have "curve_eq3 (points_path2 (p # ps)) t = linepath (fst ((p # ps) ! 0)) (snd ((p # ps) ! 0)) (2*t)"
        using `ps \<noteq> []` curve_eq_cons unfolding joinpaths_def by auto
      moreover have "2*t \<in> {0..1}" using `t \<le> 1/2` Cons by auto
      ultimately have ?case by blast
    }
    moreover {
      assume "\<not>t \<le> 1/2"
      then have "2 * t - 1 \<in> {0..1}" using Cons by auto 
      then obtain i t' where "i < length ps" "t' \<in> {0..1}" 
               "curve_eq3 (points_path2 ps) (2 * t - 1) = linepath (fst (ps ! i)) (snd (ps ! i)) t'"
        using Cons `ps \<noteq> []` by blast
      moreover have "curve_eq3 (points_path2 (p # ps)) t = curve_eq3 (points_path2 ps) (2 * t - 1)"
        using  `\<not>t \<le> 1/2` `ps \<noteq> []` curve_eq_cons points_path2_def unfolding joinpaths_def by auto
      ultimately have ?case by fastforce
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by blast
qed auto
  
lemma linepath_imp_curve_eq': "polychain points \<Longrightarrow> points \<noteq> [] \<Longrightarrow> i < length points \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> 
  \<exists>t' \<in> {0..1}. curve_eq3 (points_path2 points) t' = linepath (fst (points ! i)) (snd (points ! i)) t"
proof (induction i arbitrary: points)
  case 0
  then obtain p ps where *: "points = p # ps" using nonempty_points hd_Cons_tl by metis
  {
    assume "ps = []"
    then have "curve_eq3 (points_path2 points) t = linepath (fst p) (snd p) t" using * curve_eq_cons 
      by auto
    then have ?case using * 0 by auto
  }
  moreover {
    assume "ps \<noteq> []"
    moreover have "t/2 \<le> 1/2" using 0 by auto
    ultimately have "curve_eq3 (points_path2 (p # ps)) (t/2) = linepath (fst p) (snd p) t" 
      using curve_eq_cons unfolding joinpaths_def by auto
    then have ?case using * 0 by auto
  }
  ultimately show ?case by auto
next
  case (Suc i)
  then obtain p ps where *: "points = p # ps" using nonempty_points hd_Cons_tl by metis
  then have "ps \<noteq> []" using Suc by auto
      
  have "i < length ps" using * Suc by auto
  moreover have "polychain ps" using * polychain_Cons[of p] Suc `ps \<noteq> []` by auto
  ultimately obtain t' where t': "t' \<in> {0..1}" 
    "curve_eq3 (points_path2 ps) t' = linepath (fst (ps ! i)) (snd (ps ! i)) t" using Suc `ps \<noteq> []`   
    by blast
      
  {
    assume "(t'+1)/2 > 1/2"
    then have "curve_eq3 (points_path2 points) ((t'+1)/2) = curve_eq3 (points_path2 ps) (2 * ((t' + 1) / 2) - 1)" 
      using `ps \<noteq> []` * curve_eq_cons unfolding joinpaths_def by auto
    also have "\<dots> = curve_eq3 (points_path2 ps) t'" by argo
    finally have ?case using * t' by auto
  }
  moreover {
    assume "\<not>(t'+1)/2 > 1/2"
    then have "(t'+1)/2 = 1/2" using `t' \<in> {0..1}` by auto
    then have "curve_eq3 (points_path2 points) ((t'+1)/2) = pathfinish (linepath (fst p) (snd p))" 
      using `ps \<noteq> []` * curve_eq_cons unfolding joinpaths_def pathfinish_def by auto
    also have "\<dots> = fst (hd ps)" using polychain_Cons[of p ps] `ps \<noteq> []` Suc * hd_conv_nth[of ps] by auto
    also have "\<dots> = pathstart (linepath (fst (hd ps)) (snd (hd ps)))" by auto
    also have "\<dots> = curve_eq3 (points_path2 ps) 0" unfolding joinpaths_def pathstart_def using `ps\<noteq>[]` 
      by (metis (no_types, lifting) hd_Cons_tl list.simps(9) pathstart_curve_eq pathstart_def points_path2_def)
    finally have ?case using * t' `(t'+1)/2 = 1/2` by auto
  }
  ultimately show ?case by auto
qed
  
theorem curve_eq_imp_linepath: 
  "t \<in> {0..1} \<Longrightarrow> 
   \<exists>i < length points. \<exists>t' \<in> {0..1}. curve_eq t = linepath (fst (points ! i)) (snd (points ! i)) t'"
  using curve_eq_imp_linepath' nonempty_points by auto

theorem linepath_imp_curve_eq: 
  "i < length points \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> 
  \<exists>t' \<in> {0..1}. curve_eq3 (points_path2 points) t' = linepath (fst (points ! i)) (snd (points ! i)) t"
  using linepath_imp_curve_eq' nonempty_points poly_points by auto

abbreviation first_chain :: "real2 \<times> real2" where
  "first_chain \<equiv> hd points"  
  
abbreviation first_point :: "real2" where
  "first_point \<equiv> fst first_chain"  
  
abbreviation last_chain :: "real2 \<times> real2" where
  "last_chain \<equiv> last points"

abbreviation last_point :: "real2" where
  "last_point \<equiv> snd last_chain" 

theorem curve_eq0: "curve_eq 0 = first_point"
proof -
  have "curve_eq 0 = pathstart curve_eq" unfolding pathstart_def by auto
  also have "\<dots> = pathstart (curve_eq3 (map (\<lambda>p. linepath (fst p) (snd p)) points))"  unfolding points_path2_def by auto
  also have "\<dots> = pathstart (curve_eq3 (linepath (fst (hd points)) (snd (hd points)) # (map (\<lambda>p. linepath (fst p) (snd p)) (tl points))))"
  using nonempty_points hd_Cons_tl[of points] list.map(2)[of "(\<lambda>p. linepath (fst p) (snd p))" "hd points" "tl points"] by auto
  also have "\<dots> = pathstart (linepath (fst (hd points)) (snd (hd points)))" using pathstart_curve_eq by auto
  also have "\<dots> =  fst (hd points)" using pathstart_linepath by auto
  finally show ?thesis .
qed

text
  \<open>Proof that lanelet curve has a vector derivative from right at first point\<close>
  
theorem curve_eq_has_vector_derivative:
  shows "tl points = [] \<Longrightarrow> (curve_eq has_vector_derivative (snd (hd points) - fst (hd points))) (at_right (Inf {0..1}))"
    and "tl points \<noteq> [] \<Longrightarrow> (curve_eq has_vector_derivative 2 *\<^sub>R (snd (hd points) - fst (hd points))) (at_right (Inf {0..1}))"
proof -
  assume *: "tl points = []"
  have "(curve_eq has_vector_derivative (snd (hd points) - fst (hd points))) (at 0 within {0..})"
  proof (rule has_vector_derivative_transform_within[where f="linepath (fst (hd points)) (snd (hd points))"])
    show "(linepath (fst (hd points)) (snd (hd points)) has_vector_derivative (snd (hd points) - fst (hd points))) (at 0 within {0..})"
      using has_vector_derivative_linepath_within by auto
  next
    show "0 < (0.5::real)" by auto
  next
    show "(0::real) \<in> {0..}" by auto
  next
    fix x'
    assume "x' \<in> {0::real..}"
    assume "dist x' 0 < (0.5::real)"
    hence "x' \<in> {0..0.5}"  using \<open>x' \<in> {0..}\<close> by auto
    show "(linepath (fst (hd points)) (snd (hd points))) x' = curve_eq x'"
    proof -
      have "curve_eq = curve_eq3 (points_path2 (hd points # tl points))" using nonempty_points by auto
      also have "\<dots> = curve_eq3 (points_path2 ([hd points]))" using * by auto
      also have "\<dots> = linepath (fst (hd points)) (snd (hd points))"
        unfolding points_path2_def using curve_eq3.simps by auto
      finally show "(linepath (fst (hd points)) (snd (hd points))) x' = curve_eq x'" by auto
    qed
  qed
  moreover have "{0::real <..} \<subseteq> {0::real..}" by auto 
  ultimately show "(curve_eq has_vector_derivative (snd (hd points) - fst (hd points))) (at_right (Inf {0..1}))"
    unfolding has_vector_derivative_def using has_derivative_subset by auto
next
  assume *: "tl points \<noteq> []"
  have "(curve_eq has_vector_derivative 2 *\<^sub>R (snd (hd points) - fst (hd points))) (at 0 within {0..})"
  proof (rule has_vector_derivative_transform_within[where f="linepath (fst (hd points)) (snd (hd points)) \<circ> (\<lambda>x. 2 * x)"])
    show "(linepath (fst (hd points)) (snd (hd points)) \<circ> op * 2 has_vector_derivative 2 *\<^sub>R (snd (hd points) - fst (hd points))) (at 0 within {0..})"
    proof (intro vector_diff_chain_within)
      show "(op * 2 has_vector_derivative 2) (at 0 within {0..})" by (auto intro:derivative_eq_intros)
    next
      show "(linepath (fst (hd points)) (snd (hd points)) has_vector_derivative snd (hd points) - fst (hd points)) (at (2 * 0) within op * 2 ` {0..})"
        using has_vector_derivative_linepath_within by auto
    qed
  next
    show "0 < (0.5::real)" by auto
  next
    show "(0::real) \<in> {0..}" by auto
  next
    fix x'
    assume "x' \<in> {0::real..}"
    assume "dist x' 0 < (0.5::real)"
    hence "x' \<in> {0..0.5}"  using \<open>x' \<in> {0..}\<close> by auto
    show "(linepath (fst (hd points)) (snd (hd points)) \<circ> op * 2) x' = curve_eq x'" unfolding comp_def
    proof -
      have "curve_eq = curve_eq3 (points_path2 (hd points # tl points))" using nonempty_points by auto
      also have "... = linepath (fst (hd points)) (snd (hd points)) +++ curve_eq3 (points_path2 (tl points))"
        using * by (metis (no_types, lifting) curve_eq3.simps(2) list.exhaust_sel list.simps(9) points_path2_def)
      finally have "curve_eq = linepath (fst (hd points)) (snd (hd points)) +++ curve_eq3 (points_path2 (tl points))"
        by auto
      with \<open>x' \<in> {0..0.5}\<close> have "curve_eq x' = linepath (fst (hd points)) (snd (hd points)) (2 * x')"
        unfolding joinpaths_def by auto
      thus "linepath (fst (hd points)) (snd (hd points)) (2 * x') = curve_eq x'" by auto
    qed
  qed
  moreover have "{0::real <..} \<subseteq> {0::real..}" by auto 
  ultimately show "(curve_eq has_vector_derivative 2 *\<^sub>R (snd (hd points) - fst (hd points))) (at_right (Inf {0..1}))"
    unfolding has_vector_derivative_def using has_derivative_subset by auto
qed

text 
  \<open>Proof that lanelet curve is a refinement of a curve. The proof is obtained via sublocale proof.\<close>       
  
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
  
text \<open>One of the most important property for the polychain is monotonicity. This property is 
similar to the property that each curve equation in Physical_Trace.thy must be a graph. A graph 
here means that @{term "y"} is a function of @{term "x"}. This mean that a curve which looks like 
letter "S" cannot be a graph.\<close>
  
definition "monotone_polychain xs \<longleftrightarrow>  
            polychain (xs :: (real2 \<times> real2) list) \<and> (\<forall>i < length xs. fst (fst (xs ! i)) < fst (snd (xs ! i)))"  
   
lemma monotone_polychainI:
  fixes xs :: "(real2 \<times> real2) list"
  assumes "polychain xs"
  assumes "\<And>i. i < length xs \<Longrightarrow> fst (fst (xs ! i)) < fst (snd (xs ! i))"
  shows "monotone_polychain xs"
  using assms unfolding monotone_polychain_def by auto
    
lemma monotone_polychain_ConsD:
  assumes "monotone_polychain (x # xs)"
  shows "monotone_polychain xs"
  using assms polychain_Cons[of "x" "xs"] unfolding monotone_polychain_def
  by (metis Suc_mono length_Cons nth_Cons_Suc polychain_Nil)
    
lemma monotone_polychainD:
  assumes "monotone_polychain xs"
  shows "polychain xs"
  using assms unfolding monotone_polychain_def by auto
    
lemma monotone_polychain_fst_last:
  assumes "monotone_polychain (x # xs)"
  shows "fst (fst x) < fst (snd (last (x # xs)))"
  using assms
proof (induction xs arbitrary:x)
  case Nil
  then show ?case unfolding monotone_polychain_def by auto
next
  case (Cons a xs)
  note case_cons = this  
  hence "monotone_polychain (a # xs)" using monotone_polychain_ConsD by auto    
  with case_cons(1)[OF this] have *:"fst (fst a) < fst (snd (last (a # xs)))" by auto
  from case_cons have **: "fst (fst x) < fst (snd x)" unfolding monotone_polychain_def by auto
  from case_cons(2) have "snd x = fst a" unfolding monotone_polychain_def polychain_def
    by auto
  with * and ** show ?case by auto        
qed
            
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
      
theorem joinpaths_image_01:
  assumes "pathfinish f = pathstart g"
  shows "(f +++ g) ` {0 .. 1} = f ` {0 .. 1} \<union> g ` {0 .. 1}" 
proof (rule equalityI, rule_tac[!] subsetI)
  fix x
  assume "x \<in> (f +++ g) ` {0 .. 1}"
  then obtain t where "(f +++ g) t = x" and "t \<in> {0..1}" unfolding image_iff by auto
  consider "t \<le> 0.5" | "t > 0.5" by linarith      
  thus "x \<in> f ` {0..1} \<union> g ` {0..1}"    
  proof (cases)
    case 1
    note case_one = this
    hence "f (2 * t) = x" using \<open>(f +++ g) t = x\<close> unfolding joinpaths_def by auto  
    from case_one have "2 * t \<in> {0 .. 1}" using \<open>t \<in> {0 .. 1}\<close> by auto
    hence "x \<in> f ` {0 .. 1}" using \<open>f (2 * t) = x\<close> image_iff by auto        
    then show ?thesis by auto
  next
    case 2
    note case_two = this
    hence "g (2 * t - 1) = x" using \<open>(f +++ g) t = x\<close> unfolding joinpaths_def by auto
    from case_two have "2 * t - 1 \<in> {0 .. 1}" using \<open>t \<in> {0..1}\<close> by auto
    hence "x \<in> g ` {0 .. 1}" using \<open>g (2 * t - 1) = x\<close> image_iff by auto        
    then show ?thesis by auto
  qed    
next    
  fix x
  assume "x \<in> f ` {0..1} \<union> g ` {0..1}"
  hence "x \<in> f ` {0..1} \<or> x \<in> g ` {0..1}" by auto
  moreover    
  { assume "x \<in> f ` {0..1}"
    then obtain t where "f t = x" and "t \<in> {0 .. 1}" using image_iff by auto  
    hence "f (2 * (t / 2)) = x" and "t / 2 \<le> 0.5" and "t / 2 \<in> {0..1}" by auto                
    hence "x \<in> (f +++ g) ` {0..1}"  unfolding joinpaths_def image_iff 
      by (smt \<open>t \<in> {0..1}\<close> atLeastAtMost_iff divide_right_mono) }
  moreover
  { assume "x \<in> g ` {0..1}"
    then obtain t where "g t = x" and "t \<in> {0..1}" using image_iff by auto
    consider "t = 0" | "t \<noteq> 0" by auto
    hence "x \<in> (f +++ g) ` {0 .. 1}"
    proof (cases)
      case 1
      hence "g 0 = x" using \<open>g t = x\<close> by auto
      with assms have "f 1 = x" unfolding pathfinish_def pathstart_def by auto
      thus "x \<in> (f +++ g) `{0..1}" unfolding image_iff joinpaths_def
        by (auto intro: bexI[where x="0.5"])          
    next
      case 2 
      hence "t \<in> {0 <..1}" using \<open>t \<in> {0..1}\<close> by auto
      hence g_cond: "g (2 * ((t + 1)/ 2) - 1) = x" using \<open>g t = x\<close> by (auto simp add:divide_simps)
      from \<open>t \<in> {0<..1}\<close> have "(t + 1) / 2 > 0.5" and "(t + 1) / 2 \<in> {0..1}" by auto           
      thus ?thesis unfolding image_iff joinpaths_def using g_cond
        by (auto intro: bexI[where x="(t+1)/2"])          
    qed }
   ultimately show "x \<in> (f +++ g) ` {0..1}" by auto    
qed
              
theorem joinpaths_image_01':
  assumes "pathfinish f = pathstart g"
  shows "(f +++ g) ` {0 .. 1} = (f \<circ> (\<lambda>x. 2 * x)) ` {0 .. 0.5} \<union> (g \<circ> (\<lambda>x. 2 * x - 1)) ` {0.5 <.. 1}" 
proof (rule equalityI, rule_tac[!] subsetI)
  fix x
  assume "x \<in> (f +++ g) ` {0 .. 1}"
  then obtain t where "(f +++ g) t = x" and "t \<in> {0..1}" unfolding image_iff by auto
  consider "t \<le> 0.5" | "t > 0.5" by linarith      
  thus "x \<in> (f \<circ> (\<lambda>x. 2 * x)) ` {0..0.5} \<union> (g \<circ> (\<lambda>x. 2 * x - 1)) ` {0.5<..1}"    
  proof (cases)
    case 1
    note case_one = this
    hence "f (2 * t) = x" using \<open>(f +++ g) t = x\<close> unfolding joinpaths_def by auto  
    from case_one have "2 * t \<in> {0 .. 1}" using \<open>t \<in> {0 .. 1}\<close> by auto
    hence "x \<in> f ` {0 .. 1}" using \<open>f (2 * t) = x\<close> image_iff by auto        
    then show ?thesis 
      by (metis (no_types, lifting) "1" UnI1 \<open>f (2 * t) = x\<close> \<open>t \<in> {0..1}\<close> atLeastAtMost_iff image_comp image_iff)
  next
    case 2
    note case_two = this
    hence "g (2 * t - 1) = x" using \<open>(f +++ g) t = x\<close> unfolding joinpaths_def by auto
    from case_two have "2 * t - 1 \<in> {0 <.. 1}" using \<open>t \<in> {0..1}\<close> by auto
    hence 0: "x \<in> g ` {0 <.. 1}" using \<open>g (2 * t - 1) = x\<close> image_iff by auto
    have "(\<lambda>x. 2 * x - (1 ::real)) ` {0.5 <..1} = {0 <..1}" 
    proof -
      have *: "(\<lambda>x. 2 * x - (1::real)) = (\<lambda>x. x - 1) \<circ> (op * 2)" unfolding comp_def by auto          
      have "inj (op * (2::real))" unfolding inj_mult_left by auto
      from image_set_diff[OF this] 
      have "(op * (2::real)) ` ({0.5 ..1} - {0.5}) = (op * 2) ` {0.5 .. 1} - (op * 2) ` {0.5}"
        by auto
      hence 0: "(op * (2::real)) ` {0.5 <..1} = (op * 2) ` {0.5 .. 1} - (op * 2) ` {0.5}"
        by fastforce
      have "(op * (2::real)) ` {0.5 .. 1} = {1 .. 2}" using scaleR_image_atLeastAtMost 
        by auto
      moreover have "(op * 2) ` {0.5} = {1::real}" by auto
      ultimately have **: "(op * (2::real)) ` {0.5 <..1} = {1 <..2}" using 0 by fastforce 
      
      have "inj (\<lambda>x. x - (1::real))"  by (intro injI) (auto)
      from image_set_diff[OF this]
      have "(\<lambda>x. x - (1::real)) ` ({1 ..2} - {1}) = (\<lambda>x. x - (1::real)) ` {1 .. 2} - (\<lambda>x. x - (1::real)) ` {1}"
        by auto
      hence 1: "(\<lambda>x. x - (1::real)) ` {1 <..2} = (\<lambda>x. x - (1::real)) ` {1 .. 2} - (\<lambda>x. x - (1::real)) ` {1}"
        by fastforce
      have "(\<lambda>x. x - (1::real)) ` {1 .. 2} = {0 .. 1}" using image_add_atLeastAtMost[where k="-1"]
        by (auto simp add:algebra_simps)
      moreover have "(\<lambda>x. x - (1::real)) ` {1} = {0}" by auto
      ultimately have "(\<lambda>x. x - (1::real)) ` {1 <..2} = {0 <.. 1}" using 1 by auto 
      thus ?thesis unfolding * using ** unfolding sym[OF image_comp] by auto        
    qed      
    with 0 have "x \<in> (g \<circ> (\<lambda>x. 2 * x - 1)) ` {0.5 <..1}" unfolding sym[OF image_comp] by blast          
    thus ?thesis by auto       
  qed    
next    
  fix x
  assume "x \<in> (f \<circ> op * 2) ` {0..0.5} \<union> (g \<circ> (\<lambda>x. 2 * x - 1)) ` {0.5<..1}"
  hence "x \<in> (f \<circ> op * 2) ` {0..0.5} \<or> x \<in> (g \<circ> (\<lambda>x. 2 * x - 1)) ` {0.5<..1}" by auto
  moreover    
  { assume "x \<in> (f \<circ> op * 2) ` {0..0.5}"
    then obtain t where "f (2 * t) = x" and "t \<le> 0.5" and "t \<in> {0 .. 1}" 
      using image_iff unfolding comp_def by auto
    hence "x \<in> (f +++ g) ` {0..1}"  unfolding joinpaths_def image_iff by auto }
  moreover
  { assume "x \<in> (g \<circ> (\<lambda>x. 2 * x - 1)) ` {0.5<..1}"
    then obtain t where "g t = x" and "t \<in> {0..1}" using image_iff by auto
    consider "t = 0" | "t \<noteq> 0" by auto
    hence "x \<in> (f +++ g) ` {0 .. 1}"
    proof (cases)
      case 1
      hence "g 0 = x" using \<open>g t = x\<close> by auto
      with assms have "f 1 = x" unfolding pathfinish_def pathstart_def by auto
      thus "x \<in> (f +++ g) `{0..1}" unfolding image_iff joinpaths_def
        by (auto intro: bexI[where x="0.5"])          
    next
      case 2 
      hence "t \<in> {0 <..1}" using \<open>t \<in> {0..1}\<close> by auto
      hence g_cond: "g (2 * ((t + 1)/ 2) - 1) = x" using \<open>g t = x\<close> by (auto simp add:divide_simps)
      from \<open>t \<in> {0<..1}\<close> have "(t + 1) / 2 > 0.5" and "(t + 1) / 2 \<in> {0..1}" by auto           
      thus ?thesis unfolding image_iff joinpaths_def using g_cond
        by (auto intro: bexI[where x="(t+1)/2"])          
    qed }
   ultimately show "x \<in> (f +++ g) ` {0..1}" by auto    
qed
  
lemma
  fixes a b c :: "real2"
  assumes "\<exists>t \<in> {0..1}. linepath a b t = c"  
  assumes "fst a < fst b"    
  shows "fst a \<le> fst c \<and> fst c \<le> fst b"    
proof -
  from assms obtain t where "linepath a b t = c" and "t \<in> {0..1}" by auto  
  hence eq: "fst c = (1 - t) * fst a + t * fst b" and "0 \<le> t" and "t \<le> 1" unfolding linepath_def by auto
  have *: "\<forall>t1 \<in> {0..1}. \<forall>t2 \<in> {0..1}. t1 \<le> t2 \<longrightarrow> (1 - t1) * fst a + t1 * fst b \<le> (1 - t2) * fst a + t2 * fst b"
    using assms(2) by (smt mult_diff_mult real_mult_less_iff1)      
  with bspec[OF this, of "0"] have "\<forall>t2 \<in> {0..1}. fst a \<le> (1 - t2) * fst a + t2 * fst b"
    by auto    
  with eq have le: "fst a \<le> fst c" using \<open>t \<in> {0..1}\<close> by auto
  from * have "\<forall>t2 \<in> {0..1}. \<forall>t1 \<in> {0..1}. t1 \<le> t2 \<longrightarrow> (1 - t1) * fst a + t1 * fst b \<le> (1 - t2) * fst a + t2 * fst b"    
    by auto 
  with bspec[OF this, of "1"] have "\<forall>t \<in> {0..1}. (1 - t) * fst a + t * fst b \<le> fst b"
    by auto
  with eq have ri: "fst c \<le> fst b" using \<open>t \<in> {0..1}\<close> by auto
  from le and ri show ?thesis by auto      
qed
  
lemma h1:
  assumes "curve (curve_eq3 (points_path2 (a # pts))) {0..1}" 
  assumes "pts \<noteq> []"  
  assumes "polychain (a # pts)"    
  shows "curve(curve_eq3 (points_path2 pts)) {0..1}"
proof (unfold_locales)  
  show "convex {0::real..1}" by auto
next
  show "compact {0::real..1}" by auto
next      
  from assms have 0: "continuous_on {0..1} (curve_eq3 (points_path2 (a # pts)))"
    unfolding curve_def by auto
  have *: "points_path2 (a # pts) = linepath (fst a) (snd a) # points_path2 pts"
    unfolding points_path2_def by auto
  obtain a' pts' where "pts = a' # pts'" using assms(2) using list.exhaust_sel by blast
  with assms(3) have "snd a = fst a'" unfolding polychain_def by auto            
  have eq: "pathfinish (linepath (fst a) (snd a)) = pathstart (curve_eq3 (points_path2 pts))"
  proof -
    have lhs: "pathfinish (linepath (fst a) (snd a)) = snd a" by auto    
    have "curve_eq3 (points_path2 pts) = curve_eq3 (points_path2 (a' # pts'))" using `pts = a' # pts'` by auto
    also have "... = curve_eq3 (linepath (fst a') (snd a') # points_path2 pts')" 
      unfolding points_path2_def by auto
    finally have "curve_eq3 (points_path2 pts) = curve_eq3 (linepath (fst a') (snd a') # points_path2 pts')"    
      by auto        
    with pathstart_curve_eq have "pathstart (curve_eq3 (points_path2 pts)) = pathstart (linepath (fst a') (snd a'))"
      by auto
    also have "... = fst a'" by auto            
    finally have "pathstart (curve_eq3 (points_path2 pts)) = fst a'" by auto       
    with lhs and `snd a = fst a'` show ?thesis by auto
  qed        
  from `pts = a' # pts'` have "points_path2 pts = linepath (fst a') (snd a') # points_path2 pts'" 
    unfolding points_path2_def by auto
  with *have "curve_eq3 (points_path2 (a # pts)) = linepath (fst a) (snd a) +++ (curve_eq3 (points_path2 pts))"
    by auto
  with 0 have "continuous_on {0..1} (linepath (fst a) (snd a) +++ (curve_eq3 (points_path2 pts)))"
    by auto
  with continuous_on_joinpaths_D2[OF this eq] show "continuous_on {0..1} (curve_eq3 (points_path2 pts))"    
    by auto 
qed  
 
lemma pathfinish_pathstart:
  assumes "polychain (a # pts)"
  assumes "pts \<noteq> []"   
  shows "pathfinish (linepath (fst a) (snd a)) = pathstart (curve_eq3 (points_path2 pts))"  
proof -
  from assms(2) obtain a' pts' where "pts = a' # pts'" 
    using list.exhaust_sel by blast
  with assms(1) have 0: "snd a = fst a'" unfolding polychain_def by auto
  have 1: "pathfinish (linepath (fst a) (snd a)) = snd a" by auto
  have "pathstart (curve_eq3 (points_path2 pts)) = fst a'" unfolding `pts = a' # pts'`
    using curve_eq_cons by(cases "pts' = []") (auto)     
  with 0 and 1 show ?thesis by auto             
qed
  
lemma curve_eq3_image_01:
  assumes "curve (curve_eq3 (points_path2 (a # pts))) {0..1}"
  assumes "pts \<noteq> []"
  assumes "polychain (a # pts)"
  shows "curve_eq3 (points_path2 (a # pts)) ` {0..1} = 
                          linepath (fst a) (snd a) ` {0..1} \<union> curve_eq3 (points_path2 pts) ` {0..1}"  
proof -
  have eq: "pathfinish (linepath (fst a) (snd a)) = pathstart (curve_eq3 (points_path2 pts))" 
    using pathfinish_pathstart[OF assms(3) assms(2)] .
  from assms(1-3) have "curve (curve_eq3 (points_path2 (pts))) {0..1}"
    using h1[OF assms(1-3)] by auto
  from curve.setX_def[OF this] 
  have 1: "curve.setX (curve_eq3 (points_path2 pts)) {0..1} \<equiv> 
                                           fst ` curve_eq3 (points_path2 pts) ` {0..1}"
    by auto
  from curve.setX_def[OF assms(1)]
  have 2: "curve.setX (curve_eq3 (points_path2 (a # pts))) {0..1} \<equiv> 
                                      fst ` curve_eq3 (points_path2 (a # pts)) ` {0..1}"
    by auto
  have *: "points_path2 (a # pts) = linepath (fst a) (snd a) # points_path2 pts" 
    unfolding points_path2_def by auto   
  from `pts \<noteq> []` have "points_path2 pts \<noteq> []" unfolding points_path2_def by auto      
  with * have "curve_eq3 (points_path2 (a # pts)) = linepath (fst a) (snd a) +++ curve_eq3 (points_path2 pts)"
    (is "?lhs = ?rhs")
    using assms(2) curve_eq_cons(1) by blast
  hence "?lhs ` {0..1} = ?rhs ` {0..1}" by auto
  also have "... = linepath (fst a) (snd a) ` {0..1} \<union> curve_eq3 (points_path2 pts) ` {0..1}"    
    using joinpaths_image_01[OF eq] by auto  
  finally show "?lhs ` {0..1} = linepath (fst a) (snd a) ` {0..1} \<union> curve_eq3 (points_path2 pts) ` {0..1}"
    by auto    
qed
    

lemma h2:
  assumes "curve (curve_eq3 (points_path2 (a # pts))) {0..1}"
  assumes "pts \<noteq> []"  
  assumes "polychain (a # pts)" 
  assumes "x \<in> curve.setX (curve_eq3 (points_path2 pts)) {0..1}"  
  shows "x \<in> curve.setX (curve_eq3 (points_path2 (a # pts))) {0..1}" 
proof -
  from assms(1-3) have "curve (curve_eq3 (points_path2 (pts))) {0..1}"
    using h1[OF assms(1-3)] by auto
  from curve.setX_def[OF this] 
  have 1: "curve.setX (curve_eq3 (points_path2 pts)) {0..1} \<equiv> 
                                           fst ` curve_eq3 (points_path2 pts) ` {0..1}"
    by auto
  from curve.setX_def[OF assms(1)]
  have 2: "curve.setX (curve_eq3 (points_path2 (a # pts))) {0..1} \<equiv> 
                                      fst ` curve_eq3 (points_path2 (a # pts)) ` {0..1}"
    by auto
  have "curve_eq3 (points_path2 (a # pts)) ` {0..1}  = 
    linepath (fst a) (snd a) ` {0..1} \<union> curve_eq3 (points_path2 pts) ` {0..1}"
    using curve_eq3_image_01[OF assms(1-3)] by auto    
  hence "curve_eq3 (points_path2 pts) ` {0..1} \<subseteq> curve_eq3 (points_path2 (a # pts)) ` {0..1}" by auto
  hence "fst ` curve_eq3 (points_path2 pts) ` {0..1} \<subseteq> fst ` curve_eq3 (points_path2 (a # pts)) ` {0..1}" by auto
  hence "curve.setX (curve_eq3 (points_path2 pts)) {0..1} \<subseteq> curve.setX (curve_eq3 (points_path2 (a # pts))) {0..1}" 
    using 1 2 by auto
  with assms(4) show ?thesis by auto      
qed
  
lemma h2_hd:
  assumes "curve (curve_eq3 (points_path2 (a # pts))) {0..1}"
  assumes "pts \<noteq> []"  
  assumes "polychain (a # pts)" 
  assumes "x \<in> fst ` linepath (fst a) (snd a) ` {0..1}"  
  shows "x \<in> curve.setX (curve_eq3 (points_path2 (a # pts))) {0..1}" 
proof -
  from curve.setX_def[OF assms(1)]
  have 2: "curve.setX (curve_eq3 (points_path2 (a # pts))) {0..1} \<equiv> 
                                      fst ` curve_eq3 (points_path2 (a # pts)) ` {0..1}"
    by auto
  have "curve_eq3 (points_path2 (a # pts)) ` {0..1}  = 
    linepath (fst a) (snd a) ` {0..1} \<union> curve_eq3 (points_path2 pts) ` {0..1}"
    using curve_eq3_image_01[OF assms(1-3)] by auto 
  hence "linepath (fst a) (snd a) ` {0..1} \<subseteq> curve_eq3 (points_path2 (a # pts)) ` {0..1}"
    (is "?lhs \<subseteq> ?rhs")
    by auto  
  hence "fst ` ?lhs \<subseteq> fst ` ?rhs" by auto
  with assms(4) show ?thesis using 2 by auto            
qed
  
thm curve.setX_def  
  
lemma test2:
  assumes "points \<noteq> []"
  assumes "monotone_polychain points"  
  assumes "curve (curve_eq3 (points_path2 points)) {0..1}"    
  assumes "c \<in> set points"
  assumes "fst (fst c) \<le> x" and "x \<le> fst (snd c)"
  shows "x \<in> curve.setX (curve_eq3 (points_path2 (points))) {0..1}"
  using assms
proof (induction points)
  case Nil
  then show ?case by auto
next
  case (Cons a points)
  note case_cons = this  
  from `monotone_polychain (a # points)` have "fst (fst a) < fst (snd a)"
    unfolding monotone_polychain_def by auto
  from `monotone_polychain (a # points)` have "monotone_polychain points" using monotone_polychain_ConsD
    by auto
  from `monotone_polychain (a # points)` have "polychain (a # points)" unfolding monotone_polychain_def 
    by auto      
  obtain a' and points' where "points = [] \<or> points = a' # points'"  using list.exhaust_sel by blast
  moreover    
  { assume e: "points = []"  
    with case_cons have "c = a" by auto
    from case_cons have "fst (fst a) \<le> x" and "x \<le> fst (snd a)" unfolding `c = a` by auto
    have "linepath (fst a) (snd a) ` {0 .. 1} = closed_segment (fst a) (snd a)" using linepath_image_01
      by auto
    hence "fst ` (linepath (fst a) (snd a) ` {0 .. 1}) = fst ` (closed_segment (fst a) (snd a))"
      by auto
    also have "... = closed_segment (fst (fst a)) (fst (snd a))" by auto
    also have "... = {fst (fst a) .. fst (snd a)}" using `fst (fst a) < fst (snd a)` 
      using closed_segment_real by auto
    finally have "fst ` (linepath (fst a) (snd a) ` {0 .. 1}) = {fst (fst a) .. fst (snd a)}"
      by auto
    hence "x \<in> fst ` (linepath (fst a) (snd a) ` {0 .. 1})" using `fst (fst a) \<le> x` and `x \<le> fst (snd a)`
      by auto
    with case_cons have "x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}"
      by (simp add: curve.setX_def curve_eq_cons(2) e) }    
  
  moreover
  { assume ne: "points = a' # points'"
    with `c \<in> set (a # points)` have "c = a \<or> c \<in> set points" by auto
    moreover
    { assume "c \<in> set points"
      have curve_tail: "curve (curve_eq3 (points_path2 points)) {0..1}"
        using \<open>polychain (a # points)\<close> case_cons(4) h1 ne by blast 
      from case_cons(1) [OF _ `monotone_polychain points` curve_tail `c \<in> set points` assms(5-6)]
      have " x \<in> curve.setX (curve_eq3 (points_path2 points)) {0..1}"  unfolding ne by auto
      hence "x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}" 
        using \<open>points = [] \<Longrightarrow> x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}\<close> 
              \<open>polychain (a # points)\<close> case_cons(4) h2 by blast }
    moreover  
    { assume "c = a"
      from case_cons have "fst (fst a) \<le> x" and "x \<le> fst (snd a)" unfolding `c = a` by auto
      have "linepath (fst a) (snd a) ` {0 .. 1} = closed_segment (fst a) (snd a)" using linepath_image_01
        by auto
      hence "fst ` (linepath (fst a) (snd a) ` {0 .. 1}) = fst ` (closed_segment (fst a) (snd a))"
        by auto
      also have "... = closed_segment (fst (fst a)) (fst (snd a))" by auto
      also have "... = {fst (fst a) .. fst (snd a)}" using `fst (fst a) < fst (snd a)` 
        using closed_segment_real by auto
      finally have "fst ` (linepath (fst a) (snd a) ` {0 .. 1}) = {fst (fst a) .. fst (snd a)}"
        by auto
      hence "x \<in> fst ` (linepath (fst a) (snd a) ` {0 .. 1})" using `fst (fst a) \<le> x` and `x \<le> fst (snd a)`
        by auto
      with case_cons(2-7) have "x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}"
        using \<open>points = [] \<Longrightarrow> x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}\<close> 
              \<open>polychain (a # points)\<close> h2_hd by blast }  
    ultimately have "x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}" by auto
  }        
  ultimately show ?case by blast
qed   
  
lemma curve_linepath:
  "curve (linepath a b) {0..1}"
proof (unfold_locales)
  show "convex {0::real..1}" by auto
next
  show "compact {0::real .. 1}" by auto
next
  show "continuous_on {0..1} (linepath a b)"
    by auto  
qed
  
lemma simple_boundary_linepath:
  assumes "fst (fst a) \<noteq> fst (snd a)"
  shows "simple_boundary (linepath (fst a) (snd a)) {0..1}"
proof (unfold_locales)
  show "convex {0::real..1}" by auto
next
  show "compact {0::real .. 1}" by auto
next
  show "continuous_on {0..1} (linepath (fst a) (snd a))"
    by auto
next
  from assms have t: "fst a \<noteq> snd a" by auto
  show "inj_on (linepath (fst a) (snd a)) {0..1}"
    using inj_on_linepath t by auto
next
  show "bij_betw (curve.curve_eq_x (linepath (fst a) (snd a))) {0..1} 
                                          (curve.setX (linepath (fst a) (snd a)) {0..1})"
    unfolding bij_betw_def  curve.curve_eq_x_def[OF curve_linepath] curve.setX_def[OF curve_linepath]
  proof (rule conjI)
    have eq: "fst \<circ> linepath (fst a) (snd a) = linepath (fst (fst a)) (fst (snd a))"
      unfolding comp_def
    proof 
      fix x
      have *: "linepath (fst a) (snd a) x = (1 - x) *\<^sub>R (fst a) + x *\<^sub>R (snd a)" unfolding linepath_def
        by auto
      hence "fst ((1 - x) *\<^sub>R (fst a) + x *\<^sub>R (snd a)) = (1 - x) * (fst (fst a)) + x * (fst (snd a))"
        by auto
      also have "... = linepath (fst (fst a)) (fst (snd a)) x" unfolding linepath_def by auto   
      finally show "fst (linepath (fst a) (snd a) x) = linepath (fst (fst a)) (fst (snd a)) x"
        using * by auto
    qed
    have "inj_on (linepath (fst (fst a)) (fst (snd a))) {0..1}"
      using inj_on_linepath assms by auto
    thus "inj_on (\<lambda>s. fst (linepath (fst a) (snd a) s)) {0..1}" 
      using eq unfolding comp_def by auto
  next
    show "(\<lambda>s. fst (linepath (fst a) (snd a) s)) ` {0..1} = fst ` linepath (fst a) (snd a) ` {0..1}"
      by auto
  qed    
qed
  
lemma simple_boundary_tail:
  assumes "points \<noteq> []"
  assumes "polychain (a # points)"  
  assumes "simple_boundary (curve_eq3 (points_path2 (a # points))) {0..1}"  
  shows "simple_boundary (curve_eq3 (points_path2 (points))) {0..1}"
proof (unfold_locales)
  show " convex {0::real..1}" by auto
next
  show " compact {0::real..1}" by auto
next
  from assms(1-2) have 1: "pathfinish (linepath (fst a) (snd a)) = pathstart (curve_eq3 (points_path2 points))"
    using pathfinish_pathstart by auto
  from assms have 0: "continuous_on {0..1} (curve_eq3 (points_path2 (a # points)))"
    unfolding simple_boundary_def simple_boundary_axioms_def curve_def by auto  
  from curve_eq_cons(1)[OF assms(1)] have "curve_eq3 (points_path2 (a # points)) = 
    linepath (fst a) (snd a) +++ curve_eq3 (points_path2 points)" by auto
  with 0 show " continuous_on {0..1} (curve_eq3 (points_path2 points))" 
    using continuous_on_joinpaths_D2 1 by metis
next
  from assms(3) have bs: "inj_on (curve_eq3 (points_path2 (a # points))) {0..1}"
    unfolding simple_boundary_def simple_boundary_axioms_def by auto
  from curve_eq_cons(1)[OF assms(1)] have eq: "curve_eq3 (points_path2 (a # points)) = 
    linepath (fst a) (snd a) +++ curve_eq3 (points_path2 points)" by auto
  from bs show "inj_on (curve_eq3 (points_path2 points)) {0..1}" unfolding eq
    sorry
next
  show " bij_betw (curve.curve_eq_x (curve_eq3 (points_path2 points))) {0..1} (curve.setX (curve_eq3 (points_path2 points)) {0..1}) "
    sorry
qed
  
lemma
  assumes "points \<noteq> []"
  assumes "fst (fst a) \<le> x" and "x \<le> fst (snd a)"
  assumes "simple_boundary (curve_eq3 (points_path2 (a # points))) {0..1}"  
  shows "simple_boundary.f_of_x (curve_eq3 (points_path2 (a # points))) {0..1} x =
         simple_boundary.f_of_x (linepath (fst a) (snd a)) {0..1} x"  
proof -
  from curve_eq_cons(1)[OF assms(1)] 
    have "curve_eq3 (points_path2 (a # points)) = linepath (fst a) (snd a) +++ curve_eq3 (points_path2 points) "   
    by auto
  show ?thesis sorry  
qed
    
lemma test1':
  assumes "points \<noteq> []"
  assumes "monotone_polychain points"  
  assumes "simple_boundary (curve_eq3 (points_path2 points)) {0..1}"  
  assumes "c \<in> set points"
  assumes "fst (fst c) \<le> x" and "x \<le> fst (snd c)"
  shows "line_equation (fst c) (snd c) x = simple_boundary.f_of_x (curve_eq3 (points_path2 points)) {0..1} x"
  using assms    
proof (induction points)
  case Nil
  then show ?case by auto
next
  case (Cons a points)
  note case_cons = this  
  from `monotone_polychain (a # points)` have "fst (fst a) < fst (snd a)"
    unfolding monotone_polychain_def by auto
  hence *: "fst (fst a) \<noteq> fst (snd a)" by auto
  hence 0: "simple_boundary (linepath (fst a) (snd a)) {0..1}" using simple_boundary_linepath
    by auto
  hence 1: "curve (linepath (fst a) (snd a)) {0..1}" by(unfold_locales)  auto    
  from `monotone_polychain (a # points)` have "monotone_polychain points" using monotone_polychain_ConsD
    by auto
  from `monotone_polychain (a # points)` have "polychain (a # points)" unfolding monotone_polychain_def 
    by auto
  obtain a' and points' where "points = [] \<or> points = a' # points'"  using list.exhaust_sel by blast
  moreover
  { assume "points = []"
    from `c \<in> set (a # points)` have "c = a" using `points = []` by auto  
    have eq: "curve_eq3 (points_path2 (a # points)) = linepath (fst a) (snd a)" unfolding `points = []`
        points_path2_def by auto
    have "line_equation (fst c) (snd c) x = simple_boundary.f_of_x (linepath (fst a) (snd a)) {0..1} x"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs = line_equation (fst a) (snd a) x" unfolding `c = a` by auto 
      define y where "y \<equiv> simple_boundary.f_of_x (linepath (fst a) (snd a)) {0..1} x"     
      from case_cons(6-7) have "x \<in> curve.setX (linepath (fst a) (snd a)) {0..1}"
        unfolding `c = a`  curve.setX_def[OF 1] 
        by (metis "1" \<open>curve.setX (linepath (fst a) (snd a)) {0..1} \<equiv> fst ` linepath (fst a) (snd a) ` {0..1}\<close> 
            case_cons eq test2)
      from simple_boundary.f_of_x_curve_eq[OF 0 this, of "y"] obtain t where "t \<in> {0..1}" and 
        "linepath (fst a) (snd a) t = (x, y)"
        unfolding y_def by auto
      hence "(x, y) \<in> closed_segment (fst a) (snd a)" unfolding linepath_def closed_segment_def
        by force
      from line_equation_closed_segment[OF this *] have "line_equation (fst a) (snd a) x = y"    
        by auto
      with `?lhs = line_equation (fst a) (snd a) x` show ?thesis unfolding y_def
        by auto          
    qed      
    hence ?case using eq by auto }  
  moreover
  { assume "points = a' # points'"
    hence nem: "points \<noteq> []" by auto  
    from case_cons(5) consider "c = a" | "c \<in> set points" by auto  
    hence ?case
    proof (cases)
      case 1  
      then show ?thesis sorry
    next
      case 2
      from case_cons(4) have "simple_boundary (curve_eq3 (points_path2 points)) {0..1}"  
        using simple_boundary_tail[OF nem `polychain (a # points)`] by auto
      from case_cons(1)[OF nem `monotone_polychain points` this 2 case_cons(6-7)]
      have "line_equation (fst c) (snd c) x = simple_boundary.f_of_x (curve_eq3 (points_path2 points)) {0..1} x"
        by auto
      thus ?thesis sorry 
    qed 
  }
  ultimately show ?case by auto
qed
  
locale lanelet_simple_boundary = lanelet_curve +
  assumes monotone: "monotone_polychain points"  
begin
  
lemma first_lt_last_point: 
  "fst first_point < fst last_point"  
  using nonempty_points unfolding monotone_polychain_def
  by (metis hd_Cons_tl monotone monotone_polychain_fst_last)
    
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
  
theorem simple_boundary_curve_eq_01:
  "simple_boundary curve_eq {0..1}" 
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

interpretation lsc: simple_boundary "curve_eq" "{0..1}"
  using simple_boundary_curve_eq_01 by auto

lemma pathstart_first_point:
  "pathstart curve_eq = first_point"
proof -
  from nonempty_points obtain f and fs where "points = f # fs" using 
    linorder_list0.selsort.cases by blast
  hence "first_chain = f" by auto
  have "curve_eq = curve_eq3 (map (\<lambda>p. linepath (fst p) (snd p)) points)" 
    unfolding points_path2_def by auto
  with \<open>points = f # fs\<close> 
  have "curve_eq = curve_eq3 (map (\<lambda>p. linepath (fst p) (snd p)) (f # fs))" by auto
  hence "pathstart curve_eq = pathstart (linepath (fst f) (snd f))" 
    by (simp add: pathstart_curve_eq)
  also have "... = fst f" by auto
  finally have "pathstart curve_eq = fst f" by auto
  thus ?thesis using \<open>points = f # fs\<close> by auto      
qed     
  
lemma pathfinish_last_point:
  "pathfinish curve_eq = last_point"
proof -
  have "curve_eq = curve_eq3 (map (\<lambda>p. linepath (fst p) (snd p)) points)" 
    unfolding points_path2_def by auto
  have "pathfinish curve_eq = pathfinish (linepath (fst (last points)) (snd (last points)))"
    using pathfinish_curve_eq nonempty_points  by (simp add: last_map points_path2_def)      
  also have "... = snd (last points)" by auto                                             
  finally show "pathfinish curve_eq = snd (last points)" by auto     
qed  
      
lemma lsc_f_of_x_curve_eq:
  assumes "x \<in> lsc.setX" \<comment> \<open>@{term "x \<in> lsc.setX"}\<close>
  assumes "lsc.f_of_x x = y"
  shows "\<exists>t\<in>{0..1}. curve_eq t = (x, y)"
  using assms lsc.f_of_x_curve_eq by auto
                
lemma test1:
  assumes "c \<in> set points"
  assumes "fst (fst c) \<le> x" and "x \<le> fst (snd c)"
  shows "line_equation (fst c) (snd c) x = lsc.f_of_x x"
  using assms test2 nonempty_points lsc_f_of_x_curve_eq   
  sorry
    
lemma lsc_f_of_x_curve_eq2: 
  assumes "t \<in> {0..1}"
  assumes "curve_eq t = (x,y)"
  shows "\<exists>c s. c \<in> set points \<and> s \<in> {0..1} \<and> linepath (fst c) (snd c) s = (x, y)"
  using assms nonempty_points
proof (induction points arbitrary:t)
  case Nil
  then show ?case by auto
next
  case (Cons a points)
  note case_cons = this  
  obtain a' and points' where "points = [] \<or> points = a' # points'"  using list.exhaust_sel by blast
  moreover
  { assume "points = []"
    with case_cons have "curve_eq3 (points_path2 [a]) t = (x,y)" by auto
    hence "linepath (fst a) (snd a) t = (x,y)" unfolding points_path2_def by auto
    hence "\<exists>c s. c \<in> set (a # points) \<and> s \<in> {0..1} \<and> linepath (fst c) (snd c) s = (x, y)" 
      using case_cons(2) by (meson list.set_intros(1)) }
  moreover
  { assume ne: "points = a' # points'"
    consider "t \<le> 0.5" | "0.5 < t" by linarith
    hence "\<exists>c s. c \<in> set (a # points) \<and> s \<in> {0..1} \<and> linepath (fst c) (snd c) s = (x, y)" 
    proof (cases)
      case 1
      with case_cons(2) have rang: "2 * t \<in> {0..1}" by auto  
      from 1 and case_cons have "curve_eq3 (points_path2 (a # points)) = 
                                     (linepath (fst a) (snd a)) +++ curve_eq3 (points_path2 points)"
        (is "?lhs = ?rhs +++ _")
        unfolding ne unfolding points_path2_def by auto
      with 1 have "?lhs t = ?rhs (2 * t)" unfolding joinpaths_def by auto
      with case_cons have "linepath (fst a) (snd a) (2 * t) = (x,y)" by auto          
      then show ?thesis using rang by (meson list.set_intros(1)) 
    next
      case 2
      with case_cons(2) have as1: "2 * t - 1  \<in> {0 .. 1}" by (auto simp add:algebra_simps)  
      from case_cons have "curve_eq3 (points_path2 (a # points)) = 
                                     (linepath (fst a) (snd a)) +++ curve_eq3 (points_path2 points)"
        (is "?lhs = _ +++ ?rhs")      
        unfolding ne points_path2_def by auto
      with 2 have "?lhs t = ?rhs (2 * t - 1)" unfolding joinpaths_def by auto
      with case_cons have as2: "curve_eq3 (points_path2 points) (2 * t - 1) = (x,y)" by auto          
      with case_cons(1)[OF as1 as2] have "\<exists>c s. c \<in> set points \<and> s \<in> {0..1} \<and> linepath (fst c) (snd c) s = (x, y)"
        unfolding ne by auto          
        then show ?thesis by (meson list.set_intros)
    qed }          
  ultimately show ?case by blast
qed
        
(* making the lemma inside lsc visible for other locales extending this locale. *)  
lemma lsc_checking_strict_mono: 
  assumes "(curve.curve_eq_x curve_eq) 0 < (curve.curve_eq_x curve_eq) 1"
  shows "strict_mono_in (curve.curve_eq_x curve_eq) {0..1}"
  using lsc.checking_strict_mono assms by auto       
    
theorem curve_setX_interval:
  " curve.setX curve_eq {0..1} = {fst first_point .. fst last_point}"
  using nonempty_points monotone curve_eq_is_curve
proof (induction points)
  case Nil
  then show ?case by auto
next
  case (Cons a points)
  note case_cons = this  
  obtain a' and points' where "points = [] \<or> points = a' # points'"  by (metis hd_Cons_tl)  
  moreover
  { assume "points = []"
    hence 0: "curve.setX (curve_eq3 (points_path2 (a # points))) {0..1} = 
           curve.setX (curve_eq3 (points_path2  [a])) {0..1}" and 
      "{fst (fst (hd (a # points)))..fst (snd (last (a # points)))} =  {fst (fst a)..fst (snd a)}"
      by auto
    have 1: "points_path2 [a] = [linepath (fst a) (snd a)]" unfolding points_path2_def by auto        
    hence 2: "curve_eq3 (points_path2 [a]) = linepath (fst a) (snd a)" by auto
    have "curve.setX (linepath (fst a) (snd a)) {0..1} = fst ` closed_segment (fst a) (snd a)"
      using linepath_image_01 curve.setX_def
      by (simp add: linepath_image_01 continuous_on_linepath curve.intro)
    also have "... = closed_segment (fst (fst a)) (fst (snd a))" 
      using fst_closed_segment by auto
    finally have "curve.setX (linepath (fst a) (snd a)) {0..1} = 
                                                         closed_segment (fst (fst a)) (fst (snd a))"
      by auto
    moreover     
    from case_cons(3) have "fst (fst a) < fst (snd a)" unfolding monotone_polychain_def by auto
    ultimately have "curve.setX (linepath (fst a) (snd a)) {0..1} = {fst (fst a) .. fst (snd a)}"
      using closed_segment_real by auto
    hence "curve.setX (curve_eq3 (points_path2 (a # points))) {0..1} = 
                                       {fst (fst (hd (a # points)))..fst (snd (last (a # points)))}"
      using \<open>points = []\<close> 0 1 2 by auto }
  
  moreover
  { assume "points = a' # points'"
    hence psce3: "pathstart (curve_eq3 (points_path2 points)) = fst a'"
      unfolding \<open>points = a' # points'\<close> points_path2_def
      using pathstart_curve_eq pathstart_linepath by auto 
    from \<open>monotone_polychain (a # points)\<close> have "snd a = fst a'"
      unfolding \<open>points = a' # points'\<close> monotone_polychain_def polychain_def by auto
    from \<open>monotone_polychain (a # points)\<close> have t1: "monotone_polychain points" 
      using monotone_polychain_ConsD by auto
    from case_cons(4) have t2: "curve (curve_eq3 (points_path2 points)) {0..1}"
      unfolding curve_def using \<open>monotone_polychain points\<close> \<open>points = a' # points'\<close> curve_eq_cont 
      monotone_polychain_def by blast 
    from \<open>points = a' # points'\<close> case_cons(1)[OF _ t1 t2] 
    have ind: "curve.setX (curve_eq3 (points_path2 points)) {0..1} = 
                                                  {fst (fst (hd points))..fst (snd (last points))} "
      by auto
    have "points_path2 (a # points) = linepath (fst a) (snd a) # points_path2 points"
      unfolding points_path2_def by auto
    hence "curve_eq3 (points_path2 (a # points)) = 
                                       linepath (fst a) (snd a) +++ curve_eq3 (points_path2 points)"
      using \<open>points = a' # points'\<close> by (simp add: points_path2_def)
    hence "curve_eq3 (points_path2 (a # points)) ` {0..1} = closed_segment (fst a) (snd a) \<union> 
                                                            curve_eq3 (points_path2 points) ` {0 .. 1}"
      using joinpaths_image_01 psce3 pathfinish_linepath \<open>snd a = fst a'\<close> 
      by (simp add: joinpaths_image_01 linepath_image_01)
    hence "curve.setX (curve_eq3 (points_path2 (a # points))) {0 .. 1} = 
          fst ` closed_segment (fst a) (snd a) \<union> curve.setX (curve_eq3 (points_path2 points)) {0..1}"
      using curve.setX_def[OF case_cons(4)] curve.setX_def[OF t2]  by (simp add: image_Un)
    with ind have "curve.setX (curve_eq3 (points_path2 (a # points))) {0 .. 1} =
          fst `closed_segment (fst a) (snd a) \<union> {fst (fst a') .. fst (snd (last points))}" 
      unfolding \<open>points = a' # points'\<close> by auto
    also have "... = closed_segment (fst (fst a)) (fst (snd a)) \<union> {fst (fst a') .. fst (snd (last points))}"
      by auto
    finally have *: "curve.setX (curve_eq3 (points_path2 (a # points))) {0 .. 1} = 
             closed_segment (fst (fst a)) (fst (snd a)) \<union> {fst (fst a') .. fst (snd (last points))}"        
      by auto
    have "fst (fst a) < fst (snd a)" using \<open>monotone_polychain (a # points)\<close>
      unfolding monotone_polychain_def by auto
    hence "closed_segment (fst (fst a)) (fst (snd a)) = {fst (fst a) .. fst (snd a)}" 
      using closed_segment_real by auto
    with * have **: "curve.setX (curve_eq3 (points_path2 (a # points))) {0..1} = 
             {fst (fst a) .. fst (snd a)} \<union> {fst (fst a') .. fst (snd (last points))}" 
      by auto
    have "fst (snd a) = fst (fst a')" using \<open>snd a = fst a'\<close> by (auto simp add:prod.collapse)
    moreover have "fst (fst a) < fst (snd a)" using \<open>monotone_polychain (a # points)\<close> unfolding 
      monotone_polychain_def by auto
    moreover have "fst (fst a') < fst (snd (last points))" 
      using \<open>points = a' # points'\<close> monotone_polychain_fst_last t1 by blast                    
    ultimately have "curve.setX (curve_eq3 (points_path2 (a # points))) {0..1} = 
             {fst (fst a) .. fst (snd (last points))}" using ivl_disj_un(26) ** by auto }
  ultimately show ?case using last_ConsR by auto  
qed
   
end
    
subsection "Preliminaries for locale lanelet"  
    
text \<open>The direction of a lanelet is defined according to the relative position of the left polychain
with respect to the right polychain. In order to determine the direction, we first construct a 
polygon from these two polychains, and then find the vertex (point) which is guaranteed to be
the point in its convex hull. To find this vertex, we only need to find the points with the smallest
@{term "x"} value, and if there are more than one, we choose the one with the smallest @{term "y"}
values. The following function min2D does this job.\<close> 
  
subsubsection "Preliminaries for naive way of defining orientation"
  
definition
  "polygon xs \<longleftrightarrow> (polychain xs \<and> (xs \<noteq> [] \<longrightarrow> fst (hd xs) = snd (last xs)))"
     
text "A function for finding the smallest (in x and y dimension) vertex of the convex hull of
  a (not necessarily convex) polygon."  
    
fun convex_hull_vertex2 :: "(real2 \<times>  real2) list \<Rightarrow> real2 option" where
 "convex_hull_vertex2 [] = None" | 
 "convex_hull_vertex2 (z # zs) = 
      (case convex_hull_vertex2 zs of
         None \<Rightarrow> Some (min2D (fst z) (snd z))
       | Some z' \<Rightarrow> Some (min2D (fst z) z'))"

lemma cons_convex_hull_vertex_some':
  "\<exists>x. convex_hull_vertex2 (z # zs) = Some x"
  by (simp add: option.case_eq_if)  
    
fun convex_hull_vertex3 :: "(real2 \<times>  real2) list \<Rightarrow> real2 option" where
 "convex_hull_vertex3 [] = None" |
 "convex_hull_vertex3 [z] = Some (min2D (fst z) (snd z))" |  
 "convex_hull_vertex3 (z1 # z2 # zs) = 
      (case convex_hull_vertex3 (z2 # zs) of Some z' \<Rightarrow> Some (min2D (fst z1) z'))"
     
lemma cons_convex_hull_vertex_some:
  "\<exists>x. convex_hull_vertex3 (z # zs) = Some x"
proof (induction zs arbitrary:z)
  case Nil
  then show ?case by auto
next
  case (Cons a zs)
  then obtain x where "convex_hull_vertex3 (a # zs) = Some x" by blast
  hence "convex_hull_vertex3 (z # a # zs) = Some (min2D (fst z) x)" by auto     
  then show ?case by auto
qed
  
text \<open>Function @{term "convex_hull_vertex3"} is the same with @{term "convex_hull_vertex2"}. It is 
nicer to have the former when we are doing induction.\<close>  
 
theorem chv3_eq_chv2:
  "convex_hull_vertex3 zs = convex_hull_vertex2 zs" 
proof (induction zs rule:convex_hull_vertex3.induct)
  case 1
  then show ?case by auto
next
  case (2 z)
  then show ?case by auto
next
  case (3 z1 z2 zs)
  note case_three = this  
  obtain x where "convex_hull_vertex2 (z2 # zs) = Some x" using cons_convex_hull_vertex_some' 
    by blast
  hence "convex_hull_vertex2 (z1 # z2 # zs) = Some (min2D (fst z1) x)" by auto      
  then show ?case using case_three by (auto split:option.split)
qed
  
text \<open>This function is to test the membership of a point in a polychain.\<close>  
    
definition element_of_polychain :: "real2 \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> bool" where
  "element_of_polychain x xs \<equiv> \<exists>y. (x, y) \<in> set xs \<or> (y, x) \<in> set xs" 
  
lemma element_of_polychain_cons:
  assumes "element_of_polychain x xs"
  shows "element_of_polychain x (y # xs)"
  using assms unfolding element_of_polychain_def by auto
    
lemma element_of_polychainD:
  assumes "element_of_polychain x (y # ys)"
  shows "element_of_polychain x [y] \<or> element_of_polychain x ys"
  using assms unfolding element_of_polychain_def by auto

lemma element_of_polychain_app:
  "element_of_polychain z (xs @ ys) = element_of_polychain z xs \<or> element_of_polychain z ys"
  unfolding element_of_polychain_def by auto
        
lemma el_of_polychain1:    
  assumes "polychain zs" 
  assumes "convex_hull_vertex2 zs = Some z"
  shows "element_of_polychain z zs"
  using assms 
proof (induction zs arbitrary:z)
  case Nil
  then show ?case by auto
next
  case (Cons a zs)
  note case_cons = this
  obtain z' and zs' where "zs = [] \<or> zs = z' # zs'" by (metis hd_Cons_tl)  
  moreover
  { assume empty: "zs = []"
    with case_cons have "convex_hull_vertex2 (a # zs) = Some (min2D (fst a) (snd a))" by auto
    with case_cons have "min2D (fst a) (snd a) = z" by auto
    hence "z = (fst a) \<or> z = (snd a)" unfolding min2D_def by presburger        
    hence "element_of_polychain z (a # zs)" unfolding empty element_of_polychain_def
      apply (cases "z = fst a")      
      apply (metis list.set_intros(1) prod.collapse)  
      by (metis \<open>z = fst a \<or> z = snd a\<close> list.set_intros(1) prod.collapse) }
  moreover 
  { assume cons: "zs = z' # zs'"
    hence "convex_hull_vertex2 zs \<noteq> None" by (simp add: option.case_eq_if)
    then obtain b where "convex_hull_vertex2 zs = Some b" by auto
    hence "convex_hull_vertex2 (a # zs) = Some (min2D (fst a) b)" by auto
    with case_cons have "z = min2D (fst a) b" by auto
    from case_cons have "polychain zs"
      by (metis \<open>convex_hull_vertex2 zs \<noteq> None\<close> convex_hull_vertex2.simps(1) polychain_Cons)
    with case_cons and \<open>convex_hull_vertex2 zs = Some b\<close> have "element_of_polychain b zs"
      by auto
    with \<open>z = min2D (fst a) b\<close> have "element_of_polychain z (a # zs)" 
    (* Isar proofs found by sledgehammer *)
    proof -
      have f1: "\<forall>x0 x1. (snd (x1::real \<times> real) \<le> snd (x0::real \<times> _)) = (0 \<le> snd x0 + - 1 * snd x1)"
        by auto
      have "\<forall>x0 x1. (fst (x1::real \<times> real) < fst (x0::_ \<times> real)) = (\<not> fst x0 + - 1 * fst x1 \<le> 0)"
        by auto
      then have f2: "\<forall>p pa. min2D p pa = (if fst pa + - 1 * fst p \<le> 0 then if fst p = fst pa then if 0 \<le> snd pa + - 1 * snd p then p else pa else pa else p)"
        using f1 min2D_def by presburger
      { assume "\<not> (if 0 \<le> snd b + - 1 * snd (fst a) then min2D (fst a) b = fst a else min2D (fst a) b = b)"
        moreover
        { assume "\<not> (if fst (fst a) = fst b then if 0 \<le> snd b + - 1 * snd (fst a) then min2D (fst a) b = fst a else min2D (fst a) b = b else min2D (fst a) b = b)"
          then have "min2D (fst a) b = fst a"
       using f2 by meson
     then have "fst (min2D (fst a) b, fst z') = fst a"
            by (metis prod.sel(1)) }
        ultimately have "min2D (fst a) b = b \<or> fst (min2D (fst a) b, fst z') = fst a"
          by (metis (no_types)) }
      moreover
      { assume "fst (min2D (fst a) b, fst z') = fst a"
        moreover
        { assume aaa1: "fst (min2D (fst a) b, fst z') = fst a \<and> (min2D (fst a) b, fst z') \<noteq> a"
          obtain pp :: "(real \<times> real) \<times> real \<times> real" and pps :: "((real \<times> real) \<times> real \<times> real) list" where
            "(\<exists>v0 v1. zs = v0 # v1) = (zs = pp # pps)"
            by blast
          moreover
          { assume "snd ((a # zs) ! 0) \<noteq> fst ((a # zs) ! Suc 0)"
            then have "\<not> Suc 0 < length (a # zs)"
              by (meson case_cons(2) polychain_def)
            then have "zs \<noteq> pp # pps"
              by auto }
          ultimately have ?thesis
            using aaa1 by (metis (no_types) cons nth_Cons_0 nth_Cons_Suc prod.sel(2) prod_eqI) }
        ultimately have ?thesis
          by (metis (no_types) \<open>z = min2D (fst a) b\<close> element_of_polychain_def insert_iff list.set(2)) }
      moreover
      { assume "min2D (fst a) b = b"
        then have "element_of_polychain (min2D (fst a) b) zs"
          by (metis Cons.IH \<open>convex_hull_vertex2 zs = Some b\<close> \<open>polychain zs\<close>)
        then have ?thesis
          by (metis \<open>z = min2D (fst a) b\<close> element_of_polychain_cons) }
      ultimately show ?thesis
        by (metis (no_types) prod.sel(1))
    qed }                              
  ultimately show ?case by auto  
qed
         
theorem el_of_polychain2:    
  assumes "polygon zs" 
  assumes "convex_hull_vertex2 zs = Some z"
  shows "element_of_polychain z zs"  
proof -
  from assms(1) have "polychain zs" unfolding polygon_def by auto
  with el_of_polychain1[OF this assms(2)] show ?thesis by auto      
qed
  
lemma element_of_polychain_nth:
  "element_of_polychain z zs \<Longrightarrow> \<exists>i. i<length zs \<and> (z = fst (zs ! i) \<or> z = snd (zs ! i))"
proof (induction zs)
  case Nil
  then show ?case unfolding element_of_polychain_def by auto
next
  case (Cons a zs)
  then have "element_of_polychain z [a] \<or> element_of_polychain z zs" using element_of_polychainD by auto
  then show ?case
  proof
    assume "element_of_polychain z [a]"
    then show ?case unfolding element_of_polychain_def by auto
  next
    assume "element_of_polychain z zs"
    then have "\<exists>i. i < length zs \<and> (z = fst (zs ! i) \<or> z = snd (zs ! i))" using Cons by auto
    then show ?case by fastforce
  qed
qed
  
lemma nth_element_of_polychain:
  "\<exists>i. i<length zs \<and> (z = fst (zs ! i) \<or> z = snd (zs ! i)) \<Longrightarrow> element_of_polychain z zs"
proof -
  assume "\<exists>i. i<length zs \<and> (z = fst (zs ! i) \<or> z = snd (zs ! i))"
  then have "\<exists>i. i<length zs \<and> ((z,snd (zs ! i)) = zs ! i \<or> (fst (zs ! i),z) = zs ! i)" by auto
  then have "\<exists>i. i<length zs \<and> (\<exists>y. (z,y) = zs ! i \<or> (y,z) = zs ! i)" by blast
  then obtain i where "i<length zs" "\<exists>y. (z,y) = zs ! i \<or> (y,z) = zs ! i" by auto
  then obtain y where "(z,y) = zs ! i \<or> (y,z) = zs ! i" by auto
  then have "(z,y) \<in> set zs \<or> (y,z) \<in> set zs" using `i<length zs` nth_mem by auto
  then show ?thesis unfolding element_of_polychain_def by blast
qed
    
theorem convex_hull_vertex_smallest_x:
  assumes "polychain zs"
  assumes "convex_hull_vertex2 zs = Some x"
  shows "\<forall>z \<in> set zs. fst x \<le> fst (fst z) \<and> fst x \<le> fst (snd z)"
  using assms  
proof (induction zs arbitrary:x)
  case Nil
  then show ?case by auto
next
  case (Cons a zs)
  note case_cons = this  
  obtain x' where "convex_hull_vertex2 zs = None \<or> convex_hull_vertex2 zs = Some x'"
    by fastforce
  moreover
  { assume none: "convex_hull_vertex2 zs = None"
    with case_cons(3) have x_min2d: "x = min2D (fst a) (snd a)" by auto
    from none have "zs = []" 
      by (metis (no_types, lifting) convex_hull_vertex2.simps(2) hd_Cons_tl option.case_eq_if 
                                                                                 option.distinct(1))        
    have " \<forall>z\<in>set (a # zs). fst x \<le> fst (fst z) \<and> fst x \<le> fst (snd z)"        
      unfolding \<open>zs = []\<close> using min2D_def x_min2d by force }
  moreover
  { assume some: "convex_hull_vertex2 zs = Some x'"      
    with case_cons(3) have "x = min2D (fst a) x'" by auto
    from case_cons(2) have "polychain zs" by (metis polychain_Cons polychain_Nil)
    from case_cons(1)[OF this some] have 0: "\<forall>z\<in>set zs. fst x' \<le> fst (fst z) \<and> fst x' \<le> fst (snd z)" .
    from \<open>x = min2D (fst a) x'\<close> have "fst x \<le> fst x'" and "fst x \<le> fst (fst a)"
      using min2D_D by auto
    with 0 have 1: "\<forall>z \<in>set zs. fst x \<le> fst (fst z) \<and> fst x \<le> fst (snd z)" by auto
    from some have "zs \<noteq> []" by auto    
    with \<open>polychain (a # zs)\<close> and hd_conv_nth[OF this] have "snd a = fst (hd zs)" 
      unfolding polychain_def by auto
    with \<open>zs \<noteq> []\<close> and 1 have "fst x \<le> fst (snd a)" by auto            
    with 1 \<open>fst x \<le> fst (fst a)\<close>  have "\<forall>z\<in>set (a # zs). fst x \<le> fst (fst z) \<and> fst x \<le> fst (snd z)"
      by auto }
  ultimately show "\<forall>z\<in>set (a # zs). fst x \<le> fst (fst z) \<and> fst x \<le> fst (snd z)" by auto  
qed
  
theorem convex_hull_vertex_smallest_x2:
  assumes "polychain zs"
  assumes "convex_hull_vertex2 zs = Some x"
  assumes "element_of_polychain z zs"    
  shows "fst x \<le> fst z"
  using convex_hull_vertex_smallest_x[OF assms(1) assms(2)] assms(3)
  unfolding element_of_polychain_def by auto
        
theorem convex_hull_vertex_smallest_y:
  assumes "polychain zs"
  assumes "convex_hull_vertex3 zs = Some x"
  assumes "element_of_polychain y zs \<and> fst x = fst y"
  shows "snd x \<le> snd y"    
  using assms
proof (induction zs arbitrary:x y rule:convex_hull_vertex3.induct)
  case 1
  then show ?case by auto
next
  case (2 z)
  note case_two = this  
  hence 0: "x = min2D (fst z) (snd z)" by auto  
  from case_two obtain y' where "(y, y') = z \<or> (y', y) = z" unfolding element_of_polychain_def 
    by auto
  with 0 case_two show "snd x \<le> snd y" 
    by (smt case_two(3) fst_conv min2D_def snd_conv)    
next
  case (3 z1 z2 zs)
  note case_three = this                
  then obtain x' where 1: "convex_hull_vertex3 (z2 # zs) = Some x'" using cons_convex_hull_vertex_some
    by blast
  from case_three(2) have "polychain (z2 # zs)" by (auto simp add:polychain_Cons)     
  with 1 case_three have "x = min2D (fst z1) x'" by auto  
  from case_three(4) have "element_of_polychain y [z1] \<or> element_of_polychain y (z2 # zs)"
    using element_of_polychainD by auto
  moreover
  { assume "element_of_polychain y (z2 # zs)"
    with case_three(1)[OF \<open>polychain (z2 # zs)\<close> 1] have 2: "fst x' = fst y \<longrightarrow> snd x' \<le> snd y"
      by auto                                                           
    from \<open>x = min2D (fst z1) x'\<close> have "x = (fst z1) \<or> x = x'" using min2D_D2 by auto
    moreover
    { assume "x = x'"
      with 2 and case_three have "snd x \<le> snd y" by auto }
    moreover
    { assume "x = fst z1"
      with \<open>x = min2D (fst z1) x'\<close> have 3: "fst (fst z1) < fst x' \<or> 
                                           (fst (fst z1) = fst x'\<and> snd (fst z1) \<le> snd x')" 
        using min2D_D3 by auto
      from 1 and \<open>element_of_polychain y (z2 # zs)\<close> have "fst x' \<le> fst y" 
        using convex_hull_vertex_smallest_x2[OF \<open>polychain (z2 # zs)\<close>] chv3_eq_chv2 by auto  
      with case_three(4) and 3 \<open>x = fst z1\<close> have "(fst x = fst x'\<and> snd x \<le> snd x')"
        by auto
      moreover with case_three(4) and 2 have "snd x' \<le> snd y" by auto
      ultimately have "snd x \<le> snd y" by auto }
    ultimately have "snd x \<le> snd y" by auto }
  moreover
  { assume 4: "element_of_polychain y [z1]"
    from \<open>x = min2D (fst z1) x'\<close> have "x = (fst z1) \<or> x = x'" using min2D_D2 by auto
    moreover
    { assume "x = fst z1"
      with \<open>x = min2D (fst z1) x'\<close> have  5: "fst (fst z1) < fst x' \<or> 
                                            (fst (fst z1) = fst x'\<and> snd (fst z1) \<le> snd x')" 
        using min2D_D3 by auto
      from 4 have "y = fst z1 \<or> y = snd z1" unfolding element_of_polychain_def by auto  
      moreover
      { assume "y = fst z1"
        hence "x = y" using \<open>x = fst z1\<close> by auto
        hence "snd x \<le> snd y" by auto }
      moreover
      { assume "y = snd z1"
        hence "element_of_polychain y (z2 # zs)" using \<open>polychain (z1 # z2 # zs)\<close> 
          by (metis element_of_polychain_def list.set_intros(1) list.simps(3) nth_Cons_0 
                                                                       polychain_Cons prod.collapse)  
        with case_three(1)[OF \<open>polychain (z2 # zs)\<close> 1] have 6: "fst x' = fst y \<longrightarrow> snd x' \<le> snd y"
          by auto  
        from 1 and \<open>element_of_polychain y (z2 # zs)\<close> have "fst x' \<le> fst y" 
          using convex_hull_vertex_smallest_x2[OF \<open>polychain (z2 # zs)\<close>] chv3_eq_chv2 by auto  
        with case_three(4) and 5  \<open>x = fst z1\<close> have "(fst x = fst x'\<and> snd x \<le> snd x')"
          by auto 
        moreover with case_three(4) and 6 have "snd x' \<le> snd y" by auto
        ultimately have "snd x \<le> snd y" by auto }
      ultimately have "snd x \<le> snd y" by auto }
    moreover
    { assume "x = x'"
      with \<open>x = min2D (fst z1) x'\<close> have  7: "fst (fst z1) > fst x' \<or> 
                                            (fst (fst z1) = fst x'\<and> snd (fst z1) \<ge> snd x')" 
        using min2D_D4 by auto
      from 4 have "y = fst z1 \<or> y = snd z1" unfolding element_of_polychain_def by auto  
      moreover
      { assume "y = fst z1"
        hence "fst y = fst (fst z1)" by auto
        with case_three(4) and \<open>x = x'\<close> and 7 and \<open>y = fst z1\<close> have "snd x \<le> snd y" by auto }
      moreover
      { assume "y = snd z1"
        hence "element_of_polychain y (z2 # zs)" using \<open>polychain (z1 # z2 # zs)\<close> 
          by (metis element_of_polychain_def list.set_intros(1) list.simps(3) nth_Cons_0 
                                                                       polychain_Cons prod.collapse)  
        with case_three(1)[OF \<open>polychain (z2 # zs)\<close> 1] have 6: "fst x' = fst y \<longrightarrow> snd x' \<le> snd y"
          by auto  
        from 1 and \<open>element_of_polychain y (z2 # zs)\<close> have "fst x' \<le> fst y" 
          using convex_hull_vertex_smallest_x2[OF \<open>polychain (z2 # zs)\<close>] chv3_eq_chv2 by auto  
        with case_three(4) and 7  \<open>x = x'\<close> have "(fst x = fst x'\<and> snd x \<le> snd x')" by auto 
        moreover with case_three(4) and 6 have "snd x' \<le> snd y" by auto
        ultimately have "snd x \<le> snd y" by auto }
      ultimately have "snd x \<le> snd y" by auto }
    ultimately have "snd x \<le> snd y" by auto }
  ultimately show "snd x \<le> snd y" by auto
qed

lemma smallest_convex_hull_vertex:
  assumes "polychain zs"
  assumes "element_of_polychain x zs"
  assumes "\<And>z. element_of_polychain z zs \<Longrightarrow> fst x \<le> fst z"
  assumes "\<And>z. element_of_polychain z zs \<Longrightarrow> fst x = fst z \<Longrightarrow> snd x \<le> snd z"
  assumes "convex_hull_vertex3 zs = Some x'"
  shows "x = x'"
  using assms chv3_eq_chv2 convex_hull_vertex_smallest_x2 convex_hull_vertex_smallest_y el_of_polychain1 prod_eqI by smt  
 
lemma monotone_polychain_smallest:
  assumes "monotone_polychain zs"
  assumes "zs \<noteq> []"
  shows "i < length zs \<Longrightarrow> (fst (hd zs) = fst (zs ! i)  \<or> fst (fst (hd zs)) < fst (fst (zs ! i))) \<and> (fst (hd zs) = snd (zs ! i) \<or> fst (fst (hd zs)) < fst (snd (zs ! i)))"
proof (induction i)
  case 0
  show ?case
  proof
    show "fst (hd zs) = fst (zs ! 0) \<or> fst (fst (hd zs)) < fst (fst (zs ! 0))" using assms hd_conv_nth[of zs] by auto
  next
    have "fst (fst (zs ! 0)) < fst (snd (zs ! 0))" using assms unfolding monotone_polychain_def hd_conv_nth[of zs] by auto
    then show "fst (hd zs) = snd (zs ! 0) \<or> fst (fst (hd zs)) < fst (snd (zs ! 0))" using assms hd_conv_nth[of zs] by auto
  qed
next
  case (Suc i)
  have "fst (fst (hd zs)) \<le> fst (fst (zs ! i))" using Suc by auto
  show ?case
  proof
    have "fst (hd zs) = snd (zs ! i) \<or> fst (fst (hd zs)) < fst (snd (zs ! i))" using Suc by auto
    then show "fst (hd zs) = snd (zs ! Suc i) \<or> fst (fst (hd zs)) < fst (snd (zs ! Suc i))"
    proof
      assume "fst (hd zs) = snd (zs ! i)"
      then have "fst (fst (hd zs)) = fst (snd (zs ! i))" by auto
      also have "\<dots> = fst (fst (zs ! Suc i))" using Suc assms monotone_polychainD unfolding polychain_def by auto
      also have "\<dots> < fst (snd (zs ! (Suc i)))" using Suc assms unfolding monotone_polychain_def by auto
      finally show "fst (hd zs) = snd (zs ! Suc i) \<or> fst (fst (hd zs)) < fst (snd (zs ! Suc i))" by auto
    next
      assume " fst (fst (hd zs)) < fst (snd (zs ! i))"
      also have "\<dots> = fst (fst (zs ! (Suc i)))" using Suc assms monotone_polychainD unfolding polychain_def by auto
      also have "\<dots> < fst (snd (zs ! (Suc i)))" using Suc assms unfolding monotone_polychain_def by auto
      finally show "fst (fst (hd zs)) < fst (snd (zs ! i)) \<Longrightarrow> fst (hd zs) = snd (zs ! Suc i) \<or> fst (fst (hd zs)) < fst (snd (zs ! Suc i))" by auto
    qed   
  next
    have "fst (hd zs) = fst (zs ! i) \<or> fst (fst (hd zs)) < fst (fst (zs ! i))" using Suc by auto
    then show "fst (hd zs) = fst (zs ! Suc i) \<or> fst (fst (hd zs)) < fst (fst (zs ! Suc i))"
    proof
      assume "fst (hd zs) = fst (zs ! i)"
      then have "fst (fst (hd zs)) = fst (fst (zs ! i))" by auto
      also have "\<dots> < fst (snd (zs ! i))" using Suc assms unfolding monotone_polychain_def by auto
      also have "\<dots> = fst (fst (zs ! Suc i))" using Suc assms monotone_polychainD unfolding polychain_def by auto
      finally show "fst (hd zs) = fst (zs ! Suc i) \<or> fst (fst (hd zs)) < fst (fst (zs ! Suc i))" by auto
    next
      assume "fst (fst (hd zs)) < fst (fst (zs ! i))"
      also have "\<dots> < fst (snd (zs ! i))" using Suc assms unfolding monotone_polychain_def by auto
      also have "\<dots> = fst (fst (zs ! (Suc i)))" using Suc assms monotone_polychainD unfolding polychain_def by auto
      finally show "fst (hd zs) = fst (zs ! Suc i) \<or> fst (fst (hd zs)) < fst (fst (zs ! Suc i))" by auto
    qed
  qed
qed
  
lemma hd_smallest:
  assumes "zs \<noteq> []"
  assumes "monotone_polychain zs"
  assumes "element_of_polychain z zs"
  shows "z = fst (hd zs) \<or> fst (fst (hd zs)) < fst z"
proof -
  obtain i where "i<length zs" "z = fst (zs ! i) \<or> z = snd (zs ! i)" using assms element_of_polychain_nth by blast
  then show ?thesis using assms monotone_polychain_smallest[of zs i] by auto
qed
    
(* TODO: prove that the result of convex_hull_vertex2 is an extreme point of the convex hull. *)  
  
text \<open>Function @{term "pre_and_post_betw"} and @{term "pre_and_post"} are the functions to find 
the point connected before and after a point in the polychain. The former is the tail recursive 
part of the latter.\<close>  
  
fun pre_and_post_betw :: "(real2 \<times> real2) list \<Rightarrow> real2 \<Rightarrow> (real2 \<times> real2) option" where
  "pre_and_post_betw [] x = None" | 
  "pre_and_post_betw [z] x = None" | 
  "pre_and_post_betw (z1 # z2 # zs) x = (if snd z1 = x then Some (fst z1, snd z2) else 
                                                            pre_and_post_betw (z2 # zs) x)"  

lemma min_length_pre_post_betw_some:
  assumes "pre_and_post_betw zs x = Some pp"  
  shows "2 \<le> length zs"
  using assms 
  by (induction arbitrary:x pp rule:pre_and_post_betw.induct) (auto)

lemma pre_post_betw_component:
  assumes "pre_and_post_betw zs x = Some pp"
  shows  "\<exists>z1 z2 zs'. zs = z1 # z2 # zs'"
proof -
  from assms and min_length_pre_post_betw_some have "2 \<le> length zs" by auto    
  then obtain z1 and z2 and zs' where "zs = z1 # z2 # zs'" 
    by (metis assms option.distinct(1) pre_and_post_betw.elims)
  thus ?thesis by blast    
qed

theorem pre_post_betw_correctness:
  assumes "pre_and_post_betw zs x = Some pp"
  shows "\<exists>i. fst (zs ! i) = fst pp \<and> snd (zs ! i) = x \<and> snd (zs ! (i+1)) = snd pp"
  using assms
proof (induction arbitrary:pp rule:pre_and_post_betw.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 z x)
  then show ?case by auto
next
  case (3 z1 z2 zs x)
  note case_three = this    
  consider "x = snd z1" | "x \<noteq> snd z1" by auto      
  then show ?case 
  proof (cases)
    case 1
    with case_three show ?thesis 
      by (metis add_gr_0 diff_add_inverse2 fst_conv less_one nth_Cons_0 nth_Cons_pos option.inject 
                                                                pre_and_post_betw.simps(3) snd_conv)
  next
    case 2
    note subcase_two = \<open>x \<noteq> snd z1\<close>
    with case_three have "pre_and_post_betw (z1 # z2 # zs) x = pre_and_post_betw (z2 # zs) x"
      and 0: "pre_and_post_betw (z2 # zs) x = Some pp"
      by auto
    with \<open>pre_and_post_betw (z1 # z2 # zs) x = Some pp\<close> obtain z3 and zs' where "zs = z3 # zs'"
      using pre_post_betw_component[of "z2 # zs" "x" "pp"] by auto
    with case_three(1)[OF not_sym[OF subcase_two] 0] obtain i where 
      "fst ((z2 # zs) ! i) = fst pp \<and> snd ((z2 # zs) ! i) = x \<and> snd ((z2 # zs) ! (i + 1)) = snd pp"
      by blast
    hence 1: "fst ((z1 # z2 # zs) ! (i+1)) = fst pp \<and> snd ((z1#z2#zs) ! (i+1)) = x \<and> 
                                                                     snd ((z1#z2#zs) !(i+2))=snd pp"
      by auto
    thus ?thesis  by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) one_add_one)
  qed
qed    

(* This function is not necessarily recursive. Avoid using pre_and_post.induct! *)
  
fun pre_and_post :: "(real2 \<times> real2) list \<Rightarrow> real2 \<Rightarrow> (real2 \<times> real2) option" where
  "pre_and_post [] x = None" | 
  "pre_and_post [z] x = None" | 
  "pre_and_post (z1 # z2 # zs) x = (if fst z1 = x then Some (fst (last (z2 # zs)), snd z1) else 
                                                       pre_and_post_betw (z1 # z2 # zs) x)"

lemma min_length_pre_post_some:
  assumes "pre_and_post zs x = Some pp"  
  shows "2 \<le> length zs"
  using assms 
  by (induction arbitrary:x pp rule:pre_and_post.induct) (auto)

lemma pre_post_component:
  assumes "pre_and_post zs x = Some pp"
  shows  "\<exists>z1 z2 zs'. zs = z1 # z2 # zs'"
proof -
  from assms and min_length_pre_post_some have "2 \<le> length zs" by auto    
  then obtain z1 and z2 and zs' where "zs = z1 # z2 # zs'" 
    by (metis assms option.distinct(1) pre_and_post.elims)
  thus ?thesis by blast    
qed

text \<open>We prove the correctness of the @{term "pre_and_post"} here.\<close>
  
theorem pre_and_post_correctness1:
  assumes "pre_and_post zs x = Some pp"
  assumes "x \<noteq> fst (hd zs)"  
  shows "\<exists>i. fst (zs ! i) = fst pp \<and> snd (zs ! i) = x \<and> snd (zs ! (i + 1)) = snd pp"
  using assms
proof (induction zs arbitrary: x pp)
  case Nil
  then show ?case by auto
next
  case (Cons a zs)
  note case_cons = this
  from \<open>pre_and_post (a # zs) x = Some pp\<close> obtain z and zs' where "zs = z # zs'" 
    using pre_post_component by blast
  with \<open>x \<noteq> fst (hd (a #zs))\<close>  have "pre_and_post (a # zs) x = pre_and_post_betw (a # zs) x" by auto
  with \<open>pre_and_post (a # zs) x = Some pp\<close> obtain i where
    "fst ((a#zs) ! i) = fst pp \<and> snd ((a#zs) ! i) = x \<and> snd ((a#zs) ! (i+1)) = snd pp"
    using pre_post_betw_correctness by presburger
  then show ?case by auto
qed

theorem pre_and_post_correctness2:
  assumes "pre_and_post zs x = Some pp"
  assumes "x = fst (hd zs)"  
  shows "fst (last zs) = fst pp \<and> snd (hd zs) = snd pp"
  using assms
  by (metis (no_types, lifting) fst_conv last_ConsR list.sel(1) list.simps(3) option.inject 
                                                  pre_and_post.simps(3) pre_post_component snd_conv)    

theorem pre_post_betw_convex_hull_vertex:
  assumes "2 \<le> length zs"
  assumes "polychain zs"    
  assumes "convex_hull_vertex3 zs = Some x"   
  assumes "x \<noteq> fst (hd zs)"
  assumes "x \<noteq> snd (last zs)"  
  shows "\<exists>pp. pre_and_post_betw zs x = Some pp"
  using assms
proof (induction zs arbitrary:x rule:convex_hull_vertex3.induct)
  case 1
  then show ?case by auto
next
  case (2 z)
  then show ?case by auto
next
  case (3 z1 z2 zs)
  note case_three = this  
  obtain x' where "convex_hull_vertex3 (z2 # zs) = Some x'" using cons_convex_hull_vertex_some
    by blast
  with \<open>convex_hull_vertex3 (z1 # z2 # zs) = Some x\<close> have "x = min2D (fst z1) x'" by auto
  with \<open> x \<noteq> fst (hd (z1 # z2 # zs))\<close> have "x = x'" using min2D_D2 by fastforce    
  consider "x' = fst z2" | "x'\<noteq> fst z2" by blast  
  then show ?case 
  proof (cases)
    case 1
    with \<open>polychain (z1 # z2 # zs)\<close> have "x = snd z1" unfolding polychain_def using \<open>x = x'\<close> by auto  
    hence "pre_and_post_betw (z1 # z2 # zs) x = Some (fst z1, snd z2)" by auto                
    thus ?thesis by auto
  next
    case 2
    hence "x \<noteq> snd z1" using \<open>polychain (z1 # z2 # zs)\<close> unfolding polychain_def
      using \<open>x = x'\<close> by auto  
    obtain z3 and zs' where disj:"zs = z3 # zs' \<or> zs = []" by (meson last_in_set list.set_cases) 
    from \<open>x \<noteq> fst (hd (z1 # z2 # zs))\<close> \<open>x \<noteq> snd (last (z1 # z2 # zs))\<close> \<open>x \<noteq> snd z1\<close>
      have "zs \<noteq> []" 
        by (metis \<open>convex_hull_vertex3 (z2 # zs) = Some x'\<close> \<open>x = x'\<close> case_three(3) 
            convex_hull_vertex3.simps(2) last.simps last_ConsR list.simps(3) min2D_D2 nth_Cons_0 
            option.inject polychain_Cons)
    with disj have cons: "zs = z3 # zs'" by auto          
    from \<open>polychain (z1 # z2 # zs)\<close> have "polychain (z2 # zs)" by (simp add: polychain_Cons)
    from \<open>x \<noteq> snd (last (z1 # z2 # zs))\<close> and \<open>x = x'\<close> have neq: "x' \<noteq> snd (last (z2 # zs))" 
      by auto    
    from cons case_three(1)[OF _ \<open>polychain (z2 # zs)\<close> \<open>convex_hull_vertex3 (z2#zs) = Some x'\<close>] 2 neq
    obtain pp' where "pre_and_post_betw (z2 # zs) x' = Some pp'" by auto
    with \<open>x \<noteq> snd z1\<close> \<open>x = x'\<close> show ?thesis  by fastforce
  qed      
qed    
    
theorem pre_pos_convex_hull_vertex:
  assumes "2 \<le> length zs"
  assumes "polygon zs"    
  assumes "convex_hull_vertex3 zs = Some x"
  shows "\<exists>pp. pre_and_post zs x = Some pp"
proof (cases "x = fst (hd zs)")
  case False
  hence False':"x \<noteq> snd (last zs)" using \<open>polygon zs\<close> assms(1) unfolding polygon_def by auto  
  from assms(2) have "polychain zs" unfolding polygon_def by auto  
  from assms(1) obtain z1 and z2 and zs' where "zs = z1 # z2 # zs'" 
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right last_in_set 
        le_imp_less_Suc length_Cons less_Suc0 list.set_cases list.size(3) nat.simps(3) 
        one_add_one order_less_irrefl)  
  hence eq:"pre_and_post zs x = pre_and_post_betw zs x" using False by auto
  from pre_post_betw_convex_hull_vertex[OF assms(1) \<open>polychain zs\<close> assms(3)]
  obtain pp' where "pre_and_post_betw zs x = Some pp'" using False False' by auto
  with eq show ?thesis by fastforce
next
  case True
  from assms(1) obtain z1 and z2 and zs' where "zs = z1 # z2 # zs'" 
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right last_in_set 
        le_imp_less_Suc length_Cons less_Suc0 list.set_cases list.size(3) nat.simps(3) 
        one_add_one order_less_irrefl)   
  with True have "pre_and_post zs x = Some (fst (last (z2 # zs')), snd z1)" by auto      
  thus ?thesis by auto
qed    
  
text \<open>Two auxiliary lemmas for polychain.\<close>  

theorem polychain_snoc:
  assumes "polychain xs"
  assumes "snd (last xs) = fst a"
  shows "polychain (xs @ [a])"
  using assms by (simp add: polychain_appendI)  
      
theorem polychain_rev_map:
  assumes "polychain xs"
  shows "polychain (rev (map (\<lambda>(x,y). (y,x)) xs))"
  using assms  
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  note case_cons = this
  hence "polychain xs" by (metis polychain_Cons polychain_Nil)
  with case_cons have 0: "polychain (rev (map (\<lambda>(x,y). (y,x)) xs))" by auto
  obtain x and xs' where "xs = [] \<or> xs = x # xs'" by (meson last_in_set list.set_cases)    
  moreover
  { assume "xs = []"
    hence ?case by auto }
  moreover
  { assume "xs = x # xs'"
    with \<open>polychain (a # xs)\<close> have "snd a = fst (hd xs)" unfolding polychain_def by auto      
    have 1: "rev (map (\<lambda>(x,y). (y,x)) (a # xs)) = rev (map (\<lambda>(x,y). (y,x)) xs) @ [(snd a, fst a)]"
      by (metis (no_types, lifting) case_prod_conv list.simps(9) prod.collapse rev_eq_Cons_iff 
                                                                                           rev_swap)
    have "polychain (rev (map (\<lambda>(x, y). (y, x)) xs) @ [(snd a, fst a)])" 
    proof (intro polychain_snoc)
      show "polychain (rev (map (\<lambda>(x, y). (y, x)) xs))" using 0 .
    next
      from \<open>xs = x # xs'\<close> have "xs \<noteq> []" by auto
      hence "snd (last (rev (map (\<lambda>(x,y). (y,x)) xs))) = fst (hd xs)"
        by (simp add: assms hd_map last_rev prod.case_eq_if)
      with \<open>snd a = fst (hd xs)\<close> 
        show " snd (last (rev (map (\<lambda>(x, y). (y, x)) xs))) = fst (snd a, fst a)"
        by auto
    qed 
    hence "polychain (rev (map (\<lambda>a. case a of (x, y) \<Rightarrow> (y, x)) (a # xs)))" 
      using 1 by auto
  }
  ultimately show ?case by auto   
qed   

text "Connecting two polychains"

(*
        xs
    *--<--*---<--*
    |
    | add a path
    |
    *-->--*--->--*
        ys
*)  
  
definition connect_polychain :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list"
  where 
  "connect_polychain xs ys \<equiv> (let end1 = snd (last xs); end2 = fst (hd ys) in 
                                         if end1 \<noteq> end2 then xs @ [(end1, end2)] @ ys else xs @ ys)"  

theorem length_connect_polychain:
  "length xs + length ys \<le> length (connect_polychain xs ys)"  
  unfolding connect_polychain_def Let_def 
  by (cases "snd (last xs) \<noteq> fst (hd ys)") (auto)    
  
theorem connect_polychain_preserve:
  assumes "polychain xs"
      and "polychain ys"
  assumes "xs \<noteq> []" 
      and "ys \<noteq> []"        
    shows "polychain (connect_polychain xs ys)"
  using assms 
proof (cases "snd (last xs) \<noteq> fst (hd ys)")
  case True
  hence "connect_polychain xs ys = xs @ [(snd (last xs), fst (hd ys))] @ ys" 
    unfolding connect_polychain_def by auto
  have "polychain ([(snd (last xs), fst (hd ys))] @ ys)" 
    by (rule polychain_appendI)(auto simp add:assms)
  hence "polychain (xs @ [(snd (last xs), fst (hd ys))] @ ys)" 
    by (auto intro:polychain_appendI simp add:assms)
  then show ?thesis unfolding connect_polychain_def Let_def using True by auto
next
  case False
  then show ?thesis unfolding connect_polychain_def Let_def using False 
    by (auto intro:polychain_appendI simp add:assms)
qed    
  
theorem connect_polychain_nonempty:
  assumes "polychain xs"
  assumes "polychain ys"
  assumes "xs \<noteq> []" 
  assumes "ys \<noteq> []"
  shows "connect_polychain xs ys \<noteq> []"
  using assms unfolding connect_polychain_def Let_def by auto
      
(*
        xs
    *--<--*---<---*
    |             |
    | make a loop |
    |             |
    *-->--*--->---*
        ys
*)  
  
definition close_polychain :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list" where
  "close_polychain xs \<equiv> (let end1 = fst (hd xs); end2 = snd (last xs) in 
                                                   if end1 \<noteq> end2 then xs @ [(end2, end1)] else xs)"

theorem length_close_polychain:
  "length xs \<le> length (close_polychain xs)"
  unfolding close_polychain_def Let_def
  by (cases "fst (hd xs) \<noteq> snd (last xs)") (auto)  
        
theorem polychain_close_polychain: 
  assumes "xs \<noteq> []"
  assumes "polychain xs"  
  shows "polychain (close_polychain xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  note case_cons = this    
  show ?case unfolding close_polychain_def Let_def if_splits
  proof (rule conjI, rule_tac[!] impI)
    show "polychain ((a # xs) @ [(snd (last (a # xs)), fst (hd (a # xs)))])"      
      by (intro polychain_appendI)(auto simp add:case_cons)      
  next
    from case_cons show "polychain (a # xs)" by auto    
  qed    
qed
        
theorem polygon_close_polychain:
  assumes "xs \<noteq> []"
  assumes "polychain xs"
  shows "polygon (close_polychain xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  note case_cons = this  
  show ?case unfolding close_polychain_def Let_def if_splits
  proof (rule conjI, rule_tac[!] impI)
    assume True:"fst (hd (a # xs)) \<noteq> snd (last (a # xs))"
    from polychain_close_polychain[OF case_cons(2-3)] have "polychain (close_polychain (a # xs))" .
    thus " polygon ((a # xs) @ [(snd (last (a # xs)), fst (hd (a # xs)))])"
      unfolding close_polychain_def Let_def polygon_def using True by auto
  next
    assume "\<not> fst (hd (a # xs)) \<noteq> snd (last (a # xs))"
    thus "polygon (a # xs)" using \<open>polychain (a # xs)\<close> unfolding polygon_def using \<open>a # xs \<noteq> []\<close>
      by auto
  qed    
qed
  
subsubsection "Auxiliary functions for point-in-drivable-area test"  
         
fun find_segment :: "(real2 \<times> real2) list \<Rightarrow> real \<Rightarrow> (real2 \<times> real2) option" where
  "find_segment [] x       = None" | 
  "find_segment (c # cs) x = (if fst (fst c) \<le> x \<and> x \<le> fst (snd c) then Some c 
                              else find_segment cs x)" 

theorem find_segment_correctness:
  assumes "cs \<noteq> []"
  assumes "monotone_polychain cs"  
  assumes "fst (fst (hd cs)) < x" and "x < fst (snd (last cs))"
  shows "\<exists>end1 end2. find_segment cs x = Some (end1, end2) \<and> List.member cs (end1, end2) \<and> 
                                         fst end1 \<le> x \<and> x \<le> fst end2"
  using assms
proof (induction cs)
  case Nil
  then show ?case by auto
next
  case (Cons a cs)
  note case_cons = this
  from \<open>monotone_polychain (a # cs)\<close> have "monotone_polychain cs" using monotone_polychain_ConsD
    by auto      
  obtain a' cs' where "cs = [] \<or> cs = a' # cs'"  using list.exhaust_sel by blast
  moreover
  { assume "cs = []"
    with case_cons have "find_segment (a # cs) x = Some (fst a, snd a) \<and> List.member (a # cs) a \<and> 
                                    fst (fst a) \<le> x \<and> x \<le> fst (snd a)"
      by (auto simp add: List.member_rec)
    hence "\<exists>end1 end2. find_segment (a # cs) x = Some (end1, end2) \<and> List.member (a # cs) (end1, end2) \<and> 
                                fst end1 \<le> x \<and> x \<le> fst end2"
      by (metis prod.collapse) }
  
  moreover
  { assume "cs = a' # cs'"
    consider "fst (fst a) \<le> x \<and> x \<le> fst (snd a)" | "\<not> (fst (fst a) \<le> x \<and> x \<le> fst (snd a))" by auto
    hence "\<exists>end1 end2. find_segment (a # cs) x = Some (end1, end2) \<and> List.member (a # cs) (end1, end2) \<and> 
                                fst end1 \<le> x \<and> x \<le> fst end2"
    proof (cases)
      case 1
      then show ?thesis by (metis find_segment.simps(2) member_rec(1) prod.collapse)
    next
      case 2
      hence "x < (fst (fst a)) \<or> fst (snd a) < x" by auto
      with case_cons(4) have "fst (snd a) < x" by auto
      from \<open>monotone_polychain (a # cs)\<close> \<open>cs = a' # cs'\<close>  have "snd a = fst a'"
        unfolding monotone_polychain_def polychain_def by auto
      with \<open>fst (snd a) < x\<close> and \<open>cs = a' # cs'\<close> have 0: "fst (fst (hd cs)) < x" by auto
      from case_cons(5) and \<open>cs = a' # cs'\<close> have 1: "x < fst (snd (last cs))" by auto
      with case_cons(1)[OF _ \<open>monotone_polychain cs\<close> 0 1] and \<open>cs = a' # cs'\<close> show ?thesis 
        using 2 by (metis calculation(2) find_segment.simps(2) member_rec(1))
    qed }      
  ultimately show ?case by auto 
qed    
      
fun above_and_inside_polychains :: "(real2 \<times> real2) list \<Rightarrow> real2 \<Rightarrow> bool" where
  "above_and_inside_polychains [] p = False" | 
  "above_and_inside_polychains cs p = 
                           (if fst p \<le> fst (fst (hd cs)) \<or> fst p \<ge> fst (snd (last (cs))) then False 
                            else (case find_segment cs (fst p) of 
                                                            Some (end1, end2) \<Rightarrow> ccw' p end1 end2))"
  
theorem above_inside_poly_correctness1:
  assumes "above_and_inside_polychains cs p"
  shows "fst p \<in> {fst (fst (hd cs)) <..< fst (snd (last cs))}"    
proof -
  from assms have "cs \<noteq> []" by auto  
  with assms have "\<not> (fst p \<le> fst (fst (hd cs)) \<or> fst p \<ge> fst (snd (last (cs))))"
    using above_and_inside_polychains.elims(2) by fastforce
  thus ?thesis by auto    
qed
    
theorem ccw_ray_downwards:
  assumes ccw: "ccw' p end1 end2"
  assumes "fst end1 < fst end2"    
  shows "line_equation end1 end2 (fst p) < snd p"  
proof -
  from ccw have "det3 0 (end1 - p) (end2 - p) > 0" unfolding ccw'_def using det3_translate_origin 
    by auto
  hence "fst (end2 - p) * snd (end1 - p) + fst (p - end1) * snd (end2 - p) < 0" 
    (is " ?t1 * ?t2 + ?t3 * ?t4 < 0") unfolding det3_def' by (auto simp add:algebra_simps)
  hence "fst end2 * ?t2 - fst p * snd end1 + snd end2 * ?t3 + snd p * fst end1 < 0"
    (is " ?s < 0") by (auto simp add:algebra_simps)
  hence " ?s + fst end1 * snd end1 - fst end1 * snd end1 < 0"
    by auto
  hence "snd (end2 - end1) * fst (p - end1) + snd (end1 - p) * fst (end2 - end1) < 0"
    (is " ?u < 0") by (auto simp add:algebra_simps)
  hence "?u / fst (end2 - end1) < 0" by (simp add: assms(2) divide_neg_pos)
  hence "snd (end2 - end1) / fst (end2 - end1) *  fst (p - end1) + snd end1 <  snd p"
    using assms(2) by (auto simp add:divide_simps algebra_simps)
  thus ?thesis unfolding line_equation_def by auto              
qed
    
theorem above_inside_poly_correctness2:
  assumes "monotone_polychain cs"
  assumes "above_and_inside_polychains cs p"
  shows "\<exists>chain. List.member cs chain \<and> fst (fst chain) \<le> fst p \<and> fst p \<le> fst (snd chain) \<and> 
                                              line_equation (fst chain) (snd chain) (fst p) < snd p"    
proof -
  from assms(2) have nonempty: "cs \<noteq> []" by auto
  from assms(2) have range: "fst (fst (hd cs)) <  fst p \<and> fst p < fst (snd (last cs))"  
    using above_inside_poly_correctness1 by auto
  with find_segment_correctness[OF nonempty assms(1)] obtain end1 end2 where 
    0: "find_segment cs (fst p) = Some (end1, end2)" and 
    1: "List.member cs (end1, end2)" and
    2: "fst end1 \<le> (fst p) \<and> (fst p) \<le> fst end2" by blast
  with assms(2) and range have ccw: "ccw' p end1 end2" using above_and_inside_polychains.elims(2) 
    by fastforce
  from 1 have "(end1, end2) \<in> set cs" unfolding member_def by auto
  then obtain i where "i < length cs \<and> cs ! i = (end1, end2)" unfolding in_set_conv_nth by auto
  with \<open>monotone_polychain cs\<close> have "fst end1 < fst end2" unfolding monotone_polychain_def
    by auto
  from ccw_ray_downwards[OF ccw this] have "line_equation end1 end2 (fst p) < snd p" .     
  with 0 1 2 show ?thesis by (metis fst_conv snd_conv)
qed
  
        
fun below_and_inside_polychains :: "(real2 \<times> real2) list \<Rightarrow> real2 \<Rightarrow> bool" where
  "below_and_inside_polychains [] p = False" | 
  "below_and_inside_polychains cs p = 
                           (if fst p \<le> fst (fst (hd cs)) \<or> fst p \<ge> fst (snd (last (cs))) then False 
                            else (case find_segment cs (fst p) of 
                                                            Some (end1, end2) \<Rightarrow> det3 p end1 end2 < 0))"    

(* TODO: prove correctness of this function *)

(* polygonal chain intersection *)

(* intersects two line segments *)  
fun intersect :: "(real2 \<times> real2) \<Rightarrow> (real2 \<times> real2) \<Rightarrow> real2 option" where
  "intersect line1 line2 = undefined"

abbreviation intersect' :: "(real2 \<times> real2) \<Rightarrow> (real2 \<times> real2) \<Rightarrow> real2 list" where
  "intersect' line1 line2 \<equiv> (case intersect line1 line2 of None \<Rightarrow> []
                                                         | Some x \<Rightarrow> [x])"
    
(* intersection is a point on both lines *)
lemma intersect_some_imp_intersection:
  assumes "intersect line1 line2 = Some x"
  shows "\<exists>t \<in> {0..1}. linepath (fst line1) (snd line1) t = x"
    and "\<exists>t \<in> {0..1}. linepath (fst line2) (snd line2) t = x"
  sorry

lemma intersection_imp_intersect_some:
  assumes "\<exists>t \<in> {0..1}. linepath (fst line1) (snd line1) t = x"
  assumes "\<exists>t \<in> {0..1}. linepath (fst line2) (snd line2) t = x"
  shows "intersect line1 line2 = Some x"
  sorry
    
lemma intersect_none:
  assumes "intersect line1 line2 = None"
  shows "\<forall>t \<in> {0..1}. \<forall>t' \<in> {0..1}. linepath (fst line1) (snd line1) t \<noteq> linepath (fst line2) (snd line2) t'"
  sorry

(* intersects two lanes *)
fun intersect_lanes' :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) option \<Rightarrow> (real2 \<times> real2) option \<Rightarrow> real2 list" where
  "intersect_lanes' [] [] (Some l') (Some r') = intersect' l' r'"
| "intersect_lanes' [] _ None _ = []"
| "intersect_lanes' [] (r # ri) (Some l') (Some r') = (intersect' l' r') @ (intersect_lanes' [] ri (Some l') (Some r))"
| "intersect_lanes' [] (r # ri) (Some l') None = intersect_lanes' [] ri (Some l') (Some r)"  
| "intersect_lanes' _ [] _ None = []"
| "intersect_lanes' (l # le) [] (Some l') (Some r') = (intersect' l' r') @ (intersect_lanes' le [] (Some l) (Some r'))"
| "intersect_lanes' (l # le) [] None (Some r') = intersect_lanes' le [] (Some l) (Some r')"
| "intersect_lanes' (l # le) (r # ri) None None = (if fst (fst l) \<le> fst (fst r)
    then intersect_lanes' le (r # ri) (Some l) None
    else intersect_lanes' (l # le) ri None (Some r))"
| "intersect_lanes' (l # le) (r # ri) None (Some r') = (if fst (fst l) \<le> fst (fst r)
    then intersect_lanes' le (r # ri) (Some l) (Some r')
    else intersect_lanes' (l # le) ri None (Some r))"
| "intersect_lanes' (l # le) (r # ri) (Some l') None = (if fst (fst l) \<le> fst (fst r)
    then intersect_lanes' le (r # ri) (Some l) None
    else intersect_lanes' (l # le) ri (Some l') (Some r))" 
| "intersect_lanes' (l # le) (r # ri) (Some l') (Some r') = (if fst (fst l) \<le> fst (fst r)
    then (intersect' l' r') @ (intersect_lanes' le (r # ri) (Some l) (Some r'))
    else (intersect' l' r') @ (intersect_lanes' (l # le) ri (Some l') (Some r)))" 

fun intersect_lanes :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> real2 list" where
  "intersect_lanes le ri = intersect_lanes' le ri None None"
  
locale generalized_lanelet = le: lanelet_simple_boundary points_le + ri: lanelet_simple_boundary points_ri
  for points_le and points_ri
begin

lemma
  assumes "fst (p :: real2 \<times> real2) < snd p"
  assumes "fst q < snd q"
  assumes "fst (fst p) > fst (snd q)"
  assumes "t \<in> {0..1}"
  assumes "t' \<in> {0..1}"
  shows "linepath (fst p) (snd p) t \<noteq> linepath (fst q) (snd q) t'"
proof -
  have "fst (linepath (fst q) (snd q) t') = fst ((1 - t') *\<^sub>R fst q + t' *\<^sub>R snd q)" unfolding linepath_def by auto
  also have "\<dots> \<le> fst (snd q)" sorry
  also have "\<dots> < fst (fst p)" using assms by auto
  also have "\<dots> \<le> fst (linepath (fst p) (snd p) t)" sorry
  finally show "linepath (fst p) (snd p) t \<noteq> linepath (fst q) (snd q) t'" by auto
qed
  
theorem non_intersecting_iff_line_segments_non_intersecting:
  "(\<forall>t \<in> {0..1}. \<forall>t' \<in> {0..1}. le.curve_eq t \<noteq> ri.curve_eq t') \<longleftrightarrow> (\<forall>i < length points_le. \<forall>i' < length points_ri. \<forall>t \<in> {0..1}. \<forall>t' \<in> {0..1}. linepath (fst (points_le ! i)) (snd (points_le ! i)) t \<noteq> linepath (fst (points_ri ! i')) (snd (points_ri ! i')) t')"
proof -
  have "(\<exists>t \<in> {0..1}. \<exists>t' \<in> {0..1}. le.curve_eq t = ri.curve_eq t') \<longleftrightarrow> (\<exists>i < length points_le. \<exists>i' < length points_ri. \<exists>t \<in> {0..1}. \<exists>t' \<in> {0..1}. linepath (fst (points_le ! i)) (snd (points_le ! i)) t = linepath (fst (points_ri ! i')) (snd (points_ri ! i')) t')"
  proof
    assume "\<exists>t \<in> {0..1}. \<exists>t' \<in> {0..1}. le.curve_eq t = ri.curve_eq t'"
    then obtain t t' where *: "t \<in> {0..1}" "t' \<in> {0..1}" "le.curve_eq t = ri.curve_eq t'" by auto
    have "\<exists>i < length points_le. \<exists>t' \<in> {0..1}. le.curve_eq t = linepath (fst (points_le ! i)) (snd (points_le ! i)) t'"
      using le.curve_eq_imp_linepath[of t] * by auto
    moreover have "\<exists>i < length points_ri. \<exists>t'' \<in> {0..1}. ri.curve_eq t' = linepath (fst (points_ri ! i)) (snd (points_ri ! i)) t''"
      using ri.curve_eq_imp_linepath[of t'] * by auto
    ultimately show "\<exists>i < length points_le. \<exists>i' < length points_ri. \<exists>t \<in> {0..1}. \<exists>t' \<in> {0..1}. linepath (fst (points_le ! i)) (snd (points_le ! i)) t = linepath (fst (points_ri ! i')) (snd (points_ri ! i')) t'"
      using * by metis
  next
    assume "\<exists>i < length points_le. \<exists>i' < length points_ri. \<exists>t \<in> {0..1}. \<exists>t' \<in> {0..1}. linepath (fst (points_le ! i)) (snd (points_le ! i)) t = linepath (fst (points_ri ! i')) (snd (points_ri ! i')) t'"
    then obtain i i' t t' where *: "i < length points_le" "i' < length points_ri" "t \<in> {0..1}" "t' \<in> {0..1}" "linepath (fst (points_le ! i)) (snd (points_le ! i)) t = linepath (fst (points_ri ! i')) (snd (points_ri ! i')) t'"
      by auto
    have "\<exists>t' \<in> {0..1}. le.curve_eq t' = linepath (fst (points_le ! i)) (snd (points_le ! i)) t"
      using le.linepath_imp_curve_eq[of i t] * by auto
    moreover have "\<exists>t \<in> {0..1}. ri.curve_eq t = linepath (fst (points_ri ! i')) (snd (points_ri ! i')) t'"
      using ri.linepath_imp_curve_eq[of i' t'] * by auto
    ultimately show "\<exists>t \<in> {0..1}. \<exists>t' \<in> {0..1}. le.curve_eq t = ri.curve_eq t'"
      using * by metis
  qed
  then show ?thesis by auto
qed
  
end

theorem below_inside_poly_correctness1:
  assumes "below_and_inside_polychains cs p"
  shows "fst p \<in> {fst (fst (hd cs)) <..< fst (snd (last cs))}"
proof -
  from assms have "cs \<noteq> []" by auto
  with assms have "\<not> (fst p \<le> fst (fst (hd cs)) \<or> fst p \<ge> fst (snd (last (cs))))"      
    using below_and_inside_polychains.elims(2) by fastforce
  thus ?thesis by auto        
qed  
  
theorem cw_ray_upwards:
  assumes cw: "det3 p end1 end2 < 0"
  assumes "fst end1 < fst end2"
  shows "line_equation end1 end2 (fst p) > snd p"
proof -
  from cw have "det3 0 (end1 - p) (end2 - p) < 0" using det3_translate_origin by auto
  hence "fst (end2 - p) * snd (end1 - p) + fst (p - end1) * snd (end2 - p) > 0" 
    (is " ?t1 * ?t2 + ?t3 * ?t4 > 0") unfolding det3_def' by (auto simp add:algebra_simps)
  hence "fst end2 * ?t2 - fst p * snd end1 + snd end2 * ?t3 + snd p * fst end1 > 0"
    (is " ?s > 0") by (auto simp add:algebra_simps)
  hence " ?s + fst end1 * snd end1 - fst end1 * snd end1 > 0"
    by auto
  hence "snd (end2 - end1) * fst (p - end1) + snd (end1 - p) * fst (end2 - end1) > 0"
    (is " ?u > 0") by (auto simp add:algebra_simps)
  hence "?u / fst (end2 - end1) > 0" by (simp add: assms(2) divide_neg_pos)
  hence "snd (end2 - end1) / fst (end2 - end1) *  fst (p - end1) + snd end1 >  snd p"
    using assms(2) by (auto simp add:divide_simps algebra_simps)
  thus ?thesis unfolding line_equation_def by auto 
qed
    
theorem below_inside_poly_correctness2:
  assumes "monotone_polychain cs"
  assumes "below_and_inside_polychains cs p"
  shows "\<exists>chain. List.member cs chain \<and> fst (fst chain) \<le> fst p \<and> fst p \<le> fst (snd chain) \<and> 
                        line_equation (fst chain) (snd chain) (fst p) > snd p"
proof -
  from assms(2) have nonempty: "cs \<noteq> []" by auto
  from assms(2) have range: "fst (fst (hd cs)) <  fst p \<and> fst p < fst (snd (last cs))"  
    using below_inside_poly_correctness1 by auto
  with find_segment_correctness[OF nonempty assms(1)] obtain end1 end2 where 
    0: "find_segment cs (fst p) = Some (end1, end2)" and 
    1: "List.member cs (end1, end2)" and
    2: "fst end1 \<le> (fst p) \<and> (fst p) \<le> fst end2" by blast
  with assms(2) and range have cw: "det3 p end1 end2 < 0" using below_and_inside_polychains.elims(2) 
    by fastforce
  from 1 have "(end1, end2) \<in> set cs" unfolding member_def by auto
  then obtain i where "i < length cs \<and> cs ! i = (end1, end2)" unfolding in_set_conv_nth by auto
  with \<open>monotone_polychain cs\<close> have "fst end1 < fst end2" unfolding monotone_polychain_def
    by auto
  from cw_ray_upwards[OF cw this] have "line_equation end1 end2 (fst p) > snd p" .      
  with 0 1 2 show ?thesis by (metis fst_conv snd_conv)
qed  
  
subsubsection "Line intersection"
  
definition points_in_lines :: "real2 \<Rightarrow> real2 \<Rightarrow> real2 set" where
  "points_in_lines p1 p2 \<equiv> (let a = snd p2 - snd p1; b = fst p1 - fst p2;
                                 c = fst p1 * snd p2 - fst p2 * snd p1 in 
                            {(x,y). a * x + b * y = c})"
    
theorem line_equation_pil:
  assumes "fst p1 \<noteq> fst p2" (* no vertical lines *)
  assumes "line_equation p1 p2 x = y"
  shows "(x, y) \<in> points_in_lines p1 p2"  
  unfolding points_in_lines_def Let_def mem_Collect_eq
proof 
  from assms(1) have "fst p2 - fst p1 \<noteq> 0" by auto
  from assms(2) have "y = (snd p2 - snd p1) / (fst p2 - fst p1) * x - (snd p2 - snd p1) / (fst p2 - fst p1) * fst p1 + snd p1"
    (is "y = ?num / ?denum * x - ?num / ?denum * ?c1 + ?c2")
    using line_equation_alt_def by auto  
  hence "y * ?denum = ?num * x - ?num * ?c1 + ?c2 * ?denum" using `fst p2 - fst p1 \<noteq> 0`
    by (auto simp add:divide_simps)
  thus " (snd p2 - snd p1) * x + (fst p1 - fst p2) * y = fst p1 * snd p2 - fst p2 * snd p1"  
    by (auto simp add:algebra_simps)
qed
    
theorem line_equation_pil2: 
  assumes "fst p1 \<noteq> fst p2"
  assumes "line_equation p1 p2 x \<noteq> y"
  shows "(x,y) \<notin> points_in_lines p1 p2"
  unfolding points_in_lines_def Let_def mem_Collect_eq  
proof (split prod.split, rule allI, rule allI, rule impI)
  fix x1 x2
  assume "(x, y) = (x1, x2)"
  hence "x = x1" and "y = x2" by auto
  from assms show "(snd p2 - snd p1) * x1 + (fst p1 - fst p2) * x2 \<noteq> fst p1 * snd p2 - fst p2 * snd p1"   
    unfolding line_equation_def `x = x1` `y = x2` by (auto simp add:algebra_simps divide_simps)          
qed
    
theorem closed_segment_subset_pil: 
  "closed_segment p1 p2 \<subseteq> points_in_lines p1 p2"  
proof (rule subsetI, rename_tac "p")
  fix p
  assume "p \<in> closed_segment p1 p2"
  with in_segment(1) obtain u where "p = (1 - u) *\<^sub>R p1 + u *\<^sub>R p2" and "0 \<le> u" and "u \<le> 1" by blast
  hence x_comp: "fst p = (1 - u) * fst p1 + u * fst p2" (is "?xlhs = ?xrhs")and 
        y_comp: "snd p = (1 - u) * snd p1 + u * snd p2" (is "?ylhs = ?yrhs ")by auto
  have "(fst p, snd p) \<in> points_in_lines p1 p2"
    unfolding points_in_lines_def Let_def mem_Collect_eq
  proof      
    from x_comp have 0: "(snd p2 - snd p1) * ?xlhs = (snd p2 - snd p1) * ?xrhs" by auto
    from y_comp have "(fst p1 - fst p2) * ?ylhs = (fst p1 - fst p2) * ?yrhs" by auto      
    with 0 show "(snd p2 - snd p1) * fst p + (fst p1 - fst p2) * snd p = fst p1 * snd p2 - fst p2 * snd p1"    
      by (auto simp add:algebra_simps)      
  qed
  thus "p \<in> points_in_lines p1 p2" by auto      
qed
      
theorem pil_also_closed_segment: 
  assumes "p \<in> points_in_lines p1 p2"
  assumes "(fst p) \<in> closed_segment (fst p1) (fst p2)"
  assumes "fst p1 \<noteq> fst p2"  
  shows "p \<in> closed_segment p1 p2"
proof -
  define a where "a \<equiv>  snd p2 - snd p1" 
  define b where "b \<equiv> fst p1 - fst p2"
  define c where "c \<equiv> fst p1 * snd p2 - fst p2 * snd p1"
  note coeffs = a_def b_def c_def
  from assms(3) have "b \<noteq> 0" unfolding coeffs by auto
  from assms(1) have "a * fst p + b * snd p = c" unfolding points_in_lines_def Let_def coeffs
    by auto
  have "p1 \<in> points_in_lines p1 p2"  unfolding points_in_lines_def Let_def coeffs 
    by (auto simp add:algebra_simps)     
  hence "a * fst p1 + b * snd p1 = c" unfolding points_in_lines_def Let_def coeffs by auto
  have "p2 \<in> points_in_lines p1 p2"  unfolding points_in_lines_def Let_def coeffs 
    by (auto simp add:algebra_simps)     
  hence "a * fst p2 + b * snd p2 = c" unfolding points_in_lines_def Let_def coeffs by auto
  with `a * fst p1 + b * snd p1 = c` have "a * (fst p2 - fst p1) = b * (snd p1 - snd p2)"
    by (auto simp add:algebra_simps)
  from assms(2) obtain t where "fst p = fst p1 + t * (fst p2 - fst p1)"
    and "fst p = (1 - t) * fst p1 + t * fst p2" and "0 \<le> t" and "t \<le> 1"
    unfolding closed_segment_def by (auto simp add:field_simps)
  with `a * fst p + b * snd p = c`
  have "a * (fst p1 + t * (fst p2 - fst p1)) + b * snd p = c" by auto
  hence "a * fst p1 + a * t * (fst p2 - fst p1) + b * snd p = c" by (auto simp add:algebra_simps)
  hence "a * t * (fst p2 - fst p1) + b * snd p = b * snd p1" using `a * fst p1 + b * snd p1 = c`
    by auto
  with `a * (fst p2 - fst p1) = b * (snd p1 - snd p2)`
  have "t * b * (snd p1 - snd p2) + b * snd p = b * snd p1" 
    by (metis mult.assoc mult.left_commute)
  hence "b * (t * (snd p1 - snd p2) + snd p) = b * snd p1"
    by (auto simp add:algebra_simps)
  hence "(t * (snd p1 - snd p2) + snd p) = snd p1" using `b \<noteq> 0` by auto
  hence "snd p = snd p1 + t * (snd p2 - snd p1)" by (auto simp add:algebra_simps)
  have "p = p1 + t *\<^sub>R (p2 - p1)"
  proof -
    from `snd p = snd p1 + t * (snd p2 - snd p1)` and `fst p = fst p1 + t * (fst p2 - fst p1)`    
    have "(fst p, snd p) = (fst p1 + t * (fst p2 - fst p1), snd p1 + t * (snd p2 - snd p1))"
      by auto
    also have "... = (fst p1, snd p1) + (t * (fst p2 - fst p1), t * (snd p2 - snd p1))"
      using add_Pair by metis
    also have "... = (fst p1, snd p1) + t*\<^sub>R (fst p2 - fst p1, snd p2 - snd p1)"
      by (auto simp add:field_simps)
    also have "... = (fst p1, snd p1) + t *\<^sub>R ((fst p2, snd p2) - (fst p1, snd p1))"  
      using diff_Pair by metis
    also have "... = p1 + t*\<^sub>R (p2 - p1)" using surjective_pairing by auto
    finally show ?thesis using surjective_pairing by metis    
  qed
  hence "p = (1 - t) *\<^sub>R p1 + t*\<^sub>R p2"
  proof -
    have "\<forall>x1. (1::real) - x1 = 1 + - 1 * x1"
      by auto
    then have "p = t *\<^sub>R p2 - t *\<^sub>R p1 + (t *\<^sub>R p1 + (1 + - 1 * t) *\<^sub>R p1)"
      by (metis (no_types) \<open>p = p1 + t *\<^sub>R (p2 - p1)\<close> add.commute real_vector.scale_right_diff_distrib scaleR_collapse)
    then show ?thesis
      by simp
  qed  
  thus ?thesis  using `0 \<le> t` and `t \<le> 1` unfolding closed_segment_def by auto
qed
  
lemma surjective_closed_segment:     
  fixes p p1 p2 :: "real2"  
  assumes "fst p = (1 - t) * fst p1 + t * fst p2"
  assumes "snd p = (1 - t) * snd p1 + t * snd p2"
  shows "p = (1 - t) *\<^sub>R p1 + t *\<^sub>R p2"
proof -
  from assms(1) have 0: "fst p = fst p1 + t * (fst p2 -fst p1)" by (auto simp add:algebra_simps)
  from assms(2) have 1: "snd p = snd p1 + t * (snd p2 -snd p1)" by (auto simp add:algebra_simps)
  have "(fst p, snd p) = (fst p1 + t * (fst p2 - fst p1), snd p1 + t * (snd p2 - snd p1))"
    using 0 1 by auto
  also have "... = (fst p1, snd p1) + (t * (fst p2 - fst p1), t * (snd p2 - snd p1))"
    using add_Pair by metis
  also have "... = (fst p1, snd p1) + t*\<^sub>R (fst p2 - fst p1, snd p2 - snd p1)"
    by (auto simp add:field_simps)
  also have "... = (fst p1, snd p1) + t *\<^sub>R ((fst p2, snd p2) - (fst p1, snd p1))"  
    using diff_Pair by metis
  also have "... = p1 + t*\<^sub>R (p2 - p1)" using surjective_pairing by auto
  also have "... = (1 - t) *\<^sub>R p1 + t *\<^sub>R p2"
  proof -
    have f1: "1 + - 1 * (1 + - 1 * t) = t"
      by simp
    have "\<forall>x1. (1::real) - x1 = 1 + - 1 * x1"
      by auto
    then have "t *\<^sub>R p2 - t *\<^sub>R p1 + (t *\<^sub>R p1 + (1 + - 1 * t) *\<^sub>R p1) = t *\<^sub>R (p2 - p1) + p1"
      using f1 by (metis (no_types) real_vector.scale_right_diff_distrib scaleR_collapse)
    then show ?thesis
      by (simp add: add.commute)
  qed
  finally show ?thesis by auto  
qed
    
theorem pil_also_closed_segment_y: 
  assumes "p \<in> points_in_lines p1 p2"
  assumes "snd p \<in> closed_segment (snd p1) (snd p2)"
  assumes "fst p1 = fst p2" 
  assumes "snd p1 \<noteq> snd p2"  
  shows "p \<in> closed_segment p1 p2" 
proof -
  define a where "a \<equiv>  snd p2 - snd p1" 
  define b where "b \<equiv> fst p1 - fst p2"
  define c where "c \<equiv> fst p1 * snd p2 - fst p2 * snd p1"
  note coeffs = a_def b_def c_def
  from assms(3-4) have "b = 0" and "a \<noteq> 0" unfolding coeffs by auto
  from assms(1) have "a * fst p + b * snd p = c" unfolding points_in_lines_def coeffs Let_def by auto
  with `b = 0` have "a * fst p = c" by auto
  with `a \<noteq> 0` have "fst p = c / a" by auto
   
  have "p1 \<in> points_in_lines p1 p2" and "p2 \<in> points_in_lines p1 p2" 
    unfolding points_in_lines_def Let_def by (auto simp add:algebra_simps)
  hence "a * fst p1 + b * snd p1 = c" and "a * fst p2 + b * snd p2 = c" unfolding points_in_lines_def
    Let_def coeffs  by (auto)
  with `b = 0` have "a * fst p1 = c" and "a * fst p2 = c" by auto
  with `a \<noteq> 0` have "fst p1 = c / a" and "fst p2 = c / a" by auto
  with `fst p = c / a` have "fst p = fst p1" and "fst p = fst p2" by auto      
      
  from assms(2) obtain t where "0 \<le> t" and "t \<le> 1" and "snd p = (1 - t) * snd p1 + t * snd p2"
    unfolding closed_segment_def by auto
  from `fst p = fst p1` and `fst p = fst p2` have  "fst p = (1 - t) * fst p1 + t * fst p2"
    by (auto simp add:algebra_simps) 
  with `snd p = (1 - t) * snd p1 + t * snd p2` 
  have "p = (1 - t) *\<^sub>R p1 + t *\<^sub>R p2" using surjective_closed_segment by auto
  thus ?thesis using `0 \<le> t` and `t \<le> 1` unfolding closed_segment_def by auto      
qed
      
fun det2::"real2 \<Rightarrow> real2 \<Rightarrow> real" where "det2 (xp, yp) (xq, yq) = xp * yq - xq * yp"
  
lemma det2_def':
  "det2 p q = fst p * snd q - fst q * snd p"
  by (cases p q rule: prod.exhaust[case_product prod.exhaust[case_product prod.exhaust]]) auto
    
lemma det2_eq_det: "det2 (xa, ya) (xb, yb) =
  det (vector [vector [xa, ya], vector [xb, yb]]::real^2^2)"
  unfolding Determinants.det_def UNIV_2
  by (auto simp: sum_over_permutations_insert
    vector_2 sign_swap_id permutation_swap_id sign_compose)    
      
definition parallel_lines :: "(real2 \<times> real2) \<Rightarrow> real2 \<times> real2 \<Rightarrow> bool" where
  "parallel_lines l1 l2 \<equiv> 
          (let a1 = snd (snd l1) - snd (fst l1); b1 = fst (fst l1) - fst (snd l1);
                        c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1); 
               a2 = snd (snd l2) - snd (fst l2); b2 = fst (fst l2) - fst (snd l2); 
                        c2 = fst (fst l2) * snd (snd l2) - (fst (snd l2) * snd (fst l2))  in
               det2 (a1, b1) (a2, b2) = 0 \<and> det2 (b1, c1) (b2, c2) \<noteq> 0)"

theorem parallel_invariant: 
  assumes "l2' = (snd l2, fst l2)"
  shows "parallel_lines l1 l2 = parallel_lines l1 l2'"
  using assms   unfolding parallel_lines_def Let_def by (auto simp add:algebra_simps)
    
theorem parallel_commute:
  "parallel_lines l1 l2 = parallel_lines l2 l1"
  unfolding parallel_lines_def Let_def by (auto simp add:algebra_simps)
    
theorem parallel_invariant':
  assumes "l1' = (snd l1, fst l1)"
  shows "parallel_lines l1 l2 = parallel_lines l1' l2"
  using assms parallel_commute parallel_invariant  by blast 
    
theorem parallel_invariant2: 
  assumes "l1' = (snd l1, fst l1)"
  assumes "l2' = (snd l2, fst l2)"
  shows "parallel_lines l1 l2 = parallel_lines l1' l2'"
  using parallel_invariant parallel_invariant' assms by blast   
    
definition not_aligned :: "(real2 \<times> real2) \<Rightarrow> real2 \<times> real2 \<Rightarrow> bool" where
  "not_aligned l1 l2 \<equiv>
          (let a1 = snd (snd l1) - snd (fst l1); b1 = fst (fst l1) - fst (snd l1);
                        c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1); 
               a2 = snd (snd l2) - snd (fst l2); b2 = fst (fst l2) - fst (snd l2); 
                        c2 = fst (fst l2) * snd (snd l2) - (fst (snd l2) * snd (fst l2))  in
              det2 (b1, c1) (b2, c2) \<noteq> 0 \<or> det2 (a1, b1) (a2, b2) \<noteq> 0)"  

theorem not_aligned_invariant:
  assumes "l2' = (snd l2, fst l2)"
  shows "not_aligned l1 l2 = not_aligned l1 l2'"
  using assms unfolding not_aligned_def Let_def by (auto simp add:algebra_simps) 
    
theorem not_aligned_commute:
  "not_aligned l1 l2 = not_aligned l2 l1"
  unfolding not_aligned_def Let_def by (auto simp add:algebra_simps)
    
theorem not_aligned_invariant':
  assumes "l1' = (snd l1, fst l1)"
  shows "not_aligned l1 l2 = not_aligned l1' l2"
  using assms not_aligned_commute not_aligned_invariant by blast    

theorem not_aligned_invariant2: 
  assumes "l1' = (snd l1, fst l1)"
  assumes "l2' = (snd l2, fst l2)"
  shows "not_aligned l1 l2 = not_aligned l1' l2'"
  using not_aligned_invariant not_aligned_invariant' assms by blast   
  
theorem parallel_correctness: 
  assumes "parallel_lines l1 l2"
  shows "points_in_lines (fst l1) (snd l1) \<inter> points_in_lines (fst l2) (snd l2) = {}"
proof (rule ccontr)
  assume "points_in_lines (fst l1) (snd l1) \<inter> points_in_lines (fst l2) (snd l2) \<noteq> {}"
  then obtain p where "p \<in> points_in_lines (fst l1) (snd l1)" and "p \<in> points_in_lines (fst l2) (snd l2)"
    by auto
  then obtain a1 b1 c1 where eq1: "a1 * fst p + b1 * snd p = c1" (is "?lhs1 = ?rhs1") 
    and a1_def: "a1 = snd (snd l1) - snd (fst l1)" 
    and b1_def: "b1 = fst (fst l1) - fst (snd l1)" and c1_def: "c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1)"
    unfolding points_in_lines_def Let_def by auto
  from `p \<in> points_in_lines (fst l2) (snd l2)` obtain a2 b2 c2 where 
    eq2: "a2* fst p + b2 * snd p = c2" (is "?lhs2 = ?rhs2") and a2_def: "a2 = snd (snd l2) - snd (fst l2)" 
    and b2_def: "b2 = fst (fst l2) - fst (snd l2)" and c2_def: "c2 = fst (fst l2) * snd (snd l2) - fst (snd l2) * snd (fst l2)"
    unfolding points_in_lines_def Let_def by auto
  from assms have "det2 (a1, b1) (a2, b2) = 0" and "det2 (b1, c1) (b2, c2) \<noteq> 0" 
    using a1_def b1_def c1_def a2_def b2_def c2_def unfolding parallel_lines_def and 
    not_aligned_def Let_def by auto 
  hence zero: "a1 * b2 = a2 * b1" and nonzero: "b1 * c2 \<noteq> b2 * c1" by auto
  from eq1 eq2 have "?lhs1 * b2 - ?lhs2 * b1 = ?rhs1 * b2 - ?rhs2 * b1" by auto     
  hence "(a1 * b2 - a2 * b1) * fst p = c1 * b2 - c2 * b1" by (auto simp add:algebra_simps)
  with zero and nonzero show "False" by (auto simp add:algebra_simps)           
qed
  
definition overlaps_y :: "real2 \<times> real2 \<Rightarrow> real2 \<times> real2 \<Rightarrow> bool" where
  "overlaps_y l1 l2 \<equiv>  (let i1 = (snd (fst l1), snd (snd l1)); i2 = (snd (fst l2), snd(snd l2));
                          i1' = (min (fst i1) (snd i1), max (fst i1) (snd i1)); 
                          i2' = (min (fst i2) (snd i2), max (fst i2) (snd i2))
                      in (fst i2' \<le> snd i1' \<and> fst i1' \<le> snd i2'))"

theorem overlaps_y_invariant:
  assumes "l2' = (snd l2, fst l2)"
  shows "overlaps_y l1 l2 = overlaps_y l1 l2'"
  using assms unfolding overlaps_y_def Let_def by auto    

theorem overlaps_y_commute:
  "overlaps_y l1 l2 = overlaps_y l2 l1"
  unfolding overlaps_y_def Let_def by auto
    
theorem overlaps_y_invariant':
  assumes "l1' = (snd l1, fst l1)"
  shows "overlaps_y l1 l2 = overlaps_y l1' l2"
  using assms overlaps_y_commute overlaps_y_invariant by blast

theorem overlaps_y_invariant2:
  assumes "l1' = (snd l1, fst l1)"
  assumes "l2' = (snd l2, fst l2)"
  shows "overlaps_y l1 l2 = overlaps_y l1' l2'"
  using assms overlaps_y_invariant overlaps_y_invariant' by blast  
    
lemma nonoverlapping_y:
  assumes "\<not> overlaps_y l1 l2"
  shows "\<not> (\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"    
proof (rule ccontr)
  assume "\<not> (\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"
  then obtain p where pl1: "p \<in> closed_segment (fst l1) (snd l1)" and pl2: "p \<in> closed_segment (fst l2) (snd l2)"
    by auto      
  from pl1 have "snd p \<in> closed_segment (snd (fst l1)) (snd (snd l1))" 
    unfolding closed_segment_def by auto
  hence c1: "snd p \<in> {snd (fst l1) .. snd (snd l1)} \<or> snd p \<in> {snd (snd l1) .. snd (fst l1)}"
    (is "?ran11 \<or> ?ran12")
    using closed_segment_real[of "snd (fst l1)" "snd (snd l1)"] 
    by (cases "snd (fst l1) \<le> snd (snd l1)") (auto)
  from pl2 have "snd p \<in> closed_segment (snd (fst l2)) (snd (snd l2))"
    unfolding closed_segment_def by auto
  hence c2: "snd p \<in> {snd (fst l2) .. snd (snd l2)} \<or> snd p \<in> {snd (snd l2) .. snd (fst l2)}"
    (is "?ran21 \<or> ?ran22")
    using closed_segment_real by (cases "snd (fst l2) \<le> snd (snd l2)") (auto)
  consider "?ran11 \<and> ?ran21" | "?ran11 \<and> ?ran22" | "?ran12 \<and> ?ran21" | "?ran12 \<and> ?ran22"
    using c1 c2 by auto
  thus False
  proof (cases)
    case 1
    hence "snd (fst l1) \<le> snd (snd l1)" and "snd (fst l2) \<le> snd (snd l2)" by auto
    with assms have "\<not> (snd (fst l2) \<le> snd (snd l1) \<and> snd (fst l1) \<le> snd (snd l2))"
      unfolding overlaps_y_def Let_def by auto
    hence "snd (snd l1) < snd (fst l2)  \<or> snd (snd l2) < snd (fst l1)"
      by auto
    with 1 show "False" by auto         
  next
    case 2
    hence "snd (fst l1) \<le> snd (snd l1)" and "snd (snd l2) \<le> snd (fst l2)" by auto
    with assms have "\<not> (snd (snd l2) \<le> snd (snd l1) \<and> snd (fst l1) \<le> snd (fst l2))"
      unfolding overlaps_y_def Let_def by auto
    hence "snd (snd l1) < snd (snd l2) \<or> snd (fst l2) < snd (fst l1)" by auto        
    with 2 show ?thesis by auto
  next
    case 3
    hence "snd (snd l1) \<le> snd (fst l1)" and "snd (fst l2) \<le> snd (snd l2)"  by auto
    with assms have "\<not> (snd (fst l2) \<le> snd (fst l1) \<and> snd (snd l1) \<le> snd (snd l2))"
      unfolding overlaps_y_def Let_def by auto
    hence "snd (fst l1) < snd (fst l2) \<or> snd (snd l2) < snd (snd l1)" by auto        
    with 3 show ?thesis by auto
  next
    case 4
    hence "snd (snd l1) \<le> snd (fst l1)" and "snd (snd l2) \<le> snd (fst l2)" by auto
    with assms have "\<not> (snd (snd l2) \<le> snd (fst l1) \<and> snd (snd l1) \<le> snd (fst l2))"  
      unfolding overlaps_y_def Let_def by auto        
    with 4 show ?thesis by auto
  qed      
qed
    
lemma overlaps_y_closed_segment_case:
  assumes "overlaps_y l1 l2"
  assumes "snd (fst l1) \<le> snd (snd l1)" and "snd (fst l2) \<le> snd (snd l2)"    
  shows "\<exists>p. p \<in> closed_segment (snd (fst l1)) (snd (snd l1)) \<and> p \<in> closed_segment (snd (fst l2)) (snd (snd l2))"
proof -
  from assms have "snd (fst l2) \<le> snd (snd l1)" and "snd (fst l1) \<le> snd (snd l2)"
    unfolding overlaps_y_def Let_def by auto
  consider "snd (fst l1) \<le> snd (fst l2)" | "snd (fst l2) < snd (fst l1)" by linarith
  thus ?thesis
  proof (cases)
    case 1
    define y where "y \<equiv> snd (fst l2)"
    have temp: "y \<in> closed_segment (snd (fst l2)) (snd (snd l2))" unfolding y_def by auto 
    from 1 `snd (fst l2) \<le> snd (snd l1)` have "y \<in> closed_segment (snd (fst l1)) (snd (snd l1))"
      using closed_segment_real assms(2) unfolding y_def by auto
    with temp show ?thesis by auto
  next
    case 2
    define y where "y \<equiv> snd (fst l1)"
    have temp: "y \<in> closed_segment (snd (fst l1)) (snd (snd l1))" unfolding y_def by auto
    from 2 `snd (fst l1) \<le> snd (snd l2)` have "y \<in> closed_segment (snd (fst l2)) (snd (snd l2))"
      using closed_segment_real assms(3) unfolding y_def by auto
    with temp show ?thesis by auto
  qed
qed
      
theorem overlaps_y_closed_segment:
  assumes "overlaps_y l1 l2"                                          
  shows "\<exists>p. p \<in> closed_segment (snd (fst l1)) (snd (snd l1)) \<and> p \<in> closed_segment (snd (fst l2)) (snd (snd l2))"
proof -
  consider "snd (fst l1) \<le> snd (snd l1) \<and> snd (fst l2) \<le> snd (snd l2)" | 
           "snd (fst l1) \<le> snd (snd l1) \<and> snd (fst l2) > snd (snd l2)" | 
           "snd (fst l1) > snd (snd l1) \<and> snd (fst l2) \<le> snd (snd l2)" | 
           "snd (fst l1) > snd (snd l1) \<and> snd (fst l2) > snd (snd l2)"
           by linarith
  thus ?thesis
  proof (cases)
    case 1
    hence f: "snd (fst l1) \<le> snd (snd l1)" and s: "snd (fst l2) \<le> snd (snd l2)" by auto  
    from overlaps_y_closed_segment_case[OF assms f s] show ?thesis by auto 
  next
    case 2
    define l2' where "l2' \<equiv> (snd l2, fst l2)"
    from assms have "overlaps_y l1 l2'" unfolding l2'_def using overlaps_y_invariant
      by blast
    from overlaps_y_closed_segment_case[OF this] 2 
    have "\<exists>p. p \<in> closed_segment (snd (fst l1)) (snd (snd l1)) \<and> p \<in> closed_segment (snd (fst l2')) (snd (snd l2'))"
      unfolding l2'_def by auto        
    then show ?thesis unfolding l2'_def using closed_segment_commute by auto
  next
    case 3
    define l1' where "l1' \<equiv> (snd l1, fst l1)"
    from assms have "overlaps_y l1' l2" unfolding l1'_def using overlaps_y_invariant'
      by blast
    from overlaps_y_closed_segment_case[OF this] 3 
    have "\<exists>p. p \<in> closed_segment (snd (fst l1')) (snd (snd l1')) \<and> p \<in> closed_segment (snd (fst l2)) (snd (snd l2))"
      unfolding l1'_def by auto        
    then show ?thesis unfolding l1'_def using closed_segment_commute by auto
  next
    case 4
    define l1' where "l1' \<equiv> (snd l1, fst l1)"
    define l2' where "l2' \<equiv> (snd l2, fst l2)"                                
    from assms have "overlaps_y l1' l2'" unfolding l1'_def l2'_def using overlaps_y_invariant2
      by blast
    from overlaps_y_closed_segment_case[OF this] 4 
    have " \<exists>p. p \<in> closed_segment (snd (fst l1')) (snd (snd l1')) \<and> p \<in> closed_segment (snd (fst l2')) (snd (snd l2'))"
      unfolding l1'_def l2'_def by auto        
    then show ?thesis unfolding l1'_def l2'_def using closed_segment_commute by auto
  qed         
qed
    
definition overlaps :: "real2 \<times> real2 \<Rightarrow> real2 \<times> real2 \<Rightarrow> bool" where
  "overlaps l1 l2 \<equiv> (let i1 = (fst (fst l1), fst (snd l1)); i2 = (fst (fst l2), fst (snd l2));
                          i1' = (min (fst i1) (snd i1), max (fst i1) (snd i1)); 
                          i2' = (min (fst i2) (snd i2), max (fst i2) (snd i2))
                      in fst i2' \<le> snd i1' \<and> fst i1' \<le> snd i2')"  
  
theorem overlaps_invariant:
  assumes "l2' = (snd l2, fst l2)"
  shows "overlaps l1 l2 = overlaps l1 l2'"
  using assms unfolding overlaps_def Let_def by auto    

theorem overlaps_commute:
  "overlaps l1 l2 = overlaps l2 l1"
  unfolding overlaps_def Let_def by auto
    
theorem overlaps_invariant':
  assumes "l1' = (snd l1, fst l1)"
  shows "overlaps l1 l2 = overlaps l1' l2"
  using assms overlaps_commute overlaps_invariant by blast

theorem overlaps_invariant2:
  assumes "l1' = (snd l1, fst l1)"
  assumes "l2' = (snd l2, fst l2)"
  shows "overlaps l1 l2 = overlaps l1' l2'"
  using assms overlaps_invariant overlaps_invariant' by blast

lemma nonoverlapping:
  assumes "\<not> overlaps l1 l2"
  shows "\<not> (\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"
proof (rule ccontr)    
  assume "\<not> (\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"
  then obtain p where pl1: "p \<in> closed_segment (fst l1) (snd l1)" and pl2: "p \<in> closed_segment (fst l2) (snd l2)"
    by auto      
  from pl1 have "fst p \<in> closed_segment (fst (fst l1)) (fst (snd l1))" 
    unfolding closed_segment_def by auto
  hence c1: "fst p \<in> {fst (fst l1) .. fst (snd l1)} \<or> fst p \<in> {fst (snd l1) .. fst (fst l1)}"
    (is "?ran11 \<or> ?ran12")
    using closed_segment_real[of "fst (fst l1)" "fst (snd l1)"] 
    by (cases "fst (fst l1) \<le> fst (snd l1)") (auto)
  from pl2 have "fst p \<in> closed_segment (fst (fst l2)) (fst (snd l2))"
    unfolding closed_segment_def by auto
  hence c2: "fst p \<in> {fst (fst l2) .. fst (snd l2)} \<or> fst p \<in> {fst (snd l2) .. fst (fst l2)}"
    (is "?ran21 \<or> ?ran22")
    using closed_segment_real by (cases "fst (fst l2) \<le> fst (snd l2)") (auto)
  consider "?ran11 \<and> ?ran21" | "?ran11 \<and> ?ran22" | "?ran12 \<and> ?ran21" | "?ran12 \<and> ?ran22"
    using c1 c2 by auto
  thus False
  proof (cases)
    case 1
    hence "fst (fst l1) \<le> fst (snd l1)" and "fst (fst l2) \<le> fst (snd l2)" by auto
    with assms have "\<not> (fst (fst l2) \<le> fst (snd l1) \<and> fst (fst l1) \<le> fst (snd l2))"
      unfolding overlaps_def Let_def by auto
    hence "fst (snd l1) < fst (fst l2)  \<or> fst (snd l2) < fst (fst l1)"
      by auto
    with 1 show "False" by auto         
  next
    case 2
    hence "fst (fst l1) \<le> fst (snd l1)" and "fst (snd l2) \<le> fst (fst l2)" by auto
    with assms have "\<not> (fst (snd l2) \<le> fst (snd l1) \<and> fst (fst l1) \<le> fst (fst l2))"
      unfolding overlaps_def Let_def by auto
    hence "fst (snd l1) < fst (snd l2) \<or> fst (fst l2) < fst (fst l1)" by auto        
    with 2 show ?thesis by auto
  next
    case 3
    hence "fst (snd l1) \<le> fst (fst l1)" and "fst (fst l2) \<le> fst (snd l2)"  by auto
    with assms have "\<not> (fst (fst l2) \<le> fst (fst l1) \<and> fst (snd l1) \<le> fst (snd l2))"
      unfolding overlaps_def Let_def by auto
    hence "fst (fst l1) < fst (fst l2) \<or> fst (snd l2) < fst (snd l1)" by auto        
    with 3 show ?thesis by auto
  next
    case 4
    hence "fst (snd l1) \<le> fst (fst l1)" and "fst (snd l2) \<le> fst (fst l2)" by auto
    with assms have "\<not> (fst (snd l2) \<le> fst (fst l1) \<and> fst (snd l1) \<le> fst (fst l2))"  
      unfolding overlaps_def Let_def by auto        
    with 4 show ?thesis by auto
  qed      
qed
   
definition find_intersection :: "real2 \<times> real2 \<Rightarrow> real2 \<times> real2 \<Rightarrow> real2" where
  "find_intersection l1 l2 \<equiv>  
      (let a1 = snd (snd l1) - snd (fst l1); b1 = fst (fst l1) - fst (snd l1);
                        c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1); 
           a2 = snd (snd l2) - snd (fst l2); b2 = fst (fst l2) - fst (snd l2); 
                        c2 = fst (fst l2) * snd (snd l2) - (fst (snd l2) * snd (fst l2));
           det_val = det2 (a1, b1) (a2, b2) 
       in 
        if det_val = 0 then undefined else (1 / det_val) *\<^sub>R (b2 * c1 - b1 * c2, a1 * c2 - a2 * c1))"

abbreviation in_x_domain :: "real2 \<times> real2 \<Rightarrow> real \<Rightarrow> bool" where
  "in_x_domain l x \<equiv> fst (fst l) \<le> x \<and> x \<le> fst (snd l) \<or>  fst (snd l) \<le> x \<and> x \<le> fst (fst l)"  
      
theorem in_x_domain_eq_fst_closed_segment:
  "in_x_domain l x \<longleftrightarrow> x \<in> closed_segment (fst (fst l)) (fst (snd l))"
  by (cases "fst (fst l) \<le> fst (snd l)") (auto simp add:closed_segment_real)
    
abbreviation in_y_domain :: "real2 \<times> real2 \<Rightarrow> real \<Rightarrow> bool" where
  "in_y_domain l y \<equiv> snd (fst l) \<le> y \<and> y \<le> snd (snd l) \<or> snd (snd l) \<le> y \<and> y \<le> snd (fst l)"
  
theorem in_y_domain_eq_snd_closed_segment:
  "in_y_domain l y \<longleftrightarrow> y \<in> closed_segment (snd (fst l)) (snd (snd l))"
  by (cases "snd (fst l) \<le> snd (snd l)") (auto simp add:closed_segment_real)  
    
  
definition segments_intersects2 :: "(real2 \<times> real2) \<Rightarrow> (real2 \<times> real2) \<Rightarrow> bool" where
  "segments_intersects2 l1 l2 \<equiv> (let p = find_intersection l1 l2 in 
                                  (if parallel_lines l1 l2 then False 
                                   else if not_aligned l1 l2 then in_x_domain l1 (fst p) \<and> in_x_domain l2 (fst p) \<and> 
                                                                  in_y_domain l1 (snd p) \<and> in_y_domain l2 (snd p)
                                   else overlaps l1 l2 \<and> overlaps_y l1 l2))"
    
theorem uniqueness:
  assumes par: "\<not> parallel_lines l1 l2"
  assumes nal: "not_aligned l1 l2"    
  assumes pl1: "p \<in> points_in_lines (fst l1) (snd l1)" and pl2: "p \<in> points_in_lines (fst l2) (snd l2)"
  shows "find_intersection l1 l2 = p"    
proof -
  from pl1 obtain a1 b1 c1 where e1: "a1 * (fst p) + b1 * (snd p) = c1" (is "?e1lhs = ?e1rhs") 
    and a1_def: "a1 = snd (snd l1) - snd (fst l1)"
    and b1_def: "b1 = fst (fst l1) - fst (snd l1)" and c1_def: "c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1)"
    unfolding points_in_lines_def Let_def by auto
  from pl2 obtain a2 b2 c2 where e2: "a2 * (fst p) + b2 * (snd p) = c2" (is "?e2lhs = ?e2rhs")
    and a2_def: "a2 = snd (snd l2) - snd (fst l2)"
    and b2_def: "b2 = fst (fst l2) - fst (snd l2)" and c2_def: "c2 = fst (fst l2) * snd (snd l2) - fst (snd l2) * snd (fst l2)"
    unfolding points_in_lines_def Let_def by auto
  from par have "det2 (a1, b1) (a2, b2) \<noteq> 0 \<or> det2 (b1, c1) (b2, c2) = 0" 
    unfolding parallel_lines_def Let_def a1_def b1_def a2_def b2_def c1_def c2_def by auto
  with nal have nz: "det2 (a1, b1) (a2, b2) \<noteq> 0" unfolding not_aligned_def Let_def b1_def c1_def b2_def c2_def
    using a1_def a2_def by blast      
   define det_val where "det_val = det2 (a1,b1) (a2,b2)"      
   hence fi_eq: "find_intersection l1 l2 = (1 / det_val) *\<^sub>R (b2 * c1 - b1 * c2, a1 * c2 - a2 * c1)"
     using nz unfolding find_intersection_def Let_def det_val_def a1_def b1_def a2_def b2_def
     c1_def c2_def by auto
   show "find_intersection l1 l2 = p"
   proof (rule ccontr)      
     assume "find_intersection l1 l2 \<noteq> p"
     hence "fst (find_intersection l1 l2) \<noteq> fst p \<or> snd (find_intersection l1 l2) \<noteq> snd p"
       by (metis prod.collapse)
     moreover    
     { assume "fst (find_intersection l1 l2) \<noteq> fst p"
       with fi_eq have neq: "fst p \<noteq> (1 / det_val) * (b2 * c1 - b1 * c2)" by auto
       from e1 have 0: "?e1lhs * b2 = ?e1rhs * b2" by (auto simp add:algebra_simps)
       from e2 have "?e2lhs * b1 = ?e2rhs * b1" by (auto simp add:algebra_simps) 
       with 0 have "?e1lhs * b2 - ?e2lhs * b1 = ?e1rhs * b2 - ?e2rhs * b1" by auto
       hence "a1 * fst p * b2 - a2 * fst p * b1 = c1 * b2 - c2 * b1" by (auto simp add:algebra_simps)
       hence "det_val * fst p = c1 * b2 - c2 * b1" unfolding det_val_def by (auto simp add:algebra_simps)
       hence "fst p = (1 / det_val) * (c1 * b2 - c2 * b1)" using nz eq_divide_imp[OF nz] unfolding det_val_def
         by (auto simp add:algebra_simps)
       with neq have "False" by auto }
     moreover
     { assume "snd (find_intersection l1 l2) \<noteq> snd p"
       with fi_eq have neq2: "snd p \<noteq> (1 / det_val) * (a1 * c2 - a2 * c1)" by auto
       from e1 have 0: "?e1lhs * a2 = ?e1rhs * a2" by (auto simp add:algebra_simps)   
       from e2 have "?e2lhs * a1 = ?e2rhs * a1" by (auto simp add:algebra_simps) 
       with 0 have "?e1lhs * a2 - ?e2lhs * a1 = ?e1rhs * a2 - ?e2rhs * a1" by auto
       hence "b1 * snd p * a2 - b2 * snd p * a1 = c1 * a2 - c2 * a1" by (auto simp add:algebra_simps)
       hence "-det_val * snd p = c1 * a2 - c2 * a1" unfolding det_val_def by (auto simp add:algebra_simps)
       hence "snd p = (1 / det_val) * (a1 * c2 - a2 * c1)" using nz eq_divide_imp[OF nz] unfolding det_val_def
         by (auto simp add:algebra_simps)
       with neq2 have "False" by auto }
     ultimately show False by auto          
   qed    
qed
             
theorem segments_intersects_correctness_none:
  assumes "\<not> segments_intersects2 l1 l2"
  shows "\<not> (\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))" (is "\<not> ?E")
proof (rule ccontr)
  assume "\<not> (\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"    
  hence "?E" by auto
  from assms have "parallel_lines l1 l2 \<or> 
   \<not> parallel_lines l1 l2 \<and> not_aligned l1 l2 \<and>  
              (\<not> in_x_domain l1 (fst (find_intersection l1 l2)) \<or> 
               \<not> in_x_domain l2 (fst (find_intersection l1 l2)) \<or> 
               \<not> in_y_domain l1 (snd (find_intersection l1 l2)) \<or>
               \<not> in_y_domain l2 (snd (find_intersection l1 l2))) \<or>
    \<not> parallel_lines l1 l2 \<and> \<not> not_aligned l1 l2 \<and> (\<not> overlaps l1 l2 \<or> \<not> overlaps_y l1 l2)" unfolding segments_intersects2_def Let_def 
  by presburger
  moreover
  { assume "parallel_lines l1 l2"
    with parallel_correctness have pc: "points_in_lines (fst l1) (snd l1) \<inter> points_in_lines (fst l2) (snd l2) = {}" by auto 
    have "closed_segment (fst l1) (snd l1) \<subseteq> points_in_lines (fst l1) (snd l1)" and
       "closed_segment (fst l2) (snd l2) \<subseteq> points_in_lines (fst l2) (snd l2)" using closed_segment_subset_pil
      by auto
    with pc have "closed_segment (fst l1) (snd l1) \<inter> closed_segment (fst l2) (snd l2) = {}" by auto    
    with `?E` have "False" by auto }
  moreover
  { assume case3: "\<not> parallel_lines l1 l2 \<and> not_aligned l1 l2 \<and>  
                                                (\<not> in_x_domain l1 (fst (find_intersection l1 l2)) \<or> 
                                                 \<not> in_x_domain l2 (fst (find_intersection l1 l2))) \<or> 
                                                 \<not> in_y_domain l1 (snd (find_intersection l1 l2)) \<or>
                                                 \<not> in_y_domain l2 (snd (find_intersection l1 l2))" 
    have "False"
    \<comment> \<open>The proof of this case uses the uniqueness theorem where the intersection must be 
        the one computed by @{term "find_intersection"}. If it is an intersection point, then 
        the point must be located at both closed segments. But from the assumptions we have, 
        the point is not in both domains, hence contradiction.\<close>
    proof -      
      from `?E` obtain p where l1: "p \<in> closed_segment (fst l1) (snd l1)" and 
        l2: "p \<in> closed_segment (fst l2) (snd l2)" by auto  
      with closed_segment_subset_pil have 0: "p \<in> points_in_lines (fst l1) (snd l1)"          
        by blast
      from l2 and closed_segment_subset_pil have "p \<in> points_in_lines (fst l2) (snd l2)"
        by blast
      with 0 and case3 have "find_intersection l1 l2 = p" using uniqueness
        by (metis calculation(1) calculation(2) l1 l2 nonoverlapping nonoverlapping_y)  
       from l1 have 1: "in_x_domain l1 (fst p)" using in_x_domain_eq_fst_closed_segment 
        by (metis closed_segment_PairD surjective_pairing)
      from l1 have 3: "in_y_domain l1 (snd p)" using in_y_domain_eq_snd_closed_segment
        by (metis closed_segment_PairD surjective_pairing)        
      from l2 have "in_x_domain l2 (fst p)" using in_x_domain_eq_fst_closed_segment
        by (metis closed_segment_PairD surjective_pairing)
      from l2 have 4: "in_y_domain l2 (snd p)" using in_y_domain_eq_snd_closed_segment
        by (metis closed_segment_PairD surjective_pairing)          
      with 1 3 4 and case3 and `find_intersection l1 l2 = p` show "False"
        by (simp add: \<open>in_x_domain l2 (fst p)\<close>)                 
    qed }
  moreover
  { assume "\<not> parallel_lines l1 l2 \<and> \<not> not_aligned l1 l2 \<and> (\<not> overlaps l1 l2 \<or> \<not> overlaps_y l1 l2)"
    hence "\<not> parallel_lines l1 l2 \<and> \<not> not_aligned l1 l2 \<and> \<not> overlaps l1 l2 \<or> 
           \<not> parallel_lines l1 l2 \<and> \<not> not_aligned l1 l2 \<and> \<not> overlaps_y l1 l2" (is "?case1 \<or> ?case2")
      by auto
    moreover
    { assume "?case1"
      hence "\<not> overlaps l1 l2" by auto
      from nonoverlapping[OF this] and `?E` have "False" by auto }
    moreover
    { assume "?case2"
      hence "\<not> overlaps_y l1 l2" by auto
      from nonoverlapping_y[OF this] and `?E` have "False" by auto }
    ultimately have "False" by auto }    
  ultimately show "False" by auto
qed
      
theorem t1:   
  fixes x :: real
  assumes cs: "x \<in> closed_segment x1 x2"
  assumes mn: "a * x + b * y = c"
  assumes fs: "a * x1 + b * y1 = c" and ns: "a * x2 + b * y2 = c"
  assumes naz: "\<not> (a = 0 \<and> b = 0)"  
  assumes xneq: "x2 \<noteq> x1"    
  shows "(x,y) \<in> closed_segment (x1,y1) (x2,y2)"
proof -
  from assms(1) obtain t1 where "x = (1 - t1) * x1 + t1 * x2" and "0 \<le> t1" and "t1 \<le> 1" 
    unfolding closed_segment_def by auto
  hence 0: "x = x1 + t1 * (x2 - x1)" by (auto simp add:algebra_simps)
  from mn and fs have "a * x + b * y = a * x1 + b * y1" by auto
  hence xx1: "a * (x - x1) + b * (y - y1) = 0" by (auto simp add:algebra_simps)    
  from fs and ns have "a * x1 + b * y1 = a * x2 + b * y2" by auto
  hence eq:"0 = a * (x2 - x1) + b * (y2 - y1)" by (auto simp add:algebra_simps)      
  from xneq have "x2 - x1 \<noteq> 0" by auto
  with 0 have "t1 = (x - x1) / (x2 - x1)" by auto
  from eq have "t1 * 0 = t1 * (a * (x2 - x1) + b * (y2 - y1))" by auto
  also have "... = t1 * a * (x2 - x1) + t1 * b * (y2 - y1)" by (auto simp add:algebra_simps)
  finally have eq1: "0 = t1 * a * (x2 - x1) + t1 * b * (y2 - y1)" by auto
  have "b = 0 \<or> b \<noteq> 0" by auto
  moreover
  { assume "b = 0"
    with eq have "a = 0" using `x2 - x1 \<noteq> 0` by auto  
    with `b = 0` have "False" using naz by auto 
    hence "(x,y) \<in> closed_segment (x1,y1) (x2,y2)" by auto }
  moreover
  { assume "b \<noteq> 0"
    with eq have "y2 - y1 = a * (x1 - x2) / b" by (auto simp add:divide_simps algebra_simps)
    hence "t1 * (y2 - y1) = t1 * a * (x1 - x2) / b" by auto
    with `t1 = (x - x1) / (x2 - x1)` have "t1 * (y2 - y1) = - (x - x1) * a / b" 
      using `x2 - x1 \<noteq> 0` 
      by (smt eq_divide_eq mult.commute mult_minus_left times_divide_eq_left)
    hence temp: "y1 + t1 * (y2 - y1) = y1 +- (x - x1) * a / b" by auto           
    from xx1 have "a * (x - x1) / b + (y - y1) = 0" using `b \<noteq> 0` by (auto simp add:divide_simps algebra_simps)
    hence "- (x - x1) * a / b = y - y1" by (auto simp add:algebra_simps divide_simps)
    with temp have "y1 + t1 * (y2 - y1) = y1 + (y - y1)" by (auto simp add:divide_simps algebra_simps)
    hence "y1 + t1 * (y2 - y1) = y" by (auto simp add:algebra_simps)
    hence "y = (1 - t1) * y1 + t1 * y2" by (auto simp add:algebra_simps)   
    with `x = (1 - t1) * x1 + t1 * x2` have "(x,y) = (1 - t1) *\<^sub>R (x1,y1) + t1 *\<^sub>R (x2,y2)"
      by (auto simp add:field_simps)
    hence "(x,y) \<in> closed_segment (x1,y1) (x2,y2)" unfolding closed_segment_def           
        using `0 \<le> t1` and `t1 \<le> 1` by auto }      
  ultimately show ?thesis by auto
qed
  
theorem t2:   
  fixes x :: real
  assumes cs:  "x \<in> closed_segment x1 x2"
  assumes cs2: "y \<in> closed_segment y1 y2"  
  assumes mn: "a * x + b * y = c"
  assumes fs: "a * x1 + b * y1 = c" and ns: "a * x2 + b * y2 = c"
  assumes naz: "\<not> (a = 0 \<and> b = 0)"  
  assumes xneq: "x2 = x1"    
  shows "(x,y) \<in> closed_segment (x1,y1) (x2,y2)"
proof -
  from cs and xneq have "x = x2" and "x = x1" by auto
  have "b \<noteq> 0 \<or> b = 0" by auto    
  moreover
  { assume "b  = 0"
    with mn fs and ns have "a * x = c" by auto
    from `b = 0` and naz have "a \<noteq> 0" by auto
    with `a * x = c` have "x = c / a" by auto
    from cs2 obtain t where 0: "y = y1 + t * (y2 - y1)" and "0 \<le> t" and "t \<le> 1" 
      unfolding closed_segment_def  by (auto simp add:algebra_simps)    
    from `x = x1` have "x = x1 + t * (x2 - x1)" using `x = x2` by auto
    with 0 have "(x,y) = (x1,y1) + t *\<^sub>R ((x2,y2) - (x1,y1))" by (auto simp add:field_simps)
    hence "(x, y) = (1 - t) *\<^sub>R (x1,y1) + t *\<^sub>R (x2,y2)" by (auto simp add:field_simps)
    hence "(x,y) \<in> closed_segment (x1,y1) (x2,y2)" unfolding closed_segment_def
      using `0 \<le> t` and `t \<le> 1` by auto } 
  moreover
  { assume "b \<noteq> 0"
    with mn and fs have "y = y1" using `x = x1` by auto
    from `b \<noteq> 0` and mn and ns have "y = y2" using `x = x2` by auto
    with `y = y1` and `x = x1` and `x = x2` have "closed_segment (x1,y1) (x2,y2) = {(x,y)}"
      unfolding closed_segment_def by (auto simp add:field_simps)
    hence "(x,y) \<in> closed_segment (x1,y1) (x2,y2)" by auto  }
  ultimately show "(x,y) \<in> closed_segment (x1,y1) (x2,y2)" by auto    
qed
  
lemma t3_1:
  assumes np: "\<not> parallel_lines l1 l2"         
  assumes al: "\<not> not_aligned l1 l2"
  assumes ov: "overlaps l1 l2" and ovy: "overlaps_y l1 l2"
  assumes neq1: "fst l1 \<noteq> snd l1" and neq2: "fst l2 \<noteq> snd l2"    
  assumes ordered: "fst (fst l1) \<le> fst (snd l1)" and ordered': "fst (fst l2) \<le> fst (snd l2)"  
  assumes cond11_2: "fst (fst l1) \<le> fst (fst l2)"    
  shows "\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2)"
proof -
  from ov have cond11_1: "fst (fst l2) \<le> fst (snd l1)" 
    using ordered and ordered' unfolding overlaps_def Let_def by auto
  define a1 where "a1 = snd (snd l1) - snd (fst l1)"
  define b1 where "b1 = fst (fst l1) - fst (snd l1)"
  define c1 where "c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1)"
  define a2 where "a2 = snd (snd l2) - snd (fst l2)"
  define b2 where "b2 = fst (fst l2) - fst (snd l2)" 
  define c2 where "c2 = fst (fst l2) * snd (snd l2) - fst (snd l2) * snd (fst l2)"  
  note coeffs = a1_def b1_def c1_def a2_def b2_def c2_def  
  have "\<not> (a1 = 0 \<and> b1 = 0)" unfolding coeffs using neq1
    using prod_eqI by fastforce
  have "\<not> (a2 = 0 \<and> b2 = 0)" unfolding coeffs using neq2
    using prod_eqI by fastforce      
  from np and al have "det2 (a1, b1) (a2, b2) = 0" and "det2 (b1, c1) (b2, c2) = 0"
    unfolding parallel_lines_def not_aligned_def Let_def coeffs
    by auto  
  hence "a1 * b2 = a2 * b1" and "b1 * c2 = b2 * c1" by auto
      
  define chosenpoint where "chosenpoint \<equiv> fst l2" \<comment> \<open>Choose first endpoint of l2\<close> 
  have "chosenpoint \<in> closed_segment (fst l2) (snd l2)" unfolding chosenpoint_def by auto   
  hence "fst chosenpoint \<in> closed_segment (fst (fst l2)) (fst (snd l2))" 
    using fst_closed_segment by blast    
  have "fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))"
    using cond11_1 cond11_2 closed_segment_real ordered(1) by (simp add: chosenpoint_def)         
  have "chosenpoint \<in> points_in_lines (fst l2) (snd l2)"
    unfolding points_in_lines_def Let_def chosenpoint_def by (auto simp add:algebra_simps)      
  hence base: "a2 * fst chosenpoint + b2 * snd chosenpoint = c2" (is "?lbase = ?rbase")
    unfolding points_in_lines_def Let_def chosenpoint_def coeffs by (auto simp add:algebra_simps)
  consider "a2 = 0" | "a2 \<noteq> 0" by auto    
  thus ?thesis
  proof (cases)
    case 1
    with `\<not> (a2 = 0 \<and> b2 = 0)` have "b2 \<noteq> 0" by auto
    from 1 and `a1 * b2 = a2 * b1` have "a1 * b2 = 0" by auto
    with `b2 \<noteq> 0` have "a1 = 0" by auto
    with `\<not> (a1 = 0 \<and> b1 = 0)` have "b1 \<noteq> 0" by auto
    have "chosenpoint \<in> points_in_lines (fst l1) (snd l1)"
    proof -
      from base `a2 = 0` have "b2 * snd chosenpoint = c2" by auto
      with `b2 \<noteq> 0` have "snd chosenpoint = c2 / b2" by auto
      with `b1 * c2 = b2 * c1` have "c2 / b2 = c1 / b1" using `b2 \<noteq> 0` `b1 \<noteq> 0` 
        by (auto simp add:divide_simps)
      with `snd chosenpoint = c2 / b2` have "snd chosenpoint = c1 / b1" by auto
      with `b1 \<noteq> 0` have "b1 * snd chosenpoint = c1" by auto
      with `a1 = 0` have "a1 * fst chosenpoint + b1 * snd chosenpoint = c1" by auto
      thus ?thesis unfolding points_in_lines_def Let_def chosenpoint_def coeffs by auto
    qed        
    from pil_also_closed_segment[OF this `fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))`]
      have "chosenpoint \<in> closed_segment (fst l1) (snd l1)" using `b1 \<noteq> 0` unfolding coeffs by auto 
    with `chosenpoint \<in> closed_segment (fst l2) (snd l2)` show ?thesis by blast
  next
    case 2
    hence "a1 * b2 / a2 = b1" using `a1 * b2 = a2 * b1` by (auto simp add:divide_simps) 
    have "b1 * b2 \<noteq> 0 \<or> b1 * b2 = 0" by auto
    moreover    
    { assume "b1 * b2 \<noteq> 0"
      hence "b1 \<noteq> 0" and "b2 \<noteq> 0" by auto  
      have "a1 * c2 / a2 = c1"
      proof -
        from `a1 * b2 = a2 * b1` and `b1 * c2 = b2 * c1`
        have "a1 * b2 * b1 * c2 = a2 * b1 * b2 * c1" by auto
        with 2 and `b1 \<noteq> 0` and `b2 \<noteq> 0` show ?thesis by (auto simp add:divide_simps)        
      qed
      from base have "(a1 / a2) * ?lbase = (a1 / a2) * ?rbase" by auto  
      with `a2 \<noteq> 0` have "a1 * fst chosenpoint + b1 * snd chosenpoint = c1"
        using `a1 * b2 / a2 = b1` and `a1 * c2 / a2 = c1` by (auto simp add:algebra_simps)
      hence "chosenpoint \<in> points_in_lines (fst l1) (snd l1)"
        unfolding points_in_lines_def Let_def chosenpoint_def coeffs by auto
      from pil_also_closed_segment[OF this `fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))`]
      have "chosenpoint \<in> closed_segment (fst l1) (snd l1)" using `b1 \<noteq> 0` unfolding coeffs by auto
      with `chosenpoint \<in> closed_segment (fst l2) (snd l2)` have ?thesis by blast }    
    moreover
    { assume "b1 * b2 = 0"
      have "b1 = 0 \<and> b2 = 0"
      proof (rule ccontr)
        assume "\<not> (b1 = 0 \<and> b2 = 0)"  
        hence ded1: "b1 = 0 \<longrightarrow> b2 \<noteq> 0" by auto
        have "b1 = 0 \<longrightarrow> b2 = 0"
        proof 
          assume "b1 = 0"
          with `fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))`
            have "fst chosenpoint = fst (fst l1)" unfolding coeffs by auto
          from `b1 = 0` `a1 * b2 = a2 * b1` have "a1 * b2 = 0" by auto
          from `b1 = 0` have "a1 \<noteq> 0" using `\<not> (a1 = 0 \<and> b1 = 0)` by auto    
          with `a1 * b2 = 0` show "b2 = 0" by auto             
        qed                         
        with ded1 show "False"
          using "2" \<open>a1 * b2 = a2 * b1\<close> \<open>b1 * b2 = 0\<close> by auto  
      qed
      hence "b1 = 0" and "b2 = 0" by auto
      hence "a1 \<noteq> 0" and "a2 \<noteq> 0" using `\<not> (a1 = 0 \<and> b1 = 0)` `\<not> (a2 = 0 \<and> b2 = 0)`
        by auto
      from ovy obtain y where "y \<in> closed_segment (snd (fst l1)) (snd (snd l1))"
        and "y \<in> closed_segment (snd (fst l2)) (snd (snd l2))" 
        using overlaps_y_closed_segment[OF ovy] by auto 
      from `b1 = 0` and `fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))`
      have "fst chosenpoint = fst (fst l1)" unfolding coeffs by auto
      with `b1 = 0` have "fst chosenpoint = fst (snd l1)" unfolding coeffs by auto      
      with `fst chosenpoint = fst (fst l1)` have "a1 * fst chosenpoint = c1"
        unfolding coeffs chosenpoint_def by (auto simp add:algebra_simps)
      with `b1 = 0` have "a1 * fst chosenpoint + b1 * y = c1" by auto
      hence "(fst chosenpoint, y) \<in> points_in_lines (fst l1) (snd l1)" 
        unfolding points_in_lines_def Let_def coeffs by auto
      from pil_also_closed_segment_y[OF this ]                                  
        and `y \<in> closed_segment (snd (fst l1)) (snd (snd l1))`
      have "(fst chosenpoint, y) \<in> closed_segment (fst l1) (snd l1)" using `b1 = 0` `a1 \<noteq> 0`
        unfolding coeffs by auto
      from base `b2 = 0` have "a2 * fst chosenpoint = c2" by auto
      hence "a2 * fst chosenpoint + b2 * y = c2" using `b2 = 0` by auto
      hence "(fst chosenpoint, y) \<in> points_in_lines (fst l2) (snd l2)"
        unfolding points_in_lines_def Let_def coeffs by auto
      from pil_also_closed_segment_y[OF this] 
        `fst chosenpoint \<in> closed_segment (fst (fst l2)) (fst (snd l2))`
      have "(fst chosenpoint, y) \<in> closed_segment (fst l2) (snd l2)"  using `b2 = 0` `a2 \<noteq> 0`
        unfolding coeffs
        by (simp add: \<open>y \<in> closed_segment (snd (fst l2)) (snd (snd l2))\<close>)
      with `(fst chosenpoint, y) \<in> closed_segment (fst l1) (snd l1)`
        have ?thesis by blast }
    ultimately show ?thesis by auto
  qed        
qed  

theorem t3_2:   
  assumes np: "\<not> parallel_lines l1 l2"         
  assumes al: "\<not> not_aligned l1 l2"
  assumes ov: "overlaps l1 l2" and ovy: "overlaps_y l1 l2"
  assumes neq1: "fst l1 \<noteq> snd l1" and neq2: "fst l2 \<noteq> snd l2"    
  assumes ordered: "fst (fst l1) \<le> fst (snd l1)" and ordered': "fst (fst l2) \<le> fst (snd l2)"  
  assumes cond11_2: "fst (fst l2) < fst (fst l1)"    
  shows "\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2)"  
proof -
  from ov have cond11_1: "fst (fst l1) \<le> fst (snd l2)" 
    using ordered and ordered' unfolding overlaps_def Let_def by auto
  define a1 where "a1 = snd (snd l1) - snd (fst l1)"
  define b1 where "b1 = fst (fst l1) - fst (snd l1)"
  define c1 where "c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1)"
  define a2 where "a2 = snd (snd l2) - snd (fst l2)"
  define b2 where "b2 = fst (fst l2) - fst (snd l2)" 
  define c2 where "c2 = fst (fst l2) * snd (snd l2) - fst (snd l2) * snd (fst l2)"  
  note coeffs = a1_def b1_def c1_def a2_def b2_def c2_def  
  have "\<not> (a1 = 0 \<and> b1 = 0)" unfolding coeffs using neq1
    using prod_eqI by fastforce
  have "\<not> (a2 = 0 \<and> b2 = 0)" unfolding coeffs using neq2
    using prod_eqI by fastforce      
  from np and al have "det2 (a1, b1) (a2, b2) = 0" and "det2 (b1, c1) (b2, c2) = 0"
    unfolding parallel_lines_def not_aligned_def Let_def coeffs
    by auto  
  hence "a1 * b2 = a2 * b1" and "b1 * c2 = b2 * c1" by auto
      
  define chosenpoint where "chosenpoint \<equiv> fst l1" \<comment> \<open>Choose first endpoint of l1\<close> 
  have "chosenpoint \<in> closed_segment (fst l1) (snd l1)" unfolding chosenpoint_def by auto   
  hence "fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))" 
    using fst_closed_segment by blast    
  have "fst chosenpoint \<in> closed_segment (fst (fst l2)) (fst (snd l2))"
    using cond11_1 cond11_2 closed_segment_real ordered(1) by (simp add: chosenpoint_def)         
  have "chosenpoint \<in> points_in_lines (fst l1) (snd l1)"
    unfolding points_in_lines_def Let_def chosenpoint_def by (auto simp add:algebra_simps)      
  hence base: "a1 * fst chosenpoint + b1 * snd chosenpoint = c1" (is "?lbase = ?rbase")
    unfolding points_in_lines_def Let_def chosenpoint_def coeffs by (auto simp add:algebra_simps)
  consider "a1 = 0" | "a1 \<noteq> 0" by auto    
  thus ?thesis
  proof (cases)
    case 1
    with `\<not> (a1 = 0 \<and> b1 = 0)` have "b1 \<noteq> 0" by auto
    from 1 and `a1 * b2 = a2 * b1` have "a2 * b1 = 0" by auto
    with `b1 \<noteq> 0` have "a2 = 0" by auto
    with `\<not> (a2 = 0 \<and> b2 = 0)` have "b2 \<noteq> 0" by auto
    have "chosenpoint \<in> points_in_lines (fst l2) (snd l2)"
    proof -
      from base `a1 = 0` have "b1 * snd chosenpoint = c1" by auto
      with `b1 \<noteq> 0` have "snd chosenpoint = c1 / b1" by auto
      with `b1 * c2 = b2 * c1` have "c1 / b1 = c2 / b2" using `b2 \<noteq> 0` `b1 \<noteq> 0` 
        by (auto simp add:divide_simps)
      with `snd chosenpoint = c1 / b1` have "snd chosenpoint = c2 / b2" by auto
      with `b2 \<noteq> 0` have "b2 * snd chosenpoint = c2" by auto
      with `a2 = 0` have "a2 * fst chosenpoint + b2 * snd chosenpoint = c2" by auto
      thus ?thesis unfolding points_in_lines_def Let_def chosenpoint_def coeffs by auto
    qed        
    from pil_also_closed_segment[OF this `fst chosenpoint \<in> closed_segment (fst (fst l2)) (fst (snd l2))`]
      have "chosenpoint \<in> closed_segment (fst l2) (snd l2)" using `b2 \<noteq> 0` unfolding coeffs by auto 
    with `chosenpoint \<in> closed_segment (fst l1) (snd l1)` show ?thesis by blast
  next
    case 2
    hence "a2 * b1 / a1 = b2" using `a1 * b2 = a2 * b1` by (auto simp add:divide_simps algebra_simps) 
    have "b1 * b2 \<noteq> 0 \<or> b1 * b2 = 0" by auto
    moreover    
    { assume "b1 * b2 \<noteq> 0"
      hence "b1 \<noteq> 0" and "b2 \<noteq> 0" by auto  
      have "a2 * c1 / a1 = c2"
      proof -
        from `a1 * b2 = a2 * b1` and `b1 * c2 = b2 * c1`
        have "a1 * b2 * b1 * c2 = a2 * b1 * b2 * c1" by auto
        with 2 and `b1 \<noteq> 0` and `b2 \<noteq> 0` show ?thesis by (auto simp add:divide_simps algebra_simps)        
      qed
      from base have "(a2 / a1) * ?lbase = (a2 / a1) * ?rbase" by auto  
      with `a1 \<noteq> 0` have "a2 * fst chosenpoint + b2 * snd chosenpoint = c2"
        using `a2 * b1 / a1 = b2` and `a2 * c1 / a1 = c2` by (auto simp add:algebra_simps)
      hence "chosenpoint \<in> points_in_lines (fst l2) (snd l2)"
        unfolding points_in_lines_def Let_def chosenpoint_def coeffs by auto
      from pil_also_closed_segment[OF this `fst chosenpoint \<in> closed_segment (fst (fst l2)) (fst (snd l2))`]
      have "chosenpoint \<in> closed_segment (fst l2) (snd l2)" using `b2 \<noteq> 0` unfolding coeffs by auto
      with `chosenpoint \<in> closed_segment (fst l1) (snd l1)` have ?thesis by blast }    
    moreover
    { assume "b1 * b2 = 0"
      have "b1 = 0 \<and> b2 = 0"
      proof (rule ccontr)
        assume "\<not> (b1 = 0 \<and> b2 = 0)"  
        hence ded1: "b1 = 0 \<longrightarrow> b2 \<noteq> 0" by auto
        have "b1 = 0 \<longrightarrow> b2 = 0"
        proof 
          assume "b1 = 0"
          with `fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))`
            have "fst chosenpoint = fst (fst l1)" unfolding coeffs by auto
          from `b1 = 0` `a1 * b2 = a2 * b1` have "a1 * b2 = 0" by auto
          from `b1 = 0` have "a1 \<noteq> 0" using `\<not> (a1 = 0 \<and> b1 = 0)` by auto    
          with `a1 * b2 = 0` show "b2 = 0" by auto             
        qed                         
        with ded1 show "False"
          using "2" \<open>a1 * b2 = a2 * b1\<close> \<open>b1 * b2 = 0\<close>  using \<open>\<not> (a2 = 0 \<and> b2 = 0)\<close> by auto  
      qed
      hence "b1 = 0" and "b2 = 0" by auto
      hence "a1 \<noteq> 0" and "a2 \<noteq> 0" using `\<not> (a1 = 0 \<and> b1 = 0)` `\<not> (a2 = 0 \<and> b2 = 0)`
        by auto
      from ovy obtain y where "y \<in> closed_segment (snd (fst l2)) (snd (snd l2))"
        and "y \<in> closed_segment (snd (fst l1)) (snd (snd l1))" 
        using overlaps_y_closed_segment[OF ovy] by auto 
      from `b2 = 0` and `fst chosenpoint \<in> closed_segment (fst (fst l2)) (fst (snd l2))`
      have "fst chosenpoint = fst (fst l2)" unfolding coeffs by auto
      with `b2 = 0` have "fst chosenpoint = fst (snd l2)" unfolding coeffs by auto      
      with `fst chosenpoint = fst (fst l2)` have "a2 * fst chosenpoint = c2"
        unfolding coeffs chosenpoint_def by (auto simp add:algebra_simps)
      with `b2 = 0` have "a2 * fst chosenpoint + b2 * y = c2" by auto
      hence "(fst chosenpoint, y) \<in> points_in_lines (fst l2) (snd l2)" 
        unfolding points_in_lines_def Let_def coeffs by auto
      from pil_also_closed_segment_y[OF this ]                                  
        and `y \<in> closed_segment (snd (fst l2)) (snd (snd l2))`
      have "(fst chosenpoint, y) \<in> closed_segment (fst l2) (snd l2)" using `b2 = 0` `a2 \<noteq> 0`
        unfolding coeffs by auto
      from base `b1 = 0` have "a1 * fst chosenpoint = c1" by auto
      hence "a1 * fst chosenpoint + b1 * y = c1" using `b1 = 0` by auto
      hence "(fst chosenpoint, y) \<in> points_in_lines (fst l1) (snd l1)"
        unfolding points_in_lines_def Let_def coeffs by auto
      from pil_also_closed_segment_y[OF this] 
        `fst chosenpoint \<in> closed_segment (fst (fst l1)) (fst (snd l1))`
      have "(fst chosenpoint, y) \<in> closed_segment (fst l1) (snd l1)"  using `b1 = 0` `a1 \<noteq> 0`
        unfolding coeffs
        by (simp add: \<open>y \<in> closed_segment (snd (fst l1)) (snd (snd l1))\<close>)
      with `(fst chosenpoint, y) \<in> closed_segment (fst l2) (snd l2)`
        have ?thesis by blast }
    ultimately show ?thesis by auto
  qed        
qed 
  
lemma t3:
  assumes np: "\<not> parallel_lines l1 l2"         
  assumes al: "\<not> not_aligned l1 l2"
  assumes ov: "overlaps l1 l2" and ovy: "overlaps_y l1 l2"
  assumes neq1: "fst l1 \<noteq> snd l1" and neq2: "fst l2 \<noteq> snd l2"    
  assumes ordered: "fst (fst l1) \<le> fst (snd l1)" and ordered': "fst (fst l2) \<le> fst (snd l2)"  
  shows "\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2)"
proof -
    have "fst (fst l1) \<le> fst (fst l2) \<or> fst (fst l2) < fst (fst l1)"   by auto
    moreover
    { assume "fst (fst l1) \<le> fst (fst l2)"
      from t3_1[OF np al ov ovy neq1 neq2 ordered ordered' this] have ?thesis by auto }
    moreover
    { assume "fst (fst l2) < fst (fst l1)"
      from t3_2[OF np al ov ovy neq1 neq2 ordered ordered' this] have ?thesis by auto }
    ultimately show ?thesis by auto
qed

theorem segments_intersecst_correctness_some:
  assumes "segments_intersects2 l1 l2"
  assumes neq1: "fst l1 \<noteq> snd l1" and neq2: "fst l2 \<noteq> snd l2"    
  shows "\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2)"
proof -
  define p where "p \<equiv> find_intersection l1 l2"    
  from assms consider "\<not> parallel_lines l1 l2 \<and> not_aligned l1 l2 \<and> in_x_domain l1 (fst p) \<and> 
                         in_x_domain l2 (fst p) \<and> in_y_domain l1 (snd p) \<and> in_y_domain l2 (snd p)" | 
                      "\<not> parallel_lines l1 l2 \<and> \<not> not_aligned l1 l2 \<and> overlaps l1 l2 \<and> overlaps_y l1 l2"
    unfolding segments_intersects2_def p_def  by (metis)
  thus ?thesis
  proof (cases)
    case 1
    note case_one_top = this  
    \<comment> \<open>Here we have a classic case. The situation is both lines are not in parallel, the computed
        intersection points is inside the x-domain of both segments. The proof of this case relies
        on arithmetical operations.\<close>  
    hence np: "\<not> parallel_lines l1 l2" and na: "not_aligned l1 l2" and id: "in_x_domain l1 (fst p) \<and> in_x_domain l2 (fst p)"
      and id2: "in_y_domain l1 (snd p) \<and> in_y_domain l2 (snd p)"
      by auto
    define a1 where "a1 = snd (snd l1) - snd (fst l1)"
    define b1 where "b1 = fst (fst l1) - fst (snd l1)"
    define c1 where "c1 = fst (fst l1) * snd (snd l1) - fst (snd l1) * snd (fst l1)"
    define a2 where "a2 = snd (snd l2) - snd (fst l2)"
    define b2 where "b2 = fst (fst l2) - fst (snd l2)" 
    define c2 where "c2 = fst (fst l2) * snd (snd l2) - fst (snd l2) * snd (fst l2)"    
    define det_val where "det_val = det2 (a1, b1) (a2,b2)"
    have det_val_def': "det_val = a1 * b2 - a2 * b1" unfolding det_val_def by auto  
    note coeffs = a1_def b1_def c1_def a2_def b2_def c2_def        
    from np have 0: "\<not> det2 (a1, b1) (a2, b2) = 0 \<or> det2 (b1, c1) (b2, c2) = 0" 
      unfolding parallel_lines_def Let_def coeffs by auto
    from na have "det2 (b1, c1) (b2, c2) \<noteq> 0 \<or> det2 (a1, b1) (a2, b2) \<noteq> 0"        
      unfolding not_aligned_def Let_def coeffs by auto
    with 0 have "det2 (a1, b1) (a2, b2) \<noteq> 0" by auto
    with det_val_def' have "det_val \<noteq> 0" unfolding det_val_def by auto    
    with p_def have p_def': "p = (1 / det_val) *\<^sub>R (b2 * c1 - b1 * c2, a1 * c2 - a2 * c1)" 
      unfolding find_intersection_def Let_def coeffs det_val_def by auto
    hence fst_p_def: "fst p = (1 / det_val) * (b2 * c1 - b1 * c2)" and 
          snd_p_def: "snd p = (1 / det_val) * (a1 * c2 - a2 * c1)" 
      by auto
    have 1: "a1 * fst p + b1 * snd p = c1"  
    proof -
      have "a1 * fst p + b1 * snd p = a1 * (1 / det_val) * (b2 * c1 - b1 * c2) + 
                                      b1 * (1 / det_val) * (a1 * c2 - a2 * c1)"
        using fst_p_def snd_p_def by auto
      also have "... = (a1 * (b2 * c1 - b1 * c2) + b1 * (a1 * c2 - a2 * c1)) * (1 / det_val)"
        by (auto simp add:algebra_simps)
      also have "... = (a1 * b2 * c1 - b1 * a2 * c1) * (1 / det_val)"
        by (auto simp add:algebra_simps)
      also have "... = c1 * (a1 * b2 - a2 * b1) * (1 / det_val)"
        by (auto simp add:algebra_simps)
      also have "... = c1" using `det_val \<noteq> 0` unfolding det_val_def' by auto
      finally show "a1 * fst p + b1 * snd p = c1" by auto          
    qed      
    have 2: "a1 * fst (fst l1) + b1 * snd (fst l1) = c1"
      unfolding coeffs by (auto simp add:algebra_simps)            
    have 3: "a1 * fst (snd l1) + b1 * snd (snd l1) = c1" 
      unfolding coeffs by (auto simp add:algebra_simps)
    from id have 31: "fst p \<in> closed_segment (fst (fst l1)) (fst (snd l1))"
      using in_x_domain_eq_fst_closed_segment by auto
    have 4: "a2 * fst p + b2 * snd p = c2" 
    proof -
      have "a2 * fst p + b2 * snd p = a2 * (1 / det_val) * (b2 * c1 - b1 * c2) + 
                                      b2 * (1 / det_val) * (a1 * c2 - a2 * c1)"
        using fst_p_def snd_p_def by auto
      also have "... = (a2 * (b2 * c1 - b1 * c2) + b2 * (a1 * c2 - a2 * c1)) * (1 / det_val)"
        by (auto simp add:algebra_simps)
      also have "... = (- a2 * b1 * c2 + b2 * a1 * c2) * (1 / det_val)"
        by (auto simp add:algebra_simps)
      also have "... = c2 * (a1 * b2 - a2 * b1) * (1 / det_val)"
        by (auto simp add:algebra_simps)
      also have "... = c2" using `det_val \<noteq> 0` unfolding det_val_def' by auto
      finally show "a2 * fst p + b2 * snd p = c2" by auto    
    qed      
    have 5: "a2 * fst (fst l2) + b2 * snd (fst l2) = c2" 
      unfolding coeffs by (auto simp add:algebra_simps)
    have 6: "a2 * fst (snd l2) + b2 * snd (snd l2) = c2"
      unfolding coeffs by (auto simp add:algebra_simps)
    consider "fst (fst l1) \<noteq> fst (snd l1) \<and> fst (fst l2) \<noteq> fst (snd l2)" | 
             "fst (fst l1) = fst (snd l1) \<and> fst (fst l2) \<noteq> fst (snd l2)" | 
             "fst (fst l1) \<noteq> fst (snd l1) \<and> fst (fst l2) = fst (snd l2)" | 
             "fst (fst l1) = fst (snd l1) \<and> fst (fst l2) = fst (snd l2)"  by blast  
    thus ?thesis 
    proof (cases)
      case 1
      note case_one = this  
      from case_one have "\<not> (a1 = 0 \<and> b1 = 0)" unfolding coeffs
        using prod_eqI by fastforce
      from t1[OF 31 `a1 * fst p + b1 * snd p = c1` 2 3 `\<not> (a1 = 0 \<and> b1 = 0)`] 1 
        have *: "p \<in> closed_segment (fst l1) (snd l1)" by auto        
      from case_one have "\<not> (a2 = 0 \<and> b2 = 0)" unfolding coeffs
        using prod_eqI by fastforce
      from id have "fst p \<in> closed_segment (fst (fst l2)) (fst (snd l2))"
        using in_x_domain_eq_fst_closed_segment by auto
      from t1[OF this 4 5 6 `\<not> (a2 = 0 \<and> b2 = 0)`] 1 
      have "p \<in> closed_segment (fst l2) (snd l2)" by auto  
      then show ?thesis using * by blast
    next
      case 2
      with case_one_top have "in_x_domain l1 (fst p) \<and> in_x_domain l2 (fst p)"  
        by auto
      with 2 have "fst p = fst (fst l1)" and "fst p = fst (snd l1)" by auto   
      hence tis: "fst p \<in> closed_segment (fst (fst l1)) (fst (snd l1))" by auto
      from `fst p = fst (fst l1)` and `fst p = fst (snd l1)` have "b1 = 0" unfolding coeffs
          by auto
      from 2 have "b2 \<noteq> 0" unfolding coeffs by auto
      from det_val_def' `b1 = 0` `det_val \<noteq> 0` have "a1 * b2 \<noteq> 0" by auto
      with `b2 \<noteq> 0` have "a1 \<noteq> 0" by auto    
      with `b1 = 0` have "\<not> (a1 = 0 \<and> b1 = 0)" by auto
      from id2 have "in_y_domain l1 (snd p)" by auto
      hence "snd p \<in> closed_segment (snd (fst l1)) (snd (snd l1))" 
        unfolding in_y_domain_eq_snd_closed_segment by auto        
      from t2[OF tis this 1 `a1 * fst (fst l1) + b1 * snd (fst l1) = c1` 3 `\<not> (a1 = 0 \<and> b1 = 0)`] 2    
      have "p \<in> closed_segment (fst l1) (snd l1)"  by (metis prod.collapse)
      from id have "fst p \<in> closed_segment (fst (fst l2)) (fst (snd l2))" 
        using in_x_domain_eq_fst_closed_segment by auto
      from 2 have "\<not> (a2 = 0 \<and> b2 = 0)" unfolding coeffs using prod_eqI by fastforce    
      from t1[OF `fst p \<in> closed_segment (fst (fst l2)) (fst (snd l2))` 4 5 6 this] 2
        have "p \<in> closed_segment (fst l2) (snd l2)" by (metis prod.collapse)
      with `p \<in> closed_segment (fst l1) (snd l1)` show ?thesis by blast 
    next
      case 3
      with case_one_top have "in_x_domain l1 (fst p) \<and> in_x_domain l2 (fst p)" by auto
      with 3 have "fst p = fst (fst l2)" and "fst p = fst (snd l2)" by auto
      hence tis: "fst p \<in> closed_segment (fst (fst l2)) (fst (snd l2))" by auto
      from `fst p = fst (fst l2)` and `fst p = fst (snd l2)` have "b2 = 0" unfolding coeffs
        by auto
      from 3 have "b1 \<noteq> 0" unfolding coeffs by auto
      from det_val_def' `b2 = 0` `det_val \<noteq> 0` have "a2 * b1 \<noteq> 0" by auto
      with `b1 \<noteq> 0` have "a2 \<noteq> 0" by auto
      with `b2 = 0` have "\<not> (a2 = 0 \<and> b2 = 0)" by auto
      from id2 have "in_y_domain l2 (snd p)" by auto
      hence "snd p \<in> closed_segment (snd (fst l2)) (snd (snd l2))" 
        unfolding in_y_domain_eq_snd_closed_segment by auto
      from t2[OF tis this 4 `a2 * fst (fst l2) + b2 * snd (fst l2) = c2` 
        `a2 * fst (snd l2) + b2 * snd (snd l2) = c2` `\<not> (a2 = 0 \<and> b2 = 0)`] 3
        have "p \<in> closed_segment (fst l2) (snd l2)" by (metis prod.collapse)
      from 3 have "\<not> (a1 = 0 \<and> b1 = 0)" unfolding coeffs using prod_eqI by fastforce
      from t1[OF `fst p \<in> closed_segment (fst (fst l1)) (fst (snd l1))` 1 2 
          `a1 * fst (snd l1) + b1 * snd (snd l1) = c1` `\<not> (a1 = 0 \<and> b1 = 0)`] 3
        have "p \<in> closed_segment (fst l1) (snd l1)" by (metis prod.collapse)
      with `p \<in> closed_segment (fst l2) (snd l2)` show ?thesis by blast
    next
      case 4
      from case_one_top  have "\<not> parallel_lines l1 l2" by auto
      with 4 have "False" unfolding parallel_lines_def Let_def 
        using \<open>det2 (a1, b1) (a2, b2) \<noteq> 0\<close> b1_def b2_def by auto    
      then show ?thesis by auto
    qed            
  next
    case 2
    hence "\<not> parallel_lines l1 l2" and "\<not> not_aligned l1 l2" and "overlaps l1 l2" and "overlaps_y l1 l2" 
      by auto  
    consider "fst (fst l1) \<le> fst (snd l1) \<and> fst (fst l2) \<le> fst (snd l2)" | 
             "fst (fst l1) \<le> fst (snd l1) \<and> fst (fst l2) > fst (snd l2)" | 
             "fst (fst l1) > fst (snd l1) \<and> fst (fst l2) \<le> fst (snd l2)" | 
             "fst (fst l1) > fst (snd l1) \<and> fst (fst l2) > fst (snd l2)"
      by linarith            
    then show ?thesis
    proof (cases)
      case 1
      with t3[OF `\<not> parallel_lines l1 l2` `\<not> not_aligned l1 l2` `overlaps l1 l2` `overlaps_y l1 l2` neq1 neq2]  
      show ?thesis by auto
    next
      case 2
      define l2' where "l2' \<equiv> (snd l2, fst l2)"
      from `\<not> parallel_lines l1 l2` have "\<not> parallel_lines l1 l2'" 
        unfolding l2'_def using parallel_invariant by metis 
      from `\<not> not_aligned l1 l2` have "\<not> not_aligned l1 l2'"
        unfolding l2'_def using not_aligned_invariant by metis
      from `overlaps l1 l2` have "overlaps l1 l2'" 
        unfolding l2'_def using overlaps_invariant by metis
      from `overlaps_y l1 l2` have "overlaps_y l1 l2'"
        unfolding l2'_def using overlaps_y_invariant by  metis
      with t3[OF `\<not> parallel_lines l1 l2'` `\<not> not_aligned l1 l2'` `overlaps l1 l2'` `overlaps_y l1 l2'`] 
        neq1 neq2 2 show ?thesis
        unfolding l2'_def
        by (simp add: Convex_Euclidean_Space.closed_segment_commute)
    next
      case 3
      define l1' where "l1' \<equiv> (snd l1, fst l1)"
      from `\<not> parallel_lines l1 l2` have "\<not> parallel_lines l1' l2" unfolding l1'_def
        using parallel_invariant' by metis
      from `\<not> not_aligned l1 l2` have "\<not> not_aligned l1' l2" unfolding l1'_def
        using not_aligned_invariant' by metis
      from `overlaps l1 l2` have "overlaps l1' l2" unfolding l1'_def
        using overlaps_invariant' by metis
      from `overlaps_y l1 l2` have "overlaps_y l1' l2" unfolding l1'_def
        using overlaps_y_invariant' by metis          
      with t3[OF `\<not> parallel_lines l1' l2` `\<not> not_aligned l1' l2` `overlaps l1' l2` `overlaps_y l1' l2`]
      neq1 neq2 3 show ?thesis unfolding l1'_def 
      by (simp add: Convex_Euclidean_Space.closed_segment_commute)
    next
      case 4
      define l1' where "l1' \<equiv> (snd l1, fst l1)"
      define l2' where "l2' \<equiv> (snd l2, fst l2)"
      from `\<not> parallel_lines l1 l2` have "\<not> parallel_lines l1' l2'" unfolding l1'_def l2'_def
        using parallel_invariant2 by metis
      from `\<not> not_aligned l1 l2` have "\<not> not_aligned l1' l2'" unfolding l1'_def l2'_def
        using not_aligned_invariant2 by metis
      from `overlaps l1 l2` have "overlaps l1' l2'" unfolding l1'_def l2'_def
        using overlaps_invariant2 by metis
      from `overlaps_y l1 l2` have "overlaps_y l1' l2'" unfolding l1'_def l2'_def
        using overlaps_y_invariant2 by metis 
      from t3[OF `\<not> parallel_lines l1' l2'` `\<not> not_aligned l1' l2'` `overlaps l1' l2'` `overlaps_y l1' l2'`]
      neq1 neq2 4
      show ?thesis unfolding l1'_def l2'_def       
        by (simp add: Convex_Euclidean_Space.closed_segment_commute) 
    qed      
  qed  
qed  
  
definition segment_intersection1 :: "real2 \<times> real2 \<Rightarrow> real2 \<times> real2 \<Rightarrow> bool" where
  "segment_intersection1 l1 l2 \<equiv> (if fst l1 \<noteq> snd l1 then 
                                      if fst (fst l1) \<noteq> fst (snd l1) then 
                                         line_equation (fst l1) (snd l1) (fst (fst l2)) = snd (fst l2) \<and> 
                                         in_x_domain l1 (fst (fst l2))       
                                      else 
                                         fst (fst l2) = fst (fst l1) \<and> 
                                         in_y_domain l1 (snd (fst l2))
                                   else if fst l2 \<noteq> snd l2 then 
                                      if fst (fst l2) \<noteq> fst (snd l2) then 
                                         line_equation (fst l2) (snd l2) (fst (fst l1)) = snd (fst l1) \<and>
                                         in_x_domain l2 (fst (fst l1))
                                      else 
                                         fst (fst l1) = fst (fst l2) \<and> 
                                         in_y_domain l2 (snd (fst l1))
                                   else 
                                      fst l1 = fst l2)"  
  
lemma straigh_point_closed_segment:
  assumes "fst p1 = fst p2"
  assumes "in_y_domain (p1, p2) y"
  assumes "x = fst p1"
  shows "(x,y) \<in> closed_segment p1 p2"
proof - 
  from assms(2) have "y \<in> closed_segment (snd p1) (snd p2)"
    using in_y_domain_eq_snd_closed_segment by fastforce
  then obtain t where "y = snd p1 + t * (snd p2 - snd p1)" and "0 \<le> t" and "t \<le> 1"
    unfolding closed_segment_def by (auto simp add:algebra_simps)
  from assms(1) assms(3) have "x = fst p1 + t * (fst p2 - fst p1)" by auto      
  with `y = snd p1 + t * (snd p2 - snd p1)` have "(x,y) = p1 + t*\<^sub>R (p2 - p1)"
    by (simp add: minus_prod_def plus_prod_def)
  hence "(x,y) = (1 - t)*\<^sub>R p1 + t*\<^sub>R p2"
  proof -
    have "\<forall>x1. (1::real) - x1 = 1 + - 1 * x1"
      by auto
    then have "(x, y) = t *\<^sub>R p2 - t *\<^sub>R p1 + (t *\<^sub>R p1 + (1 + - 1 * t) *\<^sub>R p1)"
      by (metis (no_types) \<open>(x, y) = p1 + t *\<^sub>R (p2 - p1)\<close> add.commute real_vector.scale_right_diff_distrib scaleR_collapse)
    then show ?thesis
      by simp
  qed
  thus ?thesis using `0 \<le> t` and `t \<le> 1` unfolding closed_segment_def by auto      
qed
  
theorem segment_intersection1_correctness:
  assumes "fst l1 = snd l1 \<or> fst l2 = snd l2"  
  assumes "segment_intersection1 l1 l2"
  shows "\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2)"
proof -
  consider "fst l1 \<noteq> snd l1" | "fst l2 \<noteq> snd l2" | "fst l1 = snd l1 \<and> fst l2 = snd l2"
    using assms(1) by auto
  thus ?thesis
  proof (cases)
    case 1
    have "fst (fst l1) \<noteq> fst (snd l1) \<or> fst (fst l1) = fst (snd l1)" by auto
    moreover
    { assume 11: "fst (fst l1) \<noteq> fst (snd l1)"
      from assms(2) and 1 and 11 have "line_equation (fst l1) (snd l1) (fst (fst l2)) = snd (fst l2)"
        and id: "in_x_domain l1 (fst (fst l2))"
        unfolding segment_intersection1_def by auto
      from line_equation_pil[OF 11 this(1)] have "fst l2 \<in> points_in_lines (fst l1) (snd l1)"    
        by auto
      from pil_also_closed_segment[OF this _ 11] id in_x_domain_eq_fst_closed_segment
        have *: "fst l2 \<in> closed_segment (fst l1) (snd l1)" by auto
      have "fst l2 \<in> closed_segment (fst l2) (snd l2)" by auto    
      with * have ?thesis by fastforce }
    moreover
    { assume 12: "fst (fst l1) = fst (snd l1)"
      from assms(2) and 1 and 12 have "fst (fst l2) = fst (fst l1)" and id2: "in_y_domain l1 (snd (fst l2))"
        unfolding segment_intersection1_def by auto
      hence "fst l2 \<in> closed_segment (fst l1) (snd l1)" using in_y_domain_eq_snd_closed_segment
        and 12 using straigh_point_closed_segment[OF 12 _ `fst (fst l2) = fst (fst l1)`] id2
        by (metis prod.collapse)
      have "fst l2 \<in> closed_segment (fst l2) (snd l2)" by auto
      with `fst l2 \<in> closed_segment (fst l1) (snd l1)` have ?thesis by fastforce }            
    ultimately show ?thesis by auto
  next
    case 2
    with assms(1) have 13: "fst l1 = snd l1" by auto  
    have "fst (fst l2) \<noteq> fst (snd l2) \<or> fst (fst l2) = fst (snd l2)" by auto
    moreover
    { assume 21: "fst (fst l2) \<noteq> fst (snd l2)"
      from assms(2) and 2 and 21 and 13 have "line_equation (fst l2) (snd l2) (fst (fst l1)) = snd (fst l1)"
        and id: "in_x_domain l2 (fst (fst l1))"
        unfolding segment_intersection1_def by auto 
      from line_equation_pil[OF 21 this(1)] have "fst l1 \<in> points_in_lines (fst l2) (snd l2)"
        by auto
      from pil_also_closed_segment[OF this _ 21] id in_x_domain_eq_fst_closed_segment
      have *: "fst l1 \<in> closed_segment (fst l2) (snd l2)" by auto
      have "fst l1 \<in> closed_segment (fst l1) (snd l1)" by auto
      with * have ?thesis by fastforce }
    moreover
    { assume 22: "fst (fst l2) = fst (snd l2)"
      from assms(2) and 2 and 22 and 13 have "fst (fst l1) = fst (fst l2)" and id2: "in_y_domain l2 (snd (fst l1))"
        unfolding segment_intersection1_def by auto
      hence "fst l1 \<in> closed_segment (fst l2) (snd l2)" 
        using straigh_point_closed_segment[OF 22 _ `fst (fst l1) = fst (fst l2)`] id2
        by (metis prod.collapse)
      have "fst l1 \<in> closed_segment (fst l1) (snd l1)" by auto
      with `fst l1 \<in> closed_segment (fst l2) (snd l2)` have ?thesis by fastforce }
    ultimately show ?thesis by auto
  next
    case 3
    then show ?thesis  using assms(2) segment_intersection1_def by auto
  qed
qed
  
lemma snd_closed_segment[simp]: "snd ` closed_segment a b = closed_segment (snd a) (snd b)"
  by (force simp: closed_segment_def)  
  
theorem segment_intersection1_completeness:
  assumes "fst l1 = snd l1 \<or> fst l2 = snd l2"  
  assumes "\<not> segment_intersection1 l1 l2"  
  shows "\<not> (\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))" (is "\<not> ?E")
proof -  
  consider "fst l1 \<noteq> snd l1" | "fst l2 \<noteq> snd l2" | "fst l1 = snd l1 \<and> fst l2 = snd l2"
    using assms(1) by auto
  thus ?thesis
  proof (cases)
    case 1
    from assms(1) and 1 have "fst l2 = snd l2" by auto
    have "fst (fst l1) \<noteq> fst (snd l1) \<or> fst (fst l1) = fst (snd l1)" by auto
    moreover
    { assume 11: "fst (fst l1) \<noteq> fst (snd l1)"
      from assms(2) and 1 and 11 have fc: "\<not> line_equation (fst l1) (snd l1) (fst (fst l2)) = snd (fst l2) \<or> 
                                         \<not> in_x_domain l1 (fst (fst l2))"
        unfolding segment_intersection1_def by auto
      moreover
      { assume "\<not> line_equation (fst l1) (snd l1) (fst (fst l2)) = snd (fst l2)"
        from line_equation_pil2[OF 11 this] have "fst l2 \<notin> points_in_lines (fst l1) (snd l1)" by auto          
        with closed_segment_subset_pil have "fst l2 \<notin> closed_segment (fst l1) (snd l1)" by fastforce
        from `fst l2 = snd l2` have "closed_segment (fst l2) (snd l2) = {fst l2}" by auto
        hence "\<forall>p. p \<in> closed_segment (fst l2) (snd l2) \<longrightarrow> p \<notin> closed_segment (fst l1) (snd l1)"
          using `fst l2 \<notin> closed_segment (fst l1) (snd l1)` by auto
        hence ?thesis by auto }
      moreover
      { assume "\<not> in_x_domain l1 (fst (fst l2))"
        with in_x_domain_eq_fst_closed_segment have "fst (fst l2) \<notin> closed_segment (fst (fst l1)) (fst (snd l1))"
          by auto
        hence "fst l2 \<notin> closed_segment (fst l1) (snd l1)"  using fst_closed_segment by blast
        from `fst l2 = snd l2` have "closed_segment (fst l2) (snd l2) = {fst l2}" by auto
        hence "\<forall>p. p \<in> closed_segment (fst l2) (snd l2) \<longrightarrow> p \<notin> closed_segment (fst l1) (snd l1)"
          using `fst l2 \<notin> closed_segment (fst l1) (snd l1)` by auto
        hence ?thesis by auto }
      ultimately have ?thesis by auto }
    moreover
    { assume 12: "fst (fst l1) = fst (snd l1)"
      hence req: "\<forall>p . p \<in> closed_segment (fst l1) (snd l1) \<longrightarrow> fst p = fst (fst l1)"
        by (smt in_segment_fst_ge in_segment_fst_le prod.collapse)
      from assms(2) 12 and 1 have fc: "fst (fst l2) \<noteq> fst (fst l1) \<or>  \<not> in_y_domain l1 (snd (fst l2))"
        unfolding segment_intersection1_def by auto
      moreover
      { assume "fst (fst l2) \<noteq> fst (fst l1)"
        with req have "fst l2 \<notin> closed_segment (fst l1) (snd l1)" by blast
        from `fst l2 = snd l2` have "closed_segment (fst l2) (snd l2) = {fst l2}" by auto
        hence "\<forall>p. p \<in> closed_segment (fst l2) (snd l2) \<longrightarrow> p \<notin> closed_segment (fst l1) (snd l1)"
          using `fst l2 \<notin> closed_segment (fst l1) (snd l1)` by auto
        hence ?thesis by auto  }
      moreover
      { assume "\<not> in_y_domain l1 (snd (fst l2))"
        with in_y_domain_eq_snd_closed_segment have "snd (fst l2) \<notin> closed_segment (snd (fst l1)) (snd (snd l1))"
          by auto
        hence "fst l2 \<notin> closed_segment (fst l1) (snd l1)" using snd_closed_segment by blast
        from `fst l2 = snd l2` have "closed_segment (fst l2) (snd l2) = {fst l2}" by auto
        hence "\<forall>p. p \<in> closed_segment (fst l2) (snd l2) \<longrightarrow> p \<notin> closed_segment (fst l1) (snd l1)"
          using `fst l2 \<notin> closed_segment (fst l1) (snd l1)` by auto
        hence ?thesis by auto }
      ultimately have ?thesis by auto }            
    ultimately show ?thesis by auto
  next
    case 2
    from assms(1) and 2 have "fst l1 = snd l1" by auto
    have "fst (fst l2) \<noteq> fst (snd l2) \<or> fst (fst l2) = fst (snd l2)" by auto
    moreover
    { assume 21: "fst (fst l2) \<noteq> fst (snd l2)"
      with 2 and assms(2) have "\<not> line_equation (fst l2) (snd l2) (fst (fst l1)) = snd (fst l1) \<or>
                                         \<not> in_x_domain l2 (fst (fst l1))"  
        using `fst l1 = snd l1` unfolding segment_intersection1_def by auto
      moreover
      { assume "\<not> line_equation (fst l2) (snd l2) (fst (fst l1)) = snd (fst l1)"
        from line_equation_pil2[OF 21 this] have "fst l1 \<notin> points_in_lines (fst l2) (snd l2)"
          by auto
        with closed_segment_subset_pil have "fst l1 \<notin> closed_segment (fst l2) (snd l2)" by blast
        from `fst l1 = snd l1` have "closed_segment (fst l1) (snd l1) = {fst l1}" by auto
        hence "\<forall>p. p \<in> closed_segment (fst l1) (snd l1) \<longrightarrow> p \<notin> closed_segment (fst l2) (snd l2)" 
          using `fst l1 \<notin> closed_segment (fst l2) (snd l2)` by auto
        hence ?thesis by auto }
      moreover
      { assume "\<not> in_x_domain l2 (fst (fst l1))"
        with in_x_domain_eq_fst_closed_segment  have "fst (fst l1) \<notin> closed_segment (fst (fst l2)) (fst (snd l2))"  
          by auto
        hence "fst l1 \<notin> closed_segment (fst l2) (snd l2)" using fst_closed_segment by blast
        from `fst l1 = snd l1` have "closed_segment (fst l1) (snd l1) = {fst l1}" by auto
        hence "\<forall>p. p \<in> closed_segment (fst l1) (snd l1) \<longrightarrow> p \<notin> closed_segment (fst l2) (snd l2)" 
          using `fst l1 \<notin> closed_segment (fst l2) (snd l2)` by auto
        hence ?thesis by auto }
      ultimately have ?thesis by auto }
    moreover
    { assume 22: "fst (fst l2) = fst (snd l2)"
      have req: "\<forall>p. p \<in> closed_segment (fst l2) (snd l2) \<longrightarrow> fst p = fst (fst l2)"
        by (smt "22" in_segment_fst_ge in_segment_fst_le prod.collapse)
      from assms(2) 22 and 2 have " fst (fst l2) \<noteq> fst (fst l1) \<or>  \<not> in_y_domain l2 (snd (fst l1))" 
        unfolding segment_intersection1_def using `fst l1  = snd l1` by auto
      moreover
      { assume "fst (fst l2) \<noteq> fst (fst l1)"
        with req have "fst l1 \<notin> closed_segment (fst l2) (snd l2)"  by metis
        from `fst l1 = snd l1` have "closed_segment (fst l1) (snd l1) = {fst l1}" by auto    
        hence "\<forall>p. p \<in> closed_segment (fst l1) (snd l1) \<longrightarrow> p \<notin> closed_segment (fst l2) (snd l2)"
          using `fst l1 \<notin> closed_segment (fst l2) (snd l2)` by auto
        hence ?thesis by auto }
      moreover
      { assume "\<not> in_y_domain l2 (snd (fst l1))"
        with in_y_domain_eq_snd_closed_segment have "snd (fst l1) \<notin> closed_segment (snd (fst l2)) (snd (snd l2))"
          by auto
        hence "fst l1 \<notin> closed_segment (fst l2) (snd l2)" using snd_closed_segment by blast
        from `fst l1 = snd l1` have "closed_segment (fst l1) (snd l1) = {fst l1}" by auto     
        hence "\<forall>p. p \<in> closed_segment (fst l1) (snd l1) \<longrightarrow> p \<notin> closed_segment (fst l2) (snd l2)"
          using `fst l1 \<notin> closed_segment (fst l2) (snd l2)` by auto
        hence ?thesis by auto }
      ultimately have ?thesis by auto }      
    ultimately show ?thesis by auto 
  next
    case 3
    with assms(2) have "fst l1 \<noteq> fst l2" unfolding segment_intersection1_def by auto        
    then show ?thesis using 3 by auto
  qed  
qed
    
definition segment_intersection :: "real2 \<times> real2 \<Rightarrow> real2 \<times> real2 \<Rightarrow> bool" where
  "segment_intersection l1 l2 \<equiv> (if fst l1 = snd l1 \<or> fst l2 = snd l2 then 
                                    segment_intersection1 l1 l2
                                 else 
                                    segments_intersects2 l1 l2)"
  
theorem segment_intersection_correctness: 
  assumes "segment_intersection l1 l2"
  shows "\<exists>p . p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2)"
proof (cases "fst l1 = snd l1 \<or> fst l2 = snd l2")
  case True
  with assms have "segment_intersection1 l1 l2" unfolding segment_intersection_def by auto  
  then show ?thesis using segment_intersection1_correctness[OF True] by auto
next
  case False
  with assms have "segments_intersects2 l1 l2" unfolding segment_intersection_def by auto  
  then show ?thesis using segments_intersecst_correctness_some False by auto 
qed
  
theorem segment_intersection_completeness:
  assumes "\<not> segment_intersection l1 l2"
  shows "\<not> (\<exists>p . p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"  
proof (cases "fst l1 = snd l1 \<or> fst l2 = snd l2")
  case True
  with assms have "\<not> segment_intersection1  l1 l2" unfolding segment_intersection_def by auto  
  with segment_intersection1_completeness[OF True this] show ?thesis by auto
next
  case False
  with assms have "\<not> segments_intersects2 l1 l2" unfolding segment_intersection_def by auto  
  with segments_intersects_correctness_none show ?thesis by auto
qed

fun segments_intersect_polychain :: "real2 \<times> real2 \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> bool" where
  "segments_intersect_polychain line [] = False" | 
  "segments_intersect_polychain line (c # cs) = 
                (if segment_intersection line c then True else segments_intersect_polychain line cs)"
  
lemma not_segments_intersect_polychain_cons:
  assumes "\<not> segments_intersect_polychain line (c # cs)"
  shows "\<not> segments_intersect_polychain line cs"
  using assms
proof (induction cs arbitrary:c)
  case Nil
  then show ?case by auto
next
  case (Cons a cs)
  note case_cons = this
  hence "\<not> segment_intersection line c" by auto
  with `\<not> segments_intersect_polychain line (c # a # cs)` 
    show "\<not> segments_intersect_polychain line (a # cs)" by auto
qed    
      
theorem not_segment_intersect_poly_correct:
  assumes "c \<in> set cs"
  assumes "\<not> segments_intersect_polychain line cs"
  shows "\<not> (\<exists>p. p \<in> closed_segment (fst line) (snd line) \<and> p \<in> closed_segment (fst c) (snd c))"
  using assms
proof (induction cs)
  case Nil
  then show ?case by auto
next
  case (Cons a cs)
  note case_cons = this
  from `c \<in> set (a # cs)` consider "c = a" | "c \<in> set cs" by auto    
  then show ?case
  proof (cases)
    case 1
    with `\<not> segments_intersect_polychain line (a # cs)` have "\<not> segment_intersection line a"
      by auto        
    with segment_intersection_completeness[OF this] show ?thesis using `c = a` by auto
  next
    case 2
    with not_segments_intersect_polychain_cons[OF `\<not> segments_intersect_polychain line (a # cs)`] 
    have "\<not> segments_intersect_polychain line cs" by simp
    from case_cons(1)[OF 2 this] show ?thesis by auto
  qed      
qed
  
theorem segment_intersect_poly_correct:
  assumes "segments_intersect_polychain line cs"
  shows "\<exists>c p. c \<in> set cs \<and> p \<in> closed_segment (fst line) (snd line) \<and> p \<in> closed_segment (fst c) (snd c)"
  using assms
proof (induction cs)
  case Nil
  then show ?case by auto
next
  case (Cons a cs)
  note case_cons = this
  consider "segment_intersection line a" | "\<not> segment_intersection line a" by auto
  then show ?case 
  proof (cases)
    case 1
    from segment_intersection_correctness[OF this] obtain p where "p \<in> closed_segment (fst line) (snd line)"
      and "p \<in> closed_segment (fst a) (snd a)" by auto
    then show ?thesis  by (meson list.set_intros(1))
  next
    case 2
    with `segments_intersect_polychain line (a # cs)` have "segments_intersect_polychain line cs"
      by auto
    from case_cons(1)[OF this] show ?thesis by (meson list.set_intros)
  qed    
qed
  
subsection "Lanelet"
  
locale lanelet = le: lanelet_simple_boundary points_le + ri: lanelet_simple_boundary points_ri
  for points_le and points_ri +
  assumes non_intersecting: "\<forall>t1 \<in> {0..1}. \<forall>t2 \<in> {0..1}. le.curve_eq t1 \<noteq> ri.curve_eq t2"
  assumes same_init_x: "fst (pathstart le.curve_eq) = fst (pathstart ri.curve_eq)"
  assumes same_final_x: "fst (pathfinish le.curve_eq) = fst (pathfinish ri.curve_eq)"    
begin  
       
lemma same_init_x_alt_def:
  "fst (fst le.first_chain) = fst (fst ri.first_chain)"
  using le.pathstart_first_point ri.pathstart_first_point same_init_x by auto
    
lemma same_final_x_alt_def:
  "fst (snd (last points_le)) = fst (snd (last points_ri))"
  using le.pathfinish_last_point ri.pathfinish_last_point same_final_x by auto
 
theorem equal_curve_setX:
  "curve.setX le.curve_eq {0..1} = curve.setX ri.curve_eq {0..1}"
  using le.curve_setX_interval ri.curve_setX_interval same_init_x same_final_x
  same_init_x_alt_def same_final_x_alt_def by auto
    
theorem curve_setX_nonempty: 
    "curve.setX le.curve_eq {0 .. 1} \<noteq> {}"
proof -    
  have "fst le.first_point < fst le.last_point"
    by (metis hd_Cons_tl monotone_polychain_fst_last ri.monotone ri.nonempty_points 
        same_final_x_alt_def same_init_x_alt_def) 
  with le.curve_setX_interval show ?thesis by auto
qed
        
subsubsection "Naive way for determining direction"
  
text "Reversing the direction of the left polychain"  
  
definition reverse_le where
  "reverse_le \<equiv> rev (map (\<lambda>(x,y). (y,x)) points_le)"
  
theorem reverse_le_nonempty:
  "reverse_le \<noteq> []"  unfolding reverse_le_def using le.nonempty_points by auto

theorem polychain_reverse_le:
  "polychain reverse_le"
  unfolding reverse_le_def using polychain_rev_map le.poly_points by auto
           
definition lanelet_polygon where
  "lanelet_polygon \<equiv> close_polychain (connect_polychain reverse_le points_ri)"
  
theorem length_connect_polychain_reverse:
  "2 \<le> length (connect_polychain reverse_le points_ri)"
proof -
  from reverse_le_nonempty have 0: "1 \<le> length reverse_le"
    using linorder_le_less_linear by auto
  from ri.nonempty_points have "1 \<le> length points_ri"
    using linorder_le_less_linear by auto
  with 0 length_connect_polychain[of reverse_le points_ri] 
    show "2 \<le> length (connect_polychain reverse_le points_ri)" by auto
qed  
  
theorem min_length_lanelet_polygon:
  "2 \<le> length lanelet_polygon"
  unfolding lanelet_polygon_def using length_connect_polychain_reverse length_close_polychain
  order_trans by auto
    
theorem polychain_connect_polychain:
  "polychain (connect_polychain reverse_le points_ri)"
  using connect_polychain_preserve[OF polychain_reverse_le ri.poly_points reverse_le_nonempty 
    ri.nonempty_points] .
    
theorem connect_polychain_nonempty2:
  "connect_polychain reverse_le points_ri \<noteq> []"
  using connect_polychain_nonempty[OF polychain_reverse_le ri.poly_points reverse_le_nonempty 
    ri.nonempty_points] .
    
theorem polygon_lanelet_polygon:
  "polygon lanelet_polygon"
  using polygon_close_polychain[OF connect_polychain_nonempty2 polychain_connect_polychain] 
  unfolding lanelet_polygon_def .
      
theorem connect_reverse_le_points_ri_nonempty:
  "connect_polychain reverse_le points_ri \<noteq> []"
  using reverse_le_nonempty ri.nonempty_points
  unfolding connect_polychain_def Let_def by auto
    
theorem lanelet_polygon_nonempty:
  "lanelet_polygon \<noteq> []"
  using connect_reverse_le_points_ri_nonempty 
  unfolding lanelet_polygon_def close_polychain_def Let_def by auto

definition vertex_chain where
  "vertex_chain \<equiv> (case convex_hull_vertex3 lanelet_polygon of 
                    Some x \<Rightarrow> (case pre_and_post lanelet_polygon x of
                               Some (pre, post) \<Rightarrow> (pre, x, post)))"    
    
theorem chv_lanelet_polygon:
  "\<exists>x. convex_hull_vertex3 lanelet_polygon = Some x"
proof -
  obtain z and zs where "lanelet_polygon = z # zs" using lanelet_polygon_nonempty
    by (metis hd_Cons_tl)
  with cons_convex_hull_vertex_some show ?thesis by auto    
qed  
    
theorem pre_post_lanelet_polygon_chv:
  "\<exists>pre post. pre_and_post lanelet_polygon ((the \<circ> convex_hull_vertex3) lanelet_polygon) = 
                                                                                   Some (pre, post)"
  using chv_lanelet_polygon pre_pos_convex_hull_vertex[OF min_length_lanelet_polygon 
      polygon_lanelet_polygon] unfolding comp_def by auto
    
theorem 
  "\<exists>pre x post. vertex_chain = (pre, x, post)"
  unfolding vertex_chain_def using pre_post_lanelet_polygon_chv chv_lanelet_polygon by auto  

lemma hd_smallest_le:
  assumes "element_of_polychain z points_le"
  shows "z = fst (hd points_le) \<or> fst (fst (hd points_le)) < fst z"
  using assms hd_smallest le.monotone le.nonempty_points by blast

lemma hd_smallest_ri:
  assumes "element_of_polychain z points_ri"
  shows "z = fst (hd points_ri) \<or> fst (fst (hd points_ri)) < fst z"
  using assms hd_smallest ri.monotone ri.nonempty_points by blast
    
definition dir_right :: "bool" where
  "dir_right \<equiv> (case vertex_chain of (pre, x, post) \<Rightarrow> ccw' pre x post)"
  
subsubsection "Interpretation of lanelet as simple roads"  
  
interpretation sr: simple_road "le.curve_eq" "ri.curve_eq" "{0..1}"
proof
  show "convex {0::real..1}"   by auto
next
  show "compact {0::real..1}"  by auto
next
  show "continuous_on {0..1} le.curve_eq"
    using curve_eq_cont[OF le.nonempty_points le.poly_points] by auto      
next
  show "inj_on le.curve_eq {0..1}"
    using inj_on_curve_eq[OF le.monotone _ le.nonempty_points] by auto 
next
  have eq:"curve.curve_eq_x le.curve_eq = (fst \<circ> le.curve_eq)" 
    unfolding curve.curve_eq_x_def[OF le.curve_eq_is_curve] by auto    
  show "bij_betw (curve.curve_eq_x le.curve_eq) {0..1} (curve.setX le.curve_eq {0..1})"
    unfolding bij_betw_def
  proof 
    from strict_mono_in_curve_eq3[OF le.monotone _ le.nonempty_points]
      have "strict_mono_in (fst \<circ> le.curve_eq) {0..1}" by auto
    hence "inj_on (fst \<circ> le.curve_eq) {0..1}" using strict_imp_inj_on by auto
    with eq show "inj_on (curve.curve_eq_x le.curve_eq) {0..1}" by auto
  next
    show "curve.curve_eq_x le.curve_eq ` {0..1} = curve.setX le.curve_eq {0..1}"
      unfolding eq curve.setX_def[OF le.curve_eq_is_curve] by auto
  qed
next
  show "continuous_on {0..1} ri.curve_eq"
    using curve_eq_cont[OF ri.nonempty_points ri.poly_points] by auto
next
  show "inj_on ri.curve_eq {0..1}"
    using inj_on_curve_eq[OF ri.monotone _ ri.nonempty_points] by auto
next
  have eq:"curve.curve_eq_x ri.curve_eq = (fst \<circ> ri.curve_eq)" 
    unfolding curve.curve_eq_x_def[OF ri.curve_eq_is_curve] by auto    
  show "bij_betw (curve.curve_eq_x ri.curve_eq) {0..1} (curve.setX ri.curve_eq {0..1})"
    unfolding bij_betw_def
  proof 
    from strict_mono_in_curve_eq3[OF ri.monotone _ ri.nonempty_points]
      have "strict_mono_in (fst \<circ> ri.curve_eq) {0..1}" by auto
    hence "inj_on (fst \<circ> ri.curve_eq) {0..1}" using strict_imp_inj_on by auto
    with eq show "inj_on (curve.curve_eq_x ri.curve_eq) {0..1}" by auto
  next
    show "curve.curve_eq_x ri.curve_eq ` {0..1} = curve.setX ri.curve_eq {0..1}"
      unfolding eq curve.setX_def[OF ri.curve_eq_is_curve] by auto
  qed
next
  show "curve.setX le.curve_eq {0..1} \<inter> curve.setX ri.curve_eq {0..1} \<noteq> {}"
  using curve_setX_nonempty equal_curve_setX by blast  
next    
  fix x
  assume "x \<in> curve.setX le.curve_eq {0 .. 1} \<inter> curve.setX ri.curve_eq {0..1}"
  hence le: "x \<in> curve.setX le.curve_eq {0..1}" and ri: "x \<in> curve.setX ri.curve_eq {0..1}"
    by auto
  show "simple_boundary.f_of_x ri.curve_eq {0..1} x \<noteq> simple_boundary.f_of_x le.curve_eq {0..1} x"    
  proof (rule ccontr)
    assume "\<not> (simple_boundary.f_of_x ri.curve_eq {0..1} x \<noteq> simple_boundary.f_of_x le.curve_eq {0..1} x)"
    hence "simple_boundary.f_of_x ri.curve_eq {0..1} x = simple_boundary.f_of_x le.curve_eq {0..1} x"
      by auto
    then obtain y where ri_f: "simple_boundary.f_of_x ri.curve_eq {0..1} x = y" and
                        le_f: "simple_boundary.f_of_x le.curve_eq {0..1} x = y"
      using \<open>simple_boundary.f_of_x ri.curve_eq {0..1} x = simple_boundary.f_of_x le.curve_eq {0..1} x\<close> 
      by blast
    then obtain t1 and t2 where "t1 \<in> {0..1} \<and> ri.curve_eq t1 = (x,y)" and 
                                "t2 \<in> {0..1} \<and> le.curve_eq t2 = (x,y)"
      using ri.lsc_f_of_x_curve_eq[OF ri ri_f] le.lsc_f_of_x_curve_eq[OF le le_f] by auto
    with non_intersecting show "False" by force        
  qed    
qed

interpretation sr2: simple_road2 "le.curve_eq" "ri.curve_eq" "{0..1}"
proof 
  show "{0::real..1} \<noteq> {}" by auto
next
  have "curve.curve_eq_x le.curve_eq 0 < curve.curve_eq_x le.curve_eq 1 "
    using le.monotone 
    by (smt atLeastAtMost_iff comp_def curve.curve_eq_x_def le.curve_eq_is_curve le.nonempty_points 
                                                        strict_mono_in_curve_eq3 strict_mono_in_def)
  thus "strict_mono_in (curve.curve_eq_x le.curve_eq) {0..1}" using le.lsc_checking_strict_mono
    by auto
next
  have "curve.curve_eq_x ri.curve_eq 0 < curve.curve_eq_x ri.curve_eq 1 "
    using ri.monotone 
    by (smt atLeastAtMost_iff comp_def curve.curve_eq_x_def ri.curve_eq_is_curve ri.nonempty_points 
                                                        strict_mono_in_curve_eq3 strict_mono_in_def)                                                      
  thus "strict_mono_in (curve.curve_eq_x ri.curve_eq) {0..1}" using ri.lsc_checking_strict_mono
    by auto
next
  from non_intersecting show "\<forall>t\<in>{0..1}. le.curve_eq t \<noteq> ri.curve_eq t" by auto
next    
  show "ri.curve_eq differentiable at_right (Inf {0::real..1})" using ri.curve_eq_has_vector_derivative by (auto intro:differentiableI_vector)
next
  show "le.curve_eq differentiable at_right (Inf {0..1})" using le.curve_eq_has_vector_derivative by (auto intro:differentiableI_vector)
qed 

lemma "snd (hd points_ri) \<in> sr2.cr_tangent_line"
proof -
  have "\<exists>t>0. snd (hd points_ri) = ri.curve_eq 0 + t *\<^sub>R vector_derivative ri.curve_eq (at_right (Inf {0..1}))"
  proof (cases "tl points_ri = []")
    case True
    have "\<exists>t>0. snd (hd points_ri) = ri.curve_eq 0 + t *\<^sub>R ((snd (hd points_ri)) - (fst (hd points_ri)))"
    proof -
      have "ri.curve_eq 0 + 1 *\<^sub>R ((snd (hd points_ri)) - (fst (hd points_ri))) = snd (hd points_ri)" using ri.curve_eq0 by auto
      moreover have "0<(1::real)" by auto
      ultimately show ?thesis by fastforce
    qed
    moreover have "(SOME f'. (ri.curve_eq has_vector_derivative f') (at_right (Inf {0..1}))) = snd (hd points_ri) - fst (hd points_ri)"
    proof -
      have "(ri.curve_eq has_vector_derivative (snd (hd points_ri)) - (fst (hd points_ri))) (at_right (Inf {0..1}))"
        using True ri.curve_eq_has_vector_derivative by auto
      moreover then have "\<And>f'. (ri.curve_eq has_vector_derivative f') (at_right (Inf {0..1})) \<Longrightarrow> f' = snd (hd points_ri) - fst (hd points_ri)"
        using vector_derivative_unique_within[of "Inf {0..1}" "{Inf {0..1} <..}"] by auto
      ultimately show ?thesis using Hilbert_Choice.some_equality by blast
    qed
    ultimately show ?thesis unfolding vector_derivative_def by auto
  next
    case False
    have "\<exists>t>0. snd (hd points_ri) = ri.curve_eq 0 + t *\<^sub>R 2 *\<^sub>R ((snd (hd points_ri)) - (fst (hd points_ri)))"
    proof -
      have "ri.curve_eq 0 + 0.5 *\<^sub>R 2 *\<^sub>R ((snd (hd points_ri)) - (fst (hd points_ri))) = snd (hd points_ri)" using ri.curve_eq0 by auto
      moreover have "0<(0.5::real)" by auto
      ultimately show ?thesis by fastforce
    qed
    moreover have "(SOME f'. (ri.curve_eq has_vector_derivative f') (at_right (Inf {0..1}))) = 2 *\<^sub>R (snd (hd points_ri) - fst (hd points_ri))"
    proof -
      have "(ri.curve_eq has_vector_derivative 2 *\<^sub>R (snd (hd points_ri) - fst (hd points_ri))) (at_right (Inf {0..1}))"
        using False ri.curve_eq_has_vector_derivative by auto
      moreover then have "\<And>f'. (ri.curve_eq has_vector_derivative f') (at_right (Inf {0..1})) \<Longrightarrow> f' = 2 *\<^sub>R (snd (hd points_ri) - fst (hd points_ri))"
        using vector_derivative_unique_within[of "Inf {0..1}" "{Inf {0..1} <..}"] by auto
      ultimately show ?thesis using Hilbert_Choice.some_equality by blast
    qed
    ultimately show ?thesis unfolding vector_derivative_def by auto
  qed
  then show ?thesis unfolding sr2.cr_tangent_line_def sr2.ri_tangent_at_inf_def by auto
qed
  
subsubsection "Point in drivable area test"

definition direction_right :: "bool" where
  "direction_right \<equiv> snd ri.first_point < snd le.first_point"
  
abbreviation direction_left :: bool where
  "direction_left \<equiv> \<not> direction_right"

find_theorems "ri.first_point"  
  
theorem direction_left_alt_def:
  "direction_left \<Longrightarrow> snd ri.first_point > snd le.first_point"
  unfolding direction_right_def using non_intersecting ri.pathstart_first_point 
  le.pathstart_first_point same_init_x_alt_def unfolding pathstart_def
  by (smt cInf_atLeastAtMost prod_eqI sr2.inf_in_dom)
      
lemma sr_lb_x_eq:
  "sr.lb_x = fst le.first_point"  
  unfolding sr.lb_x_def sr.common_setX_def using equal_curve_setX le.curve_setX_interval    
    cInf_atLeastAtMost[OF order.strict_implies_order[OF le.first_lt_last_point]] by auto 

lemma sr_ub_x_eq:
  "sr.ub_x = fst le.last_point"
  unfolding sr.ub_x_def sr.common_setX_def using equal_curve_setX le.curve_setX_interval
    cSup_atLeastAtMost[OF order.strict_implies_order[OF le.first_lt_last_point]] by auto

lemma sr_lb_x_eq':
  "sr.lb_x = fst ri.first_point"
  using same_init_x_alt_def sr_lb_x_eq by auto
    
lemma sr_ub_x_eq':
  "sr.ub_x = fst ri.last_point"
  using same_final_x_alt_def sr_ub_x_eq by auto
        
lemma ri_first_point_curve_eq0:
  "ri.first_point = ri.curve_eq 0"
  unfolding points_path2_def using ri.nonempty_points pathstart_linepath unfolding pathstart_def
  by (smt pathstart_def points_path2_def ri.pathstart_first_point)

lemma le_first_point_curve_eq0:
  "le.first_point = le.curve_eq 0"
  unfolding points_path2_def using le.nonempty_points pathstart_linepath unfolding pathstart_def
  by (smt pathstart_def points_path2_def le.pathstart_first_point)
                    
thm "simple_boundary.f_of_x_def"  
term "simple_boundary.f_of_x ri.curve_eq {0..1} x"
term "simple_boundary.inv_curve_x ri.curve_eq {0..1}"
term "curve.curve_eq_x ri.curve_eq"
thm "curve.curve_eq_x_def"  
    
lemma ri_first_point_f_of_x:
  "snd ri.first_point = sr.ri.f_of_x sr.lb_x"
  unfolding sr_lb_x_eq' 
proof -
  have "ri.first_point = ri.curve_eq 0" using ri_first_point_curve_eq0 by auto
  have "fst (ri.curve_eq 0) = sr.ri.curve_eq_x 0"  
    unfolding curve.curve_eq_x_def[OF ri.curve_eq_is_curve] by auto
  with \<open>ri.first_point = ri.curve_eq 0\<close> 
    have 0: "sr.ri.f_of_x (fst ri.first_point) = sr.ri.f_of_x (sr.ri.curve_eq_x 0)" by auto    
  with simple_boundary.f_of_x_def[OF ri.simple_boundary_curve_eq_01]
    have "... = sr.ri.curve_eq_y 0" using sr.ri.inv_curve_x_def using sr.ri.param_y_via_f_of_x by auto
  also have "... = snd (ri.curve_eq 0)" unfolding sr.ri.curve_eq_y_def by auto
  finally have "sr.ri.f_of_x (fst ri.first_point) = snd (ri.curve_eq 0)" using 0 by auto        
  with ri_first_point_curve_eq0 show "snd ri.first_point = sr.ri.f_of_x (fst ri.first_point)"    
    by auto   
qed
  
lemma le_first_point_f_of_x:
  "snd le.first_point = sr.le.f_of_x sr.lb_x"
  unfolding sr_lb_x_eq
proof -
  have "le.first_point = le.curve_eq 0" using le_first_point_curve_eq0 by auto
  have "fst (le.curve_eq 0) = sr.le.curve_eq_x 0"  
    unfolding curve.curve_eq_x_def[OF le.curve_eq_is_curve] by auto
  with \<open>le.first_point = le.curve_eq 0\<close> 
    have 0: "sr.le.f_of_x (fst le.first_point) = sr.le.f_of_x (sr.le.curve_eq_x 0)" by auto    
  with simple_boundary.f_of_x_def[OF le.simple_boundary_curve_eq_01]
    have "... = sr.le.curve_eq_y 0" using sr.le.inv_curve_x_def using sr.le.param_y_via_f_of_x by auto
  also have "... = snd (le.curve_eq 0)" unfolding sr.le.curve_eq_y_def by auto
  finally have "sr.le.f_of_x (fst le.first_point) = snd (le.curve_eq 0)" using 0 by auto        
  with le_first_point_curve_eq0 show "snd le.first_point = sr.le.f_of_x (fst le.first_point)"    
    by auto   
qed    
      
theorem simplified_direction_right:
  "direction_right = sr.direction_right"
  unfolding direction_right_def sr.direction_right_def 
  using ri_first_point_f_of_x le_first_point_f_of_x by auto
    
theorem simplified_direction_left:
  "direction_left = sr.direction_left"
  using sr.direction_right_neq_left simplified_direction_right by blast    
         
definition point_in_drivable_area :: "real2 \<Rightarrow> bool" where
  "point_in_drivable_area p \<equiv>
    ( if direction_right then  
          above_and_inside_polychains points_ri p \<and> below_and_inside_polychains points_le p
      else 
        above_and_inside_polychains points_le p \<and> below_and_inside_polychains points_ri p
    )"
  
abbreviation outside where
  "outside p cs \<equiv> fst p \<le> fst (fst (hd cs)) \<or> fst p \<ge> fst (snd (last (cs))) "  
      
definition point_outside_drivable_area :: "real2 \<Rightarrow> bool" where
  "point_outside_drivable_area p \<equiv>
    ( if direction_right then  
        outside p points_le \<or>   (* points_le and points_ri have the same setX *) 
                   above_and_inside_polychains points_le p \<or> below_and_inside_polychains points_ri p
      else 
        outside p points_le \<or> 
                   above_and_inside_polychains points_ri p \<or> below_and_inside_polychains points_le p
    )"
    
theorem sr_between_setYI_right:
  assumes "direction_right"
  assumes "sr.ri.f_of_x x < y" and "y < sr.le.f_of_x x"    
  shows "y \<in> sr.between_setY x"  
  using assms unfolding sr.between_setY_def by auto

theorem sr_between_setYI_left:
  assumes "direction_left"
  assumes "sr.le.f_of_x x < y" and "y < sr.ri.f_of_x x"  
  shows "y \<in> sr.between_setY x"
  using assms unfolding sr.between_setY_def by auto    
      
theorem pida_correctness: 
  assumes "point_in_drivable_area (x,y)"
  shows "(x,y) \<in> sr.drivable_area"
proof (rule sr.drivable_areaI)
  consider "direction_right" | "direction_left" by auto
  thus "x \<in> sr.open_common_setX"
  proof (cases)
    case 1
    have "sr.common_setX = sr.ri.setX" using equal_curve_setX sr.common_setX_def by auto   
    have "fst ri.first_point < fst ri.last_point"
      by (metis hd_Cons_tl monotone_polychain_fst_last ri.monotone ri.nonempty_points 
        same_final_x_alt_def same_init_x_alt_def)             
    with \<open>sr.common_setX = sr.ri.setX\<close> have  sr_eq: "sr.open_common_setX = {fst ri.first_point <..< fst ri.last_point}"
      unfolding sr.lb_x_def sr.ub_x_def ri.curve_setX_interval 
      using Inf_atLeastAtMost Sup_atLeastAtMost atLeastAtMost_diff_ends by auto
    with above_inside_poly_correctness1 and assms have "x \<in> {fst ri.first_point <..< fst ri.last_point}"
      unfolding point_in_drivable_area_def using 1 by auto
    with sr_eq show "x \<in> sr.open_common_setX" by auto 
  next
    case 2      
    have "sr.common_setX = sr.le.setX" using equal_curve_setX sr.common_setX_def by auto   
    have "fst le.first_point < fst le.last_point"
      by (metis hd_Cons_tl monotone_polychain_fst_last ri.monotone ri.nonempty_points 
        same_final_x_alt_def same_init_x_alt_def)             
    with \<open>sr.common_setX = sr.le.setX\<close> have  sr_eq: "sr.open_common_setX = {fst le.first_point <..< fst le.last_point}"
      unfolding sr.lb_x_def sr.ub_x_def le.curve_setX_interval 
      using Inf_atLeastAtMost Sup_atLeastAtMost atLeastAtMost_diff_ends by auto
    with above_inside_poly_correctness1 and assms have "x \<in> {fst le.first_point <..< fst le.last_point}"
      unfolding point_in_drivable_area_def using 2 by auto
    with sr_eq show "x \<in> sr.open_common_setX" by auto
  qed       
next
  have "direction_right \<or> direction_left" by auto
  moreover
  { assume "direction_right"
    with assms have True: "above_and_inside_polychains points_ri (x,y)" and 
      False: "below_and_inside_polychains points_le (x,y)" unfolding point_in_drivable_area_def by auto      
    with above_inside_poly_correctness2[OF ri.monotone this(1)] obtain chain where 
      "chain \<in> set points_ri" and "fst (fst chain) \<le> x \<and> x \<le> fst (snd chain)" and 
      "line_equation (fst chain) (snd chain) x < y" using eq_snd_iff in_set_member by fastforce            
    with ri.test1[OF `chain \<in> set points_ri`]  have leo:"sr.ri.f_of_x x < y" by auto        
    from below_inside_poly_correctness2[OF le.monotone False] obtain chain2 where
      "chain2 \<in> set points_le" and "fst (fst chain2) \<le> x \<and> x \<le> fst (snd chain2)" and
      "line_equation (fst chain2) (snd chain2) x > y" using eq_snd_iff in_set_member by fastforce
    with le.test1[OF `chain2 \<in> set points_le`] have rio: "y < sr.le.f_of_x x" by auto        
    from leo rio \<open>direction_right\<close> have "y \<in> sr.between_setY x" using sr_between_setYI_right by auto }
  moreover
  { assume "direction_left"
    with assms have True: "above_and_inside_polychains points_le (x,y)" and 
      False: "below_and_inside_polychains points_ri (x,y)" unfolding point_in_drivable_area_def by auto      
    with above_inside_poly_correctness2[OF le.monotone this(1)] obtain chain where 
      "chain \<in> set points_le" and "fst (fst chain) \<le> x \<and> x \<le> fst (snd chain)" and 
      "line_equation (fst chain) (snd chain) x < y" using eq_snd_iff in_set_member by fastforce
    with le.test1[OF `chain \<in> set points_le`] have leo:"sr.le.f_of_x x < y" by auto        
    from below_inside_poly_correctness2[OF ri.monotone False] obtain chain2 where
      "chain2 \<in> set points_ri" and "fst (fst chain2) \<le> x \<and> x \<le> fst (snd chain2)" and
      "line_equation (fst chain2) (snd chain2) x > y" using eq_snd_iff in_set_member by fastforce
    with ri.test1[OF `chain2 \<in> set points_ri`] have rio: "y < sr.ri.f_of_x x" by auto        
    from leo rio \<open>direction_left\<close> have "y \<in> sr.between_setY x" using sr_between_setYI_left by auto }
  ultimately show "y \<in> sr.between_setY x" by auto       
qed  

subsubsection "Intersection of line segment with boundaries"
  
definition intersect_left_boundary where
  "intersect_left_boundary line \<equiv> segments_intersect_polychain line points_le"

definition intersect_right_boundary where
  "intersect_right_boundary line \<equiv> segments_intersect_polychain line points_ri"
    
definition intersect_boundaries where
  "intersect_boundaries line \<equiv> intersect_left_boundary line \<or> intersect_right_boundary line" 
  
subsubsection "Rectangle containment"
        
definition vertices_inside :: "rectangle \<Rightarrow> bool" where
  "vertices_inside rect \<equiv> (let vertices = get_vertices_rotated rect; 
                                insides = map point_in_drivable_area vertices in 
                                insides ! 0 \<and> insides ! 1 \<and> insides ! 2 \<and> insides ! 3)"
      
lemma vertices_inside_pida:
  assumes "vertices_inside rect" 
  assumes "0 \<le> i" and "i < 4"    
  shows "point_in_drivable_area (get_vertices_rotated rect ! i)"
proof -
  define vertices where "vertices \<equiv> get_vertices_rotated rect" 
  from nbr_of_vertex_rotated have l: "length (get_vertices_rotated rect) = 4" by auto
  from assms(1) have "map point_in_drivable_area (get_vertices_rotated rect) ! 0" and
                     "map point_in_drivable_area (get_vertices_rotated rect) ! 1" and
                     "map point_in_drivable_area (get_vertices_rotated rect) ! 2" and 
                     "map point_in_drivable_area (get_vertices_rotated rect) ! 3"
    unfolding vertices_inside_def Let_def by auto 
  with nth_map and l have c: "point_in_drivable_area (get_vertices_rotated rect ! 0)\<and>  
                           point_in_drivable_area (get_vertices_rotated rect ! 1)\<and>
                           point_in_drivable_area (get_vertices_rotated rect ! 2)\<and>
                           point_in_drivable_area (get_vertices_rotated rect ! 3)"
    by auto
  consider "i = 0" | "i = 1" | "i = 2" | "i = 3" using assms(2-3) by linarith    
  thus ?thesis using c
  by (cases) (auto)
qed
   
definition lines_inside :: "rectangle \<Rightarrow> bool" where
  "lines_inside rect \<equiv> (let lines = get_lines rect; 
                            intersect = map intersect_boundaries lines in
                            \<not> intersect ! 0 \<and> \<not> intersect ! 1 \<and> \<not> intersect ! 2 \<and> \<not> intersect ! 3)"  

definition rectangle_inside :: "rectangle \<Rightarrow> bool" where
  "rectangle_inside rect \<equiv> vertices_inside rect \<and> lines_inside rect"    
  
theorem vertices_inside_drivable_area:
  assumes "rectangle_inside rect"
  assumes "p \<in> set (get_vertices_rotated rect)"  
  shows "p \<in> sr.drivable_area"
proof -
  from assms(1) have "vertices_inside rect" unfolding rectangle_inside_def by auto  
  from assms(2) obtain i where "p = (get_vertices_rotated rect) ! i" and 
    "i < length (get_vertices_rotated rect)" and "0 \<le> i" unfolding in_set_conv_nth  by auto
  with `vertices_inside rect` have "point_in_drivable_area p" unfolding vertices_inside_def Let_def
    nbr_of_vertex_rotated using vertices_inside_pida[OF `vertices_inside rect` `0 \<le> i`] by auto
  with pida_correctness show ?thesis by (metis prod.collapse)  
qed

theorem points_in_rectangle_perimeter_drivable_area:
  assumes "rectangle_inside rect"
  assumes "line \<in> set (get_lines rect)"  
  assumes "p \<in> closed_segment (fst line) (snd line)"  
  shows "p \<in> sr.drivable_area"
  sorry  
  
theorem interior_points_in_rectangle_drivable_area:
  assumes "rectangle_inside rect"
  assumes "inside_rectangle p rect"
  shows "p \<in> sr.drivable_area"
  sorry
    
theorem points_in_rectangle_perimeter_drivable_area2:
  assumes "\<not> rectangle_inside rect"
  shows "\<exists>l p. l \<in> set (get_lines rect) \<and> p \<in> closed_segment (fst l) (snd l) \<and> p \<notin> sr.drivable_area"
  sorry    
end
      
definition (in lanelet_simple_boundary) rectangle_intersect :: "rectangle \<Rightarrow> bool" where
  "rectangle_intersect rect \<equiv> (let lines = get_lines rect in 
                               segments_intersect_polychain (lines ! 0) points \<or> 
                               segments_intersect_polychain (lines ! 1) points \<or> 
                               segments_intersect_polychain (lines ! 2) points \<or> 
                               segments_intersect_polychain (lines ! 3) points)" 
  
theorem (in lanelet_simple_boundary) rectangle_intersect_correctness:
  assumes "rectangle_intersect rect"
  shows "\<exists>c \<in> set points. \<exists>l \<in> set (get_lines rect). 
                       \<exists>p. p \<in> closed_segment (fst c) (snd c) \<and> p \<in> closed_segment (fst l) (snd l)"    
proof -
  define lines where "lines = get_lines rect" 
  from assms consider "segments_intersect_polychain (lines ! 0) points" |
                               "segments_intersect_polychain (lines ! 1) points" |
                               "segments_intersect_polychain (lines ! 2) points" |
                               "segments_intersect_polychain (lines ! 3) points"  
    unfolding rectangle_intersect_def Let_def lines_def by auto
  thus ?thesis
  proof (cases)
    case 1
    have "lines ! 0 \<in> set (get_lines rect)" using nth_mem nbr_of_lines unfolding lines_def
        by auto      
    with segment_intersect_poly_correct[OF 1]            
    show ?thesis by blast
  next
    case 2
    have "lines ! 1 \<in> set (get_lines rect)" using nth_mem nbr_of_lines unfolding lines_def
        by auto      
    with segment_intersect_poly_correct[OF 2]            
    show ?thesis by blast
  next
    case 3
    have "lines ! 2 \<in> set (get_lines rect)" using nth_mem nbr_of_lines unfolding lines_def
        by auto      
    with segment_intersect_poly_correct[OF 3]            
    show ?thesis by blast
  next
    case 4
    have "lines ! 3 \<in> set (get_lines rect)" using nth_mem nbr_of_lines unfolding lines_def
        by auto      
    with segment_intersect_poly_correct[OF 4]            
    show ?thesis by blast
  qed  
qed
  
subsection "Lane : composition of lanelets"

term "lanelet.rectangle_inside"  
  
fun it_in_lane :: "(real2 \<times> real2) list list \<Rightarrow> rectangle \<Rightarrow> nat \<Rightarrow> nat option" where
  "it_in_lane [] _ _ = None" | 
  "it_in_lane [_] _ _ = None" |   
  "it_in_lane (bound # bounds) rect num = 
          (if lanelet.rectangle_inside bound (hd bounds) rect then Some num else it_in_lane bounds rect (num + 1))"
  
lemma start_leq_num:
  assumes "it_in_lane boundaries rect start = Some num"
  shows "start \<le> num"
  using assms
proof (induction boundaries arbitrary:start num)
  case Nil
  then show ?case by auto
next
  case (Cons a boundaries)
  note case_cons = this  
  obtain a' bound' where "boundaries = [] \<or> boundaries = a' # bound'"  by (meson list.exhaust)
  moreover
  { assume "boundaries = []"
    with case_cons have ?case by auto }
  moreover
  { assume "boundaries = a' # bound'"
    with case_cons  
    consider "lanelet.rectangle_inside a a' rect" | "\<not> lanelet.rectangle_inside a a' rect" by auto
    hence ?case
    proof (cases)
      case 1
      with case_cons(2) have "start = num" unfolding `boundaries = a' # bound'` 
        by auto                
      then show ?thesis by auto
    next
      case 2
      with case_cons(2) have "it_in_lane (a' # bound') rect (start + 1) = Some num" 
        unfolding `boundaries = a' # bound'` it_in_lane.simps by auto
      with case_cons(1) have "start + 1 \<le> num" unfolding `boundaries = a' # bound'` by auto       
      then show ?thesis by auto
    qed
  }    
  ultimately show ?case by auto 
qed    
  
lemma it_in_lane_at_most_length:
  assumes "it_in_lane boundaries rect start = Some num"
  shows "num < start + length boundaries"
  using assms
proof (induction boundaries arbitrary:start num)
  case Nil
  then show ?case by auto
next
  case (Cons a boundaries)
  note case_cons = this  
  obtain a' bound' where "boundaries = [] \<or> boundaries = a' # bound'"  by (meson list.exhaust)
  moreover
  { assume "boundaries = []"
    with case_cons have ?case by auto }    
  moreover
  { assume "boundaries = a' # bound'"
    consider "lanelet.rectangle_inside a a' rect" | "\<not> lanelet.rectangle_inside a a' rect" by auto
    hence ?case
    proof (cases)
      case 1
      with case_cons have "start = num" unfolding `boundaries = a' # bound'` by auto                
      then show ?thesis by auto
    next
      case 2
      with case_cons have "it_in_lane (a' # bound') rect (start + 1) = Some num"
        unfolding `boundaries = a' # bound'` it_in_lane.simps by auto
      with case_cons(1) have "num < start + 1 + length boundaries" unfolding `boundaries = a' # bound'`
        by metis          
      then show ?thesis by auto
    qed  
  }    
  ultimately show ?case by auto
qed    
  
lemma it_in_lane_at_most_length0:
  assumes "it_in_lane boundaries rect 0 = Some num"
  shows "num < length boundaries"
  using it_in_lane_at_most_length[OF assms] by auto
    
theorem it_in_lane_correctness_general:
  assumes "it_in_lane boundaries rect start = Some num"
  shows "lanelet.rectangle_inside (boundaries ! (num - start)) (boundaries ! ((num - start) + 1)) rect"  
  using assms
proof (induction boundaries arbitrary:start num)
  case Nil
  then show ?case by auto
next
  case (Cons a boundaries)
  note case_cons = this
  obtain a' bound' where "boundaries = [] \<or> boundaries = a' # bound'"  by (meson list.exhaust)
  moreover
  { assume "boundaries = []"
    with case_cons(2) have ?case by auto }  
  moreover
  { assume "boundaries = a' # bound'"
    with case_cons(2) 
    consider "lanelet.rectangle_inside a a' rect" | "\<not> lanelet.rectangle_inside a a' rect" by auto
    hence ?case    
    proof (cases)
      case 1
      with case_cons(2) have "num = start" unfolding `boundaries = a' # bound'`  it_in_lane.simps(3)
        by auto
      moreover    
      have "(a # boundaries) ! 0 = a" by auto
      moreover     
      have "(a # boundaries) ! 1 = a'" using `boundaries = a' # bound'` by auto
      ultimately show ?thesis using 1 by auto
    next
      case 2
      from 2 and case_cons(2) have base: "it_in_lane boundaries rect (start + 1) = Some num" 
        unfolding `boundaries = a' # bound'` it_in_lane.simps by auto
      hence "num \<ge> start + 1" using start_leq_num by auto        
      from base and case_cons(1) have 
        0: "lanelet.rectangle_inside (boundaries ! (num - (start + 1))) (boundaries ! (num - (start + 1) + 1)) rect"
        using case_cons(2) by auto
      have 1: "lanelet.rectangle_inside (boundaries ! (num - start - 1)) (boundaries ! (num - start)) rect"
        using `num \<ge> start + 1`
      proof -
        have *:"num - (start + 1) = num - start - 1" by auto
        have "num - (start + 1) + 1 = num - start" using `num \<ge> start + 1` by auto
        with * and 0 show ?thesis by auto    
      qed      
      then show ?thesis
      proof -
        have "0 < num - start" using `num \<ge> start + 1` by auto
        have *: "(a # boundaries) ! (num - start) = boundaries ! (num - start - 1)"
          using nth_Cons_pos [OF `0 < num - start`] by auto
        have "(a # boundaries) ! (num - start + 1) = boundaries ! (num - start)"
          using nth_Cons_pos by auto
        with * show ?thesis using 1 by auto            
      qed        
    qed    
  }          
  ultimately show ?case by auto
qed
  
theorem it_in_lane_correctness0:
  assumes "it_in_lane boundaries rect 0 = Some num"
  shows "lanelet.rectangle_inside (boundaries ! num) (boundaries ! (num + 1)) rect"  
  using it_in_lane_correctness_general[OF assms] by auto   
  
fun boundaries_touched :: "(real2 \<times> real2) list list \<Rightarrow> rectangle \<Rightarrow> nat \<Rightarrow> nat list" where
  "boundaries_touched [] rect _ = []" | 
  "boundaries_touched (bound # bounds) rect num = 
    (if lanelet_simple_boundary.rectangle_intersect bound rect then num # boundaries_touched bounds rect (num + 1) 
     else boundaries_touched bounds rect (num + 1))"
  
lemma boundaries_touched_leq:
  assumes "boundaries_touched bounds rect start = ns"
  assumes "n \<in> set ns"    
  shows "start \<le> n"
  using assms
proof (induction bounds arbitrary: start n ns)
  case Nil
  then show ?case by auto
next
  case (Cons a bounds)
  note case_cons = this    
  have "lanelet_simple_boundary.rectangle_intersect a rect \<or> \<not> lanelet_simple_boundary.rectangle_intersect a rect"
    (is "?true \<or> ?false")
    by auto
  moreover
  { assume "?true"
    with case_cons(2) have "ns = start # boundaries_touched bounds rect (start + 1)" 
      unfolding boundaries_touched.simps by auto
    with case_cons(3) consider "n = start" | "n \<in> set (boundaries_touched bounds rect (start + 1))"
      by auto
    hence ?case        
    proof (cases)
      case 1
      then show ?thesis by auto
    next
      case 2
      from case_cons(1)[OF _ 2] have "start + 1 \<le> n" by auto 
      then show ?thesis by auto
    qed }
  moreover
  { assume "?false"
    with case_cons(2) have "ns = boundaries_touched bounds rect (start + 1)" by auto  
    from case_cons(1)[OF sym[OF this] `n \<in> set ns`] have ?case by auto    
  }
  ultimately show ?case by auto
qed 
  
lemma boundaries_touched_leq0:
  assumes "boundaries_touched bounds rect 0 = ns"
  assumes "n \<in> set ns"    
  shows "0 \<le> n"
  using boundaries_touched_leq[OF assms] by auto  
  
lemma boundaries_touched_at_most:
  assumes "boundaries_touched bounds rect start = ns"
  assumes "n \<in> set ns"    
  shows "n < start + length bounds"
  using assms
proof (induction bounds arbitrary: start n ns)
  case Nil
  then show ?case by auto
next
  case (Cons a bounds)
  note case_cons = this    
  have "lanelet_simple_boundary.rectangle_intersect a rect \<or> \<not> lanelet_simple_boundary.rectangle_intersect a rect"
    (is "?true \<or> ?false")
    by auto
  moreover    
  { assume "?true"
    with case_cons(2) have "ns = start # boundaries_touched bounds rect (start + 1)" 
      unfolding boundaries_touched.simps by auto
    with case_cons(3) consider "n = start" | "n \<in> set (boundaries_touched bounds rect (start + 1))"
      by auto 
    hence ?case        
    proof (cases)
      case 1
      then show ?thesis by auto
    next
      case 2
      with case_cons(1)[OF _ 2] have "n < start + 1 + length bounds" by metis          
      then show ?thesis by auto
    qed }
  moreover
  { assume "?false"
    with case_cons(2) have "ns = boundaries_touched bounds rect (start + 1)" by auto  
    with case_cons(1)[OF sym[OF this] case_cons(3)] have ?case by auto }
  ultimately show ?case by auto
qed
  
lemma boundaries_touched_at_most0:
  assumes "boundaries_touched bounds rect 0 = ns"
  assumes "n \<in> set ns"    
  shows "n < length bounds"
  using boundaries_touched_at_most[OF assms] by auto    

theorem boundaries_touched:
  assumes "boundaries_touched bounds rect start = ns"  
  assumes "n \<in> set ns"    
  shows "lanelet_simple_boundary.rectangle_intersect (bounds ! (n - start)) rect"
  using assms
proof (induction bounds arbitrary: start ns)
  case Nil
  then show ?case by auto
next
  case (Cons a bounds)
  note case_cons = this    
  consider "lanelet_simple_boundary.rectangle_intersect a rect" | 
           "\<not> lanelet_simple_boundary.rectangle_intersect a rect"
    by auto      
  thus ?case
  proof (cases)
    case 1
    with case_cons(2) have "ns = start # boundaries_touched bounds rect (start + 1)"
      unfolding boundaries_touched.simps by auto
    with case_cons(3) have "n = start \<or> n \<in> set (boundaries_touched bounds rect (start + 1))" 
      by auto
    moreover
    { assume "n = start "
      have "a = (a # bounds) ! 0" by auto  
      hence ?thesis using 1 and `n = start` by auto }
    moreover
    { assume as: "n \<in> set (boundaries_touched bounds rect (start + 1))"
      from boundaries_touched_leq[OF _ this] have "start + 1 \<le> n" by auto
      hence "0 < n - start" by auto   
      from case_cons(1)[OF _ as] 
        have *: "lanelet_simple_boundary.rectangle_intersect (bounds ! (n - (start + 1))) rect" 
        by auto
      have "lanelet_simple_boundary.rectangle_intersect ((a # bounds) ! (n - start)) rect"
      proof -
        have eq: "(a # bounds) ! (n - start) = bounds ! (n - (start + 1))" 
          using nth_Cons_pos[OF `0 < n - start`] by auto
        show ?thesis using * unfolding eq by auto                    
      qed }      
    ultimately show ?thesis by auto
  next
    case 2  
    from 2 case_cons(2) have eq: "ns = boundaries_touched bounds rect (start + 1)" by auto
    with boundaries_touched_leq[OF _ `n \<in> set ns`] have "start + 1 \<le> n" by auto    
    hence "start < n" by auto        
    from eq case_cons have "lanelet_simple_boundary.rectangle_intersect (bounds ! (n - (start + 1))) rect"
      by auto
    then show ?thesis using nth_Cons_pos `start < n` by auto
  qed
qed    
  
theorem boundaries_touched0:
  assumes "boundaries_touched bounds rect 0 = ns"  
  assumes "n \<in> set ns"    
  shows "lanelet_simple_boundary.rectangle_intersect (bounds ! n) rect"  
  using boundaries_touched[OF assms] by auto
    
(* return type of lane detection *)  
datatype detection_opt = Outside | Lane (glane: nat) | Boundaries "nat list"  

theorem drop_cons: 
  "0 < n \<Longrightarrow> drop n (x # xs) = drop (n - 1) xs"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case unfolding drop_Suc_Cons by auto
qed  
  
locale lane =
  fixes boundaries :: "(real2 \<times> real2) list list"
  fixes border :: nat  
  assumes "2 \<le> length boundaries"
  assumes "0 \<le> border" and "border < length boundaries "    
  assumes "\<forall>i. Suc i \<le> length boundaries \<longrightarrow> lanelet (boundaries ! Suc i) (boundaries ! i)"
  assumes "\<forall>i j. i + 1 \<le> border \<and> j + 1 \<le> border \<and> i < j \<longrightarrow> 
                  lanelet.direction_right (boundaries ! (i+1)) (boundaries ! i) = 
                  lanelet.direction_right (boundaries ! (j+1)) (boundaries ! j)"
  assumes "\<forall>i j. border \<le> i  \<and>  i + 1 < length boundaries \<and> border \<le> j  \<and> j + 1 < length boundaries \<and> i < j \<longrightarrow> 
                  lanelet.direction_right (boundaries ! (i+1)) (boundaries ! i) = 
                  lanelet.direction_right (boundaries ! (j+1)) (boundaries ! j)"
  assumes "\<forall>i j. i + 1 \<le> border \<and> border \<le> j \<and> j + 1 < length boundaries \<longrightarrow> 
                  lanelet.direction_right (boundaries ! (i+1)) (boundaries ! i) \<noteq>
                  lanelet.direction_right (boundaries ! (j+1)) (boundaries ! j)"    
  assumes "\<forall>i j t1 t2. lanelet_curve.curve_eq (boundaries ! i) t1 \<noteq> lanelet_curve.curve_eq (boundaries ! j) t2"
begin

fun in_lane :: "rectangle \<Rightarrow> nat option" where
  "in_lane rect = it_in_lane boundaries rect 0"
  
theorem in_lane_correctness_abstract:
  assumes "in_lane rect = Some num"
  shows "lanelet.rectangle_inside (boundaries ! num) (boundaries ! (num + 1)) rect"    
  using it_in_lane_correctness0 assms by auto
    
theorem 
  assumes "in_lane rect = Some num"
  shows "num < length boundaries"
  using it_in_lane_at_most_length0 assms by auto
    
fun lane_boundaries_touched :: "rectangle \<Rightarrow> nat list" where
  "lane_boundaries_touched rect = boundaries_touched boundaries rect 0"  

theorem lane_boundaries_touched_correctness_abstract:
  assumes "lane_boundaries_touched rect = ns"
  assumes "n \<in> set ns"
  shows "lanelet_simple_boundary.rectangle_intersect (boundaries ! n) rect"    
  using boundaries_touched0 assms by auto    

theorem 
  assumes "lane_boundaries_touched rect = ns"
  assumes "n \<in> set ns"
  shows "n < length boundaries"
  using boundaries_touched_at_most0 assms by auto    
    
fun lane_detection :: "rectangle \<Rightarrow> detection_opt" where
  "lane_detection rect = (case in_lane rect of Some x \<Rightarrow> Lane x 
                                             | None \<Rightarrow> (case lane_boundaries_touched rect of 
                                                          [] \<Rightarrow> Outside
                                                        | ns \<Rightarrow> Boundaries ns))"  
  
theorem boundaries_not_empty: 
  assumes "lane_detection rect = Boundaries ns" 
  shows "ns \<noteq> []"
  using assms  
proof -
  consider x where "in_lane rect = Some x" | "in_lane rect = None" by auto
  thus ?thesis
  proof (cases)
    case 1  
    then show ?thesis using assms by auto
  next
    case 2
    obtain a as where "lane_boundaries_touched rect = [] \<or> lane_boundaries_touched rect = a # as"
      by (meson list_encode.elims)    
    moreover
    { assume "lane_boundaries_touched rect = []"
      with assms have ?thesis using 2 by auto }
    moreover
    { assume "lane_boundaries_touched rect = a # as"
      with assms have ?thesis using 2 by auto }    
    ultimately show ?thesis by auto
  qed    
qed

text "Finding initial position of the trace --- where trace is regarded as a series of 
   rectangles. A rectangle signify the occupancy of a vehicle."
  
definition initial_lane :: "rectangle list \<Rightarrow> detection_opt" where
  "initial_lane rects = lane_detection (hd rects)"  
  
fun start_inc_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "start_inc_lane [] ori_lane _ = None" | 
  "start_inc_lane (rect # rects) ori_lane num = (case lane_detection rect of
                                                      Outside \<Rightarrow> None 
                                                    (* If it suddenly jumps to the next lane without touching boundaries, it is not considered as part of overtaking *)
                                                    | Lane n  \<Rightarrow> (if n = ori_lane then start_inc_lane rects n (num + 1) else None) 
                                                    (* If the it touches more than one boundaries or not the specified boundary, it will not be considered as initial part of overtaking *)
                                                    | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (num, rects) else None))"

theorem start_inc_lane_not_nil:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "rects \<noteq> []"
  using assms by auto

theorem start_inc_lane_cons:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  obtains a rects' where "rects = a # rects'" using start_inc_lane_not_nil[OF assms]
  by (meson list.exhaust_sel)

theorem start_inc_lane_cases_neq:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  shows "ld_res \<noteq> Outside"    
proof -
  from start_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto
  from assms(1) show ?thesis unfolding rects start_inc_lane.simps ld_res_def by auto      
qed
    
theorem start_inc_lane_cases:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  shows "\<exists>n ns. ld_res = Lane n \<or> ld_res = Boundaries ns"
proof -
  from start_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto
  from start_inc_lane_cases_neq[OF assms(1)] have "ld_res \<noteq> Outside" unfolding ld_res_def by auto   
  thus ?thesis by (induction ld_res) (auto)
qed
  
theorem start_inc_lane_cases_obtain:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  obtains n ns where "ld_res = Lane n \<or> ld_res = Boundaries ns"
  using start_inc_lane_cases[OF assms(1)] unfolding ld_res_def by auto
    
theorem start_inc_lane_cases_bound:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Boundaries ids"
  shows "ids = [ori_lane + 1]"
proof -
  from start_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto
  hence "ld_res = lane_detection a" unfolding ld_res_def rects by auto
  with assms(3) have "lane_detection a = Boundaries ids" by auto    
  from assms(1) have "tl ids = [] \<and> hd ids = ori_lane + 1" 
    unfolding rects start_inc_lane.simps `lane_detection a = Boundaries ids`    
  proof -
    assume "(case Boundaries ids of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects' n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects') else None) = Some (time, rest)"
    then have "(if tl ids = [] \<and> hd ids = ori_lane + 1 then Some (start_time, rects') else None) \<noteq> None"
      by simp
    then show ?thesis
      by meson
  qed
  hence "ids = [ori_lane + 1]" 
    using \<open>lane_detection a = Boundaries ids\<close> boundaries_not_empty hd_Cons_tl by force
  thus ?thesis using assms(2) by auto 
qed
  
theorem start_inc_lane_cases_bound_tail:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Boundaries ids"
  shows "rest = tl rects"  
proof -
  from start_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto
  hence "ld_res = lane_detection a" unfolding ld_res_def rects by auto
  with assms(3) have "lane_detection a = Boundaries ids" by auto    
  with start_inc_lane_cases_bound[OF assms(1)] have "ids = [ori_lane + 1]" unfolding rects     
    by auto
  with `lane_detection a = Boundaries ids` have "lane_detection a = Boundaries [ori_lane + 1]" by auto
  from assms(1) show ?thesis unfolding rects start_inc_lane.simps `lane_detection a = Boundaries [ori_lane + 1]`      
    by auto      
qed
  
theorem start_inc_lane_cases_lane:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Lane n"
  shows "n = ori_lane"  
proof -
  from start_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto
  hence "ld_res = lane_detection a" unfolding ld_res_def rects by auto
  with assms(3) have "lane_detection a = Lane n" unfolding rects ld_res_def by auto    
  from assms(1)   have "(if n = ori_lane then start_inc_lane rects' n (start_time + 1) else None) = Some (time, rest)"
    unfolding rects start_inc_lane.simps `lane_detection a = Lane n` by auto
  also have "... \<noteq> None" by auto
  finally have "(if n = ori_lane then start_inc_lane rects' n (start_time + 1) else None) \<noteq> None"
    by auto  
  thus "n = ori_lane" unfolding split_ifs by auto  
qed
  
theorem start_inc_lane_cases2:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"      
  shows "ld_res = Lane ori_lane \<or> ld_res = Boundaries [ori_lane + 1]"
proof -
  from start_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto  
  from start_inc_lane_cases_obtain[OF assms(1)] obtain n ns 
    where "lane_detection a = Lane n \<or> lane_detection a = Boundaries ns" unfolding rects by auto
  moreover
  { assume *: "lane_detection a = Lane n"
    with start_inc_lane_cases_lane[OF assms(1)] have "n = ori_lane" unfolding rects by auto
    hence ?thesis unfolding ld_res_def rects using * by auto }
  moreover
  { assume **: "lane_detection a = Boundaries ns"
    with start_inc_lane_cases_bound[OF assms(1)] have "ns = [ori_lane + 1]" unfolding rects
      by auto
    hence ?thesis unfolding ld_res_def rects using ** by auto }
  ultimately show ?thesis by auto
qed      
    
theorem start_inc_lane_decrease_length:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "length rest < length rects"
  using assms  
proof (induction rects arbitrary:start_time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this    
  from start_inc_lane_cases2[OF case_cons(2)] have "lane_detection a = Lane ori_lane \<or>
                                                    lane_detection a = Boundaries [ori_lane + 1]"
    by auto
  moreover
  { assume "lane_detection a = Lane ori_lane"
    from case_cons(2) have "start_inc_lane rects ori_lane (start_time + 1) = Some (time, rest)" 
      unfolding start_inc_lane.simps `lane_detection a = Lane ori_lane` by auto
    with case_cons(1)[OF this] have "length rest < length rects" by auto
    hence "length rest < length (a # rects)" by auto }
    
  moreover
  { assume "lane_detection a = Boundaries [ori_lane + 1]"
    from case_cons(2) have "rest = rects" unfolding start_inc_lane.simps 
        `lane_detection a = Boundaries [ori_lane + 1]`  by auto
    hence "length rest < length (a # rects)" by auto } 
  ultimately show ?case by auto
qed          
           
theorem start_inc_lane_at_least: 
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "start_time \<le> time"  
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?thesis by auto  
  next
    case (Lane x)
    note case_lane = this      
    have "x = ori_lane \<or> x \<noteq> ori_lane" by auto
    moreover        
    { assume "x = ori_lane"
      with case_lane case_cons(2) have "start_inc_lane rects x (start_time + 1) = Some (time, rest)"
        unfolding start_inc_lane.simps
      proof -
        assume a1: "(case lane_detection a of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None) = Some (time, rest)"
        have "start_inc_lane rects x (start_time + 1) = (case Lane ori_lane of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None)"
          by (simp add: \<open>x = ori_lane\<close>)
        then show ?thesis
          using a1 \<open>Lane x = lane_detection a\<close> \<open>x = ori_lane\<close> by force
      qed
      with case_cons(1) have "start_time + 1 \<le> time" unfolding `x = ori_lane`
        by auto
      hence ?case by auto          
    }  
    moreover
    { assume "x \<noteq> ori_lane"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }    
    ultimately show ?case by auto
  next
    case (Boundaries x)    
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto          
    have "tl x = [] \<and> hd x = ori_lane + 1 \<or> \<not> (tl x = [] \<and> hd x = ori_lane + 1)" by auto  
    moreover
    { assume "tl x = [] \<and> hd x = ori_lane + 1"
      with sym[OF case_bound] case_cons(2) have "start_time = time" by auto  
      hence ?case by auto }
    moreover
    { assume "\<not> (tl x = [] \<and> hd x = ori_lane + 1)"
      with sym[OF case_bound] case_cons(2) have ?case by auto }      
    ultimately show ?case by auto
  qed
qed    
  
theorem start_inc_lane_atmost:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "time \<le> start_time + length rects"
  using assms
proof (induction rects arbitrary:start_time time rest)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?thesis by auto  
  next
    case (Lane x)
    note case_lane = this      
    have "x = ori_lane \<or> x \<noteq> ori_lane" by auto
    moreover
    { assume "x = ori_lane"
      with case_lane case_cons(2) have "start_inc_lane rects x (start_time + 1) = Some (time, rest)"
        unfolding start_inc_lane.simps
      proof -
        assume a1: "(case lane_detection a of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None) = Some (time, rest)"
        have "start_inc_lane rects x (start_time + 1) = (case Lane ori_lane of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None)"
          by (simp add: \<open>x = ori_lane\<close>)
        then show ?thesis
          using a1 \<open>Lane x = lane_detection a\<close> \<open>x = ori_lane\<close> by force
      qed
      with case_cons(1) have "time \<le> start_time + 1 + length rects" unfolding `x = ori_lane`
        by metis          
      hence ?case by auto }
    moreover
    { assume "x \<noteq> ori_lane"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }    
    ultimately show ?case by auto
  next
    case (Boundaries x)
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto          
    have "tl x = [] \<and> hd x = ori_lane + 1 \<or> \<not> (tl x = [] \<and> hd x = ori_lane + 1)" by auto  
    moreover
    { assume "tl x = [] \<and> hd x = ori_lane + 1"
      with sym[OF case_bound] case_cons(2) have "start_time = time" by auto  
      hence ?case by auto }
    moreover
    { assume "\<not> (tl x = [] \<and> hd x = ori_lane + 1)"
      with sym[OF case_bound] case_cons(2) have ?case by auto }      
    ultimately show ?case by auto
  qed      
qed    
  
theorem start_inc_lane_boundaries:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "lane_detection (rects ! (time - start_time)) = Boundaries [ori_lane + 1]"
  using assms
proof (induction rects arbitrary:start_time time rest)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?thesis by auto  
  next
    case (Lane x)
    note case_lane = this      
    have "x = ori_lane \<or> x \<noteq> ori_lane" by auto
    moreover
    { assume "x = ori_lane"
       with case_lane case_cons(2) have base: "start_inc_lane rects x (start_time + 1) = Some (time, rest)"
        unfolding start_inc_lane.simps
      proof -
        assume a1: "(case lane_detection a of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None) = Some (time, rest)"
        have "start_inc_lane rects x (start_time + 1) = (case Lane ori_lane of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None)"
          by (simp add: \<open>x = ori_lane\<close>)
        then show ?thesis
          using a1 \<open>Lane x = lane_detection a\<close> \<open>x = ori_lane\<close> by force
      qed
      hence "start_time + 1 \<le> time" using start_inc_lane_at_least by auto
      hence "0 < time - start_time" by auto    
      from base and case_cons(1) have "lane_detection (rects ! (time - start_time - 1)) = Boundaries [ori_lane + 1]"
        unfolding `x = ori_lane` by auto
      hence ?thesis using nth_Cons_pos[OF `0 < time - start_time`] by metis }  
    moreover
    { assume "x \<noteq> ori_lane"
          with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }    
    ultimately show ?case by auto
  next
    case (Boundaries x)
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto
    have "tl x = [] \<and> hd x = ori_lane + 1 \<or> \<not> (tl x = [] \<and> hd x = ori_lane + 1)" by auto  
    moreover
    { assume "tl x = [] \<and> hd x = ori_lane + 1"         
      with sym[OF case_bound] case_cons(2) have "start_time = time" by auto
      hence "lane_detection ((a # rects) ! (time - start_time)) = lane_detection a" by auto
      also have "... = Boundaries x" using case_bound by auto
      also have "... = Boundaries [ori_lane + 1]" using `tl x = [] \<and> hd x = ori_lane + 1`
      proof -
        assume "tl x = [] \<and> hd x = ori_lane + 1"        
        with hd_Cons_tl[OF `x \<noteq> []`] have "x = [ori_lane + 1]" by auto
        thus ?thesis by auto            
      qed        
      hence ?case using sym[OF case_bound] `tl x = [] \<and> hd x = ori_lane + 1` `start_time = time`
        by auto }
    moreover
    { assume "\<not> (tl x = [] \<and> hd x = ori_lane + 1)"
          with sym[OF case_bound] case_cons(2) have ?case by auto }            
    ultimately show ?case by auto
  qed    
qed  
  
theorem start_inc_lane_ori_lane:
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "\<forall>t. 0 \<le> t - start_time \<and> t - start_time < time - start_time  \<longrightarrow> lane_detection (rects ! (t - start_time)) = Lane ori_lane"
  using assms
proof (induction rects arbitrary:start_time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?thesis by auto  
  next
    case (Lane x)
    note case_lane = this      
    have "x = ori_lane \<or> x \<noteq> ori_lane" by auto
    moreover
    { assume "x = ori_lane"
      with case_lane case_cons(2) have base: "start_inc_lane rects x (start_time + 1) = Some (time, rest)"
        unfolding start_inc_lane.simps
      proof -
        assume a1: "(case lane_detection a of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None) = Some (time, rest)"
        have "start_inc_lane rects x (start_time + 1) = (case Lane ori_lane of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (start_time + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (start_time, rects) else None)"
          by (simp add: \<open>x = ori_lane\<close>)
        then show ?thesis
          using a1 \<open>Lane x = lane_detection a\<close> \<open>x = ori_lane\<close> by force
      qed
      with case_cons have rec: "\<forall>t. 0 \<le> t - (start_time + 1) \<and> t - (start_time + 1) < time - (start_time + 1) \<longrightarrow> lane_detection (rects ! (t - (start_time + 1))) = Lane ori_lane" unfolding `x = ori_lane` 
        by auto
      have ?thesis
      proof (rule allI, rule impI)
        fix t
        assume "0 \<le> t - start_time \<and> t - start_time < time - start_time"  
        have "t = start_time \<or> t > start_time \<or> t < start_time" by auto
        moreover
        { assume "t = start_time"
          hence "lane_detection ((a # rects) ! (t - start_time)) = lane_detection a" by auto  
          also have "... = Lane x" using `Lane x = lane_detection a` by auto
          also have "... = Lane ori_lane" using `x = ori_lane` by auto
          finally have "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by auto }
        moreover
        { assume "start_time < t" 
          hence "lane_detection ((a # rects) ! (t - start_time)) = lane_detection (rects ! (t - start_time - 1))"
            using nth_Cons_pos by auto
          also have "... = Lane ori_lane" using `start_time < t` `0 \<le> t - start_time \<and> t - start_time < time - start_time` rec by auto
          finally have "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by auto }
        moreover
        { assume "t < start_time"
          hence "lane_detection ((a # rects) ! (t - start_time)) = lane_detection a" by auto  
          also have "... = Lane x" using `Lane x = lane_detection a` by auto
          also have "... = Lane ori_lane" using `x = ori_lane` by auto
          finally have "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by auto }
        ultimately show "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by blast
      qed }    
    moreover
    { assume "x \<noteq> ori_lane"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }  
    ultimately show ?case by auto      
  next
    case (Boundaries x)
    note case_bound = this 
    with boundaries_not_empty have "x \<noteq> []" by auto
    have "tl x = [] \<and> hd x = ori_lane + 1 \<or> \<not> (tl x = [] \<and> hd x = ori_lane + 1)" by auto  
    moreover
    { assume "tl x = [] \<and> hd x = ori_lane + 1"         
      with sym[OF case_bound] case_cons(2) have "start_time = time" by auto       
      have ?thesis
      proof (rule allI, rule impI)
        fix t        
        assume asm: "0 \<le> t- start_time \<and> t - start_time < time - start_time"  
        with `start_time = time` have "t - start_time < 0" by auto          
        have "t \<le> start_time \<or> t > start_time"  by auto 
        moreover
        { assume "t \<le> start_time"
          with `t - start_time < 0` have "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by auto }
        moreover
        { assume "t > start_time"
          with `t - start_time < 0` have "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by auto}
        ultimately show "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane" by blast
      qed }
    moreover
    { assume "\<not> (tl x = [] \<and> hd x = ori_lane + 1)"
          with sym[OF case_bound] case_cons(2) have ?case by auto }            
    ultimately show ?case by auto
  qed
qed
      
theorem start_inc_lane_general_correctness: 
  assumes "start_inc_lane rects ori_lane start_time = Some (time, rest)"
  shows "(LEAST n. start_time \<le> n \<and> n \<le> start_time + length rects \<and> 
                    lane_detection (rects ! (n - start_time)) = Boundaries [ori_lane + 1] \<and> 
                    (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < n - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)) = time"    
proof (rule Least_equality)
  have "start_time \<le> time" using start_inc_lane_at_least[OF assms] by auto
  moreover      
  have "time \<le> start_time + length rects" using start_inc_lane_atmost[OF assms] by auto     
  moreover
  have " lane_detection (rects ! (time - start_time)) = Boundaries [ori_lane + 1]"  
    using start_inc_lane_boundaries[OF assms] by auto
  moreover
  have " (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)" 
    using start_inc_lane_ori_lane[OF assms] by auto
  ultimately show "start_time \<le> time \<and>
    time \<le> start_time + length rects \<and>
    lane_detection (rects ! (time - start_time)) = Boundaries [ori_lane + 1] \<and>
    (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)"
    by auto
next
  fix y
  assume bas: "start_time \<le> y \<and>
         y \<le> start_time + length rects \<and>
         lane_detection (rects ! (y - start_time)) = Boundaries [ori_lane + 1] \<and>
         (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < y - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)"  
  show "time \<le> y"
  proof (rule ccontr)
    assume "\<not> time \<le> y"
    hence "y < time" by auto
    from bas have 1: "0 \<le> y - start_time" by auto    
    with `y < time` have 2: "y - start_time < time - start_time"  using bas diff_less_mono by blast        
    have " (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)" 
      using start_inc_lane_ori_lane[OF assms] by auto
    with 1 and 2 have "lane_detection (rects ! (y - start_time)) = Lane ori_lane" by auto    
    with bas show "False" by auto    
  qed      
qed
  
theorem start_inc_lane_correctness0: 
  assumes "start_inc_lane rects ori_lane 0 = Some (time, rest)"
  shows "(LEAST n. n \<le> length rects \<and> 
                    lane_detection (rects ! n) = Boundaries [ori_lane + 1] \<and> 
                    (\<forall>m. m < n \<longrightarrow> lane_detection (rects ! m) = Lane ori_lane)) = time"   
  using start_inc_lane_general_correctness[OF assms] by auto
  
    
theorem start_inc_lane_drop:
  assumes "start_inc_lane rects ori_lane t1 = Some (t2, rest)"
  shows "rest = drop (t2 - t1 + 1) rects"  
  using assms
proof (induction rects arbitrary:t1)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?case by auto
  next
    case (Lane x)
    note case_lane = this      
    have "x = ori_lane \<or> x \<noteq> ori_lane" by auto
    moreover
    { assume "x = ori_lane"
      with case_cons case_lane have base: "start_inc_lane rects ori_lane (t1 + 1) = Some (t2, rest)" 
        unfolding start_inc_lane.simps by (auto split:detection_opt.splits) 
      with start_inc_lane_at_least[OF this] have "0 < t2 - t1" by auto           
      from base case_cons have "rest = drop (t2 - (t1 + 1) + 1) rects" by auto
      hence "rest = drop (t2 - t1) rects" using `0 < t2 - t1` 
        by (metis Nat.le_imp_diff_is_add One_nat_def Suc_leI diff_diff_add)         
      hence ?case using drop_cons[OF `0 < t2 - t1`] 
        by (simp add: \<open>\<And>xs x. drop (t2 - t1) (x # xs) = drop (t2 - t1 - 1) xs\<close>) }
    moreover
    { assume "x \<noteq> ori_lane"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }  
    ultimately show ?case by auto  
  next
    case (Boundaries x)
    note case_bound = this 
    with boundaries_not_empty have "x \<noteq> []" by auto
    have "tl x = [] \<and> hd x = ori_lane + 1 \<or> \<not> (tl x = [] \<and> hd x = ori_lane + 1)" by auto
    moreover
    { assume "tl x = [] \<and> hd x = ori_lane + 1"
      with case_cons case_bound have "t1 = t2 \<and> rects = rest" unfolding start_inc_lane.simps
      proof -
        assume a1: "(case lane_detection a of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (t1 + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (t1, rects) else None) = Some (t2, rest)"
        have "Some (t1, rects) = (case Boundaries x of Outside \<Rightarrow> None | Lane n \<Rightarrow> if n = ori_lane then start_inc_lane rects n (t1 + 1) else None | Boundaries ns \<Rightarrow> if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (t1, rects) else None)"
          by (simp add: \<open>tl x = [] \<and> hd x = ori_lane + 1\<close>)
        then show ?thesis
          using a1 by (simp add: case_bound)
      qed
      hence ?case by auto  }         
    moreover
    { assume "\<not> (tl x = [] \<and> hd x = ori_lane + 1)"
          with sym[OF case_bound] case_cons(2) have ?case by auto }            
    ultimately show ?case by auto      
  qed
qed
    
    
fun finish_inc_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "finish_inc_lane [] _ _ = None" | 
  "finish_inc_lane (rect # rects) bound_id num = (case lane_detection rect of 
                                                       Outside \<Rightarrow> None
                                                     (* If the it touches more than one boundaries or not the specified boundary, it will not be considered as initial part of overtaking *)                                                    
                                                     | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = bound_id then finish_inc_lane rects bound_id (num + 1) else None) 
                                                     (* If it does not arrive on the lane specified, then it will not be considered as part of overtaking*)
                                                     | Lane n \<Rightarrow> (if n = bound_id then Some (num, rects) else None))" 

theorem finish_inc_lane_not_nil:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  shows "rects \<noteq> []"    
  using assms by auto
    
theorem finish_inc_lane_cons:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  obtains a rects' where "rects = a # rects'" using finish_inc_lane_not_nil[OF assms]
  by (meson list.exhaust_sel)    
  
theorem finish_inc_lane_cases_neq:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  shows "ld_res \<noteq> Outside"  
proof -
  from finish_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'"
    by auto
  from assms(1) show ?thesis unfolding rects finish_inc_lane.simps ld_res_def by auto
qed
  
theorem finish_inc_lane_cases:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  shows "\<exists>n ns. ld_res = Lane n \<or> ld_res = Boundaries ns"
proof -
  from finish_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'"
    by auto
  from finish_inc_lane_cases_neq[OF assms(1)] have "ld_res \<noteq> Outside" unfolding ld_res_def
    by auto
  thus ?thesis by (induction ld_res) (auto)    
qed

theorem finish_inc_lane_cases_obtain:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  obtains n ns where "ld_res = Lane n \<or> ld_res = Boundaries ns"
  using finish_inc_lane_cases[OF assms(1)] unfolding ld_res_def by auto

theorem finish_inc_lane_cases_bound:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Boundaries ids"
  shows "ids = [bound_id]"
proof -
  from finish_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'"
    by auto
  hence "ld_res = lane_detection a" unfolding ld_res_def rects by auto
  with assms(3) have "lane_detection a = Boundaries ids" by auto
  from assms(1) have "(if tl ids = [] \<and> hd ids = bound_id then finish_inc_lane rects' bound_id (start_time + 1) else None) =
  Some (time, rest)" (is "?if = _") 
    unfolding rects finish_inc_lane.simps `lane_detection a = Boundaries ids`
    by auto
  also have "... \<noteq> None" by auto
  finally have "?if \<noteq> None" by auto
  hence "tl ids = [] \<and> hd ids = bound_id" by meson
  hence "ids = [bound_id]" 
    using \<open>lane_detection a = Boundaries ids\<close> boundaries_not_empty hd_Cons_tl by force
  thus ?thesis using assms(2) by auto         
qed
  
theorem finish_inc_lane_cases_lane:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Lane n"
  shows "n = bound_id"
proof -
  from finish_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'"
    by auto
  hence "ld_res = lane_detection a" unfolding ld_res_def rects by auto
  with assms(3) have "lane_detection a = Lane n" by auto
  from assms(1) have "(if n = bound_id then Some (start_time, rects') else None) = Some (time, rest)"
    (is "?if = _")
    unfolding rects finish_inc_lane.simps `lane_detection a = Lane n` by auto
  also have "... \<noteq> None" by auto
  finally have "?if \<noteq> None" by auto
  thus "n = bound_id"      
  using \<open>lane_detection a = Lane n\<close> boundaries_not_empty hd_Cons_tl by force
qed
      
theorem finish_inc_lane_bound_tail:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Lane n" 
  shows "rest = tl rects"
proof -
  from finish_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'"
    by auto
  hence "ld_res = lane_detection a" unfolding ld_res_def rects by auto
  with assms(3) have "lane_detection a = Lane n" by auto
  with finish_inc_lane_cases_lane[OF assms(1)] have "n = bound_id" unfolding rects
    by auto      
  with `lane_detection a = Lane n` have "lane_detection a = Lane bound_id"
    by auto
  from assms(1) show ?thesis unfolding rects finish_inc_lane.simps `lane_detection a = Lane bound_id`
    by auto
qed 
  
theorem finish_inc_lane_cases2:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  shows "ld_res = Lane bound_id \<or> ld_res = Boundaries [bound_id]"
proof -
  from finish_inc_lane_cons[OF assms(1)] obtain a rects' where rects: "rects = a # rects'"
    by auto
  from finish_inc_lane_cases_obtain[OF assms(1)] obtain n ns where 
    "lane_detection a = Lane n \<or> lane_detection a = Boundaries ns" unfolding rects by auto
  moreover
  { assume *: "lane_detection a = Lane n"
    with finish_inc_lane_cases_lane[OF assms(1)] have "n = bound_id" unfolding rects
        by auto
    hence ?thesis unfolding ld_res_def rects using * by auto }
  moreover
  { assume **: "lane_detection a = Boundaries ns"
    with finish_inc_lane_cases_bound[OF assms(1)] have "ns = [bound_id]" unfolding rects  
      by auto
    hence ?thesis unfolding ld_res_def rects using ** by auto }
  ultimately show ?thesis by auto    
qed
  
theorem finish_inc_lane_decrease_length:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  shows "length rest < length rects"
  using assms  
proof (induction rects arbitrary:start_time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from finish_inc_lane_cases2[OF case_cons(2)] have "lane_detection a = Lane bound_id \<or> 
                                                     lane_detection a = Boundaries [bound_id]"
    by auto
  moreover
  { assume "lane_detection a = Lane bound_id"
    from case_cons(2) have "rest = rects" unfolding finish_inc_lane.simps `lane_detection a = Lane bound_id`
      by auto
    hence "length rest < length (a # rects)" by auto }
  moreover
  { assume "lane_detection a = Boundaries [bound_id]"
    from case_cons(2) have "finish_inc_lane rects bound_id (start_time + 1) = Some (time, rest)"
      unfolding finish_inc_lane.simps `lane_detection a = Boundaries [bound_id]` by auto
    with case_cons(1)[OF this] have "length rest < length rects" by auto       
    hence "length rest < length (a # rects)" by auto }      
  ultimately show ?case by auto  
qed
      
theorem finish_inc_lane_at_least: 
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  shows "start_time \<le> time"  
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?thesis by auto  
  next
    case (Boundaries x)    
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto          
    have "tl x = [] \<and> hd x = bound_id  \<or> \<not> (tl x = [] \<and> hd x = bound_id)" by auto  
    moreover
    { assume "tl x = [] \<and> hd x = bound_id"
      with sym[OF case_bound] case_cons(2) have "finish_inc_lane rects bound_id (start_time + 1) = Some (time, rest)"
        unfolding finish_inc_lane.simps  by auto
      from case_cons(1)[OF this] have "start_time + 1 \<le> time"  by auto
      hence ?case by auto }
    moreover
    { assume f: "\<not> (tl x = [] \<and> hd x = bound_id)"
      with sym[OF case_bound] case_cons(2) have ?case by auto }      
    ultimately show ?case by auto
  next
    case (Lane x)
    note case_lane = this      
    have "x = bound_id \<or> x \<noteq> bound_id" by auto
    moreover        
    { assume "x = bound_id"
      with sym[OF case_lane] case_cons(2) have "time = start_time "
        unfolding finish_inc_lane.simps by auto
      hence ?case by auto }  
    moreover
    { assume "x \<noteq> bound_id"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }    
    ultimately show ?case by auto        
  qed
qed    
  
theorem finish_inc_lane_at_most: 
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  shows "time \<le> start_time + length rects"  
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this  
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?case by auto 
  next
    case (Lane x)
    note case_lane = this      
    have "x = bound_id \<or> x \<noteq> bound_id" by auto
    moreover        
    { assume "x = bound_id"
      with sym[OF case_lane] case_cons(2) have "time = start_time "
        unfolding finish_inc_lane.simps by auto
      hence ?case by auto }
    moreover
    { assume "x \<noteq> bound_id"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }          
    ultimately show ?case by auto
  next
    case (Boundaries x)
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto          
    have "tl x = [] \<and> hd x = bound_id  \<or> \<not> (tl x = [] \<and> hd x = bound_id)" by auto 
    moreover
    { assume "tl x = [] \<and> hd x = bound_id"
      with sym[OF case_bound] case_cons(2) have "finish_inc_lane rects bound_id (start_time + 1) = Some (time, rest)"
        unfolding finish_inc_lane.simps  by auto      
      from case_cons(1)[OF this] have ?case by auto }
    moreover
    { assume f: "\<not> (tl x = [] \<and> hd x = bound_id)"
      with sym[OF case_bound] case_cons(2) have ?case by auto }       
    ultimately show ?case by auto
  qed    
qed    
  
theorem finish_inc_lane_lane: 
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  shows "lane_detection (rects ! (time - start_time)) = Lane bound_id"    
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this  
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?case by auto
  next
    case (Lane x)
    note case_lane = this      
    have "x = bound_id \<or> x \<noteq> bound_id" by auto 
    moreover        
    { assume "x = bound_id"
      with sym[OF case_lane] case_cons(2) have "time = start_time "
        unfolding finish_inc_lane.simps by auto
      hence ?case using sym[OF case_lane] `x = bound_id` by auto}
    moreover
    { assume "x \<noteq> bound_id"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }          
    ultimately show ?case by auto
  next
    case (Boundaries x)
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto          
    have "tl x = [] \<and> hd x = bound_id  \<or> \<not> (tl x = [] \<and> hd x = bound_id)" by auto   
    moreover
    { assume "tl x = [] \<and> hd x = bound_id"
      with sym[OF case_bound] case_cons(2) have *: "finish_inc_lane rects bound_id (start_time + 1) = Some (time, rest)"
        unfolding finish_inc_lane.simps  by auto
      with finish_inc_lane_at_least[OF this] have "0 < time - start_time" by auto    
      from case_cons(1)[OF *] have ?case using nth_Cons_pos[OF `0 < time - start_time`] 
        by (simp add: \<open>\<And>xs x. (x # xs) ! (time - start_time) = xs ! (time - start_time - 1)\<close>) }
    moreover
    { assume f: "\<not> (tl x = [] \<and> hd x = bound_id)"
      with sym[OF case_bound] case_cons(2) have ?case by auto }
    ultimately show ?case by auto
  qed    
qed
      
theorem finish_inc_lane_boundaries: 
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"  
  shows "\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id]"
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto 
next
  case (Cons a rects)
  note case_cons = this  
  obtain ld_res where "ld_res = lane_detection a" by auto    
  then show ?case 
  proof (induction ld_res)
    case Outside
    with case_cons show ?case by auto
  next
    case (Lane x)
    note case_lane = this      
    have "x = bound_id \<or> x \<noteq> bound_id" by auto    
    { assume "x = bound_id"
      with sym[OF case_lane] case_cons(2) have "time = start_time "
        unfolding finish_inc_lane.simps by auto
      hence ?case using sym[OF case_lane] `x = bound_id` by auto}
    moreover
    { assume "x \<noteq> bound_id"
      with case_lane case_cons(2) have ?case by (auto split:detection_opt.splits) }    
    ultimately show ?case by auto
  next
    case (Boundaries x)
    note case_bound = this      
    with boundaries_not_empty have "x \<noteq> []" by auto          
    have "tl x = [] \<and> hd x = bound_id  \<or> \<not> (tl x = [] \<and> hd x = bound_id)" by auto   
    moreover
    { assume "tl x = [] \<and> hd x = bound_id"
      with sym[OF case_bound] case_cons(2) have *: "finish_inc_lane rects bound_id (start_time + 1) = Some (time, rest)"
        unfolding finish_inc_lane.simps  by auto
      from case_cons(1)[OF this] have **: "\<forall>m. 0 \<le> m - (start_time + 1) \<and> m - (start_time + 1) < time - (start_time + 1) \<longrightarrow>
      lane_detection (rects ! (m - (start_time + 1))) = Boundaries [bound_id]" by auto          
      with finish_inc_lane_at_least[OF *] have "0 < time - start_time" by auto    
      have ?case 
      proof (rule allI, rule impI) 
        fix m
        assume asm: "0 \<le> m - start_time \<and> m - start_time < time - start_time"
        have "m = start_time \<or> m < start_time \<or> m > start_time" by auto
        moreover
        { assume "m = start_time"
          hence "lane_detection ((a # rects) ! (m - start_time)) = lane_detection a" by auto  
          also have "... = Boundaries x" using case_bound by auto
          also have "... = Boundaries [bound_id]" using `tl x = [] \<and> hd x = bound_id`
            using list.collapse[OF `x \<noteq> []`] by auto
          finally have "lane_detection ((a # rects) ! (m - start_time)) = Boundaries [bound_id]"
            by auto }
        moreover
        { assume "m < start_time"
          hence "lane_detection ((a # rects) ! (m - start_time)) = lane_detection a" by auto  
          also have "... = Boundaries x" using case_bound by auto
          also have "... = Boundaries [bound_id]" using `tl x = [] \<and> hd x = bound_id`
            using list.collapse[OF `x \<noteq> []`] by auto
          finally have "lane_detection ((a # rects) ! (m - start_time)) = Boundaries [bound_id]"
            by auto }
        moreover
        { assume "m > start_time"
          hence "0 < m - start_time" by auto
          hence hyp1: "0 \<le> m - (start_time + 1)" by auto    
          from asm have "m - start_time < time - start_time" by auto
          hence "m - start_time - 1 < time - start_time - 1"  
            using \<open>0 < m - start_time\<close> gr_implies_not0 by auto
          with hyp1 ** have "lane_detection (rects ! (m - (start_time + 1))) = Boundaries [bound_id]"    
            by auto 
          hence "lane_detection ((a # rects) ! (m - start_time)) = Boundaries [bound_id]"
            using nth_Cons_pos[OF `0 < m - start_time`]
            by (simp add: \<open>\<And>xs x. (x # xs) ! (m - start_time) = xs ! (m - start_time - 1)\<close>) }
        ultimately show "lane_detection ((a # rects) ! (m - start_time)) = Boundaries [bound_id]"  
          by blast
      qed }
    moreover
    { assume f: "\<not> (tl x = [] \<and> hd x = bound_id)"
      with sym[OF case_bound] case_cons(2) have ?case by auto }
    ultimately show ?case by auto
  qed    
qed    
    
theorem finish_inc_lane_general_correctness:
  assumes "finish_inc_lane rects bound_id start_time = Some (time, rest)"
  shows "(LEAST n. start_time \<le> n \<and> n \<le> start_time + length rects \<and> 
                    lane_detection (rects ! (n - start_time)) = Lane bound_id \<and> 
                    (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < n - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])) = time"    
proof (rule Least_equality)
  have "start_time \<le> time" using finish_inc_lane_at_least[OF assms] by auto
  moreover      
  have "time \<le> start_time + length rects" using finish_inc_lane_at_most[OF assms] by auto     
  moreover
  have " lane_detection (rects ! (time - start_time)) = Lane bound_id"  
    using finish_inc_lane_lane[OF assms] by auto
  moreover
  have " (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])" 
    using finish_inc_lane_boundaries[OF assms] by auto
  ultimately show "start_time \<le> time \<and>
    time \<le> start_time + length rects \<and>
    lane_detection (rects ! (time - start_time)) = Lane bound_id \<and>
    (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])"
    by auto  
next
  fix y
  assume bas: "start_time \<le> y \<and>
         y \<le> start_time + length rects \<and>
         lane_detection (rects ! (y - start_time)) = Lane bound_id \<and>
         (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < y - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])"  
  show "time \<le> y"
  proof (rule ccontr)
    assume "\<not> time \<le> y"
    hence "y < time" by auto
    from bas have 1: "0 \<le> y - start_time" by auto    
    with `y < time` have 2: "y - start_time < time - start_time"  using bas diff_less_mono by blast        
    have "(\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])" 
      using finish_inc_lane_boundaries[OF assms] by auto
    with 1 and 2 have "lane_detection (rects ! (y - start_time)) = Boundaries [bound_id]" by auto    
    with bas show "False" by auto    
  qed         
qed
    
fun start_dec_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "start_dec_lane _ 0 _ = None" |  \<comment> \<open>cannot return to original lane if it is the the rightmost lane\<close>
  "start_dec_lane [] ori_lane _ = None" | 
  "start_dec_lane (rect # rects) ori_lane num = (case lane_detection rect of
                                                      Outside \<Rightarrow> None 
                                                    | Lane n  \<Rightarrow> (if n = ori_lane then start_dec_lane rects n (num + 1) else None) 
                                                    | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = ori_lane then Some (num, rects) else None))" 

theorem start_dec_lane_not_nil:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  shows "rects \<noteq> []"
  using assms
proof (induction ori_lane)
  case 0
  then show ?case unfolding start_dec_lane.simps by auto
next
  case (Suc ori_lane)  
  then show ?case by (cases "rects = []") auto
qed
  
theorem start_dec_lane_cons:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  obtains a rects' where "rects = a # rects'"
  using start_dec_lane_not_nil[OF assms]
  by (induction rects) (auto)  
  
theorem start_dec_lane_cases_neq:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  shows "ld_res \<noteq> Outside"
proof (rule ccontr)
  assume "\<not> ld_res \<noteq> Outside"
  hence "ld_res = Outside" by auto
  from start_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'" by auto 
  with `ld_res = Outside` have "lane_detection a = Outside" unfolding ld_res_def by auto    
  from assms(1) and `ld_res = Outside` show "False" unfolding `rects = a # rects'` `ori_lane = Suc n`  
     start_dec_lane.simps `lane_detection a = Outside` by auto  
qed
  
theorem start_dec_lane_cases:    
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  shows "\<exists>id ids. ld_res = Lane id \<or> ld_res = Boundaries ids"
proof -
  from start_dec_lane_cases_neq[OF assms(1-2)] have "ld_res \<noteq> Outside"
    unfolding ld_res_def by auto
  thus ?thesis by (induction ld_res) (auto)      
qed
  
theorem start_dec_lane_cases2:    
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  obtains id ids where "ld_res = Lane id \<or> ld_res = Boundaries ids"
  using start_dec_lane_cases[OF assms(1-2)] ld_res_def by auto
  
theorem start_dec_lane_cases_bound:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Boundaries ids"
  shows "ids = [ori_lane]"
proof -
  from start_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"  
    by auto
  from assms(4) have "lane_detection a = Boundaries ids" unfolding ld_res_def
    `rects = a # rects'` by auto
  from assms(1) and assms(4) have "(if tl ids = [] \<and> hd ids = Suc n then Some (start_time, rects') else None) = Some (time, rest)" 
    unfolding `rects = a # rects'` `ori_lane = Suc n`
    start_dec_lane.simps `lane_detection a = Boundaries ids` by auto      
  hence "tl ids = [] \<and> hd ids = Suc n"  by (meson option.distinct(1))  
  hence "ids = [Suc n]" 
    using \<open>lane_detection a = Boundaries ids\<close> boundaries_not_empty hd_Cons_tl by force
  thus ?thesis using assms(2) by auto     
qed
  
theorem start_dec_lane_cases_bound_tail:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Boundaries ids"
  shows "start_time = time" and "rest = tl rects"
proof -
  from start_dec_lane_cases_bound[OF assms(1-2)] assms(4) have "ids = [ori_lane]"
    unfolding ld_res_def by auto
  from start_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"  
    by auto  
  from assms(4) have "lane_detection a = Boundaries [ori_lane]" unfolding `rects = a #rects'`
    `ori_lane = Suc n`  ld_res_def `ids = [ori_lane]` by auto
  from assms(1) show "start_time = time" unfolding `rects = a # rects'` `ori_lane = Suc n`
    start_dec_lane.simps `lane_detection a = Boundaries [ori_lane]` by auto
  from assms(1) show "rest = tl rects" unfolding `rects = a # rects'` `ori_lane = Suc n`
    start_dec_lane.simps `lane_detection a = Boundaries [ori_lane]` by auto
qed
    
theorem start_dec_lane_cases_lane:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Lane i"
  shows "i = ori_lane" 
proof -
  from start_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"  
    by auto
  from assms(4) have "lane_detection a = Lane i" unfolding ld_res_def
    `rects = a # rects'` by auto  
  from assms(1) and assms(4) have " (if i = Suc n then start_dec_lane rects' i (start_time + 1) else None) = Some (time, rest)"
    unfolding `rects = a # rects'` `ori_lane = Suc n` start_dec_lane.simps `lane_detection a = Lane i`
    by auto  
  hence "i = Suc n" by (meson option.distinct)      
  thus ?thesis using assms(2) by auto
qed

theorem start_dec_lane_cases_lane_tail:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"    
  assumes "ld_res = Lane i"
  shows "start_dec_lane (tl rects) ori_lane (start_time + 1) = Some (time, rest)"
proof -
  from start_dec_lane_cases_lane[OF assms(1-2)] assms(4) have "i = ori_lane"
    unfolding ld_res_def by auto      
  from start_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"
    by auto
  hence "lane_detection a = Lane ori_lane" using assms(4) unfolding ld_res_def
      `i = ori_lane` by auto
  from assms(1) show ?thesis unfolding `rects = a # rects'` `ori_lane = Suc n`    
    start_dec_lane.simps `lane_detection a = Lane ori_lane` by auto    
qed
  
theorem start_dec_lane_cases_imp:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"     
  shows "ld_res = Lane ori_lane \<or> ld_res = Boundaries [ori_lane]"
  using assms start_dec_lane_cases2[OF assms(1-2)] start_dec_lane_cases_lane[OF assms(1-2)]
  start_dec_lane_cases_bound[OF assms(1-2)] by auto

theorem start_dec_lane_case_final:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  defines "ld_res \<equiv> lane_detection (hd rects)"     
  shows "ld_res = Lane ori_lane \<and> start_dec_lane (tl rects) ori_lane (start_time + 1) = Some (time, rest) \<or>
         ld_res = Boundaries [ori_lane] \<and> start_time = time \<and> rest = tl rects"
proof -
  from start_dec_lane_cases_imp[OF assms(1-2)] 
  have "lane_detection (hd rects) = Lane ori_lane \<or>  lane_detection (hd rects) = Boundaries [ori_lane ] "  
    by auto
  moreover
  { assume "lane_detection (hd rects) = Lane ori_lane"
    with start_dec_lane_cases_lane_tail[OF assms(1-2) this] have ?thesis unfolding ld_res_def by auto }
  moreover
  { assume "lane_detection (hd rects) = Boundaries [ori_lane]"
    with start_dec_lane_cases_bound_tail[OF assms(1-2) this] have ?thesis unfolding ld_res_def by auto }  
  ultimately show ?thesis by auto
qed      
    
theorem start_dec_lane_at_least:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"  
  shows "start_time \<le> time"
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  thus ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from start_dec_lane_case_final[OF case_cons(2-3)] 
  consider "start_dec_lane (tl (a # rects)) ori_lane (start_time + 1) = Some (time, rest)" |
           "start_time = time \<and> rest = tl (a # rects)" by auto
  thus ?case
  proof (cases)
    case 1
    hence "start_dec_lane rects ori_lane (start_time + 1) = Some (time, rest)"  by auto
    with case_cons(1)[OF this case_cons(3)] have "start_time + 1 \<le> time" by auto  
    then show ?thesis by auto
  next
    case 2      
    then show ?thesis by auto
  qed    
qed    

theorem start_dec_lane_at_most:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"    
  shows "time \<le> start_time + length rects"
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from start_dec_lane_case_final[OF case_cons(2-3)] 
  consider "start_dec_lane (tl (a # rects)) ori_lane (start_time + 1) = Some (time, rest)" |
           "start_time = time \<and> rest = tl (a # rects)" by auto
  thus ?case
  proof (cases)
    case 1
    hence "start_dec_lane rects ori_lane (start_time + 1) = Some (time, rest)" by auto  
    from case_cons(1)[OF this case_cons(3)] have "time \<le> start_time + 1 + length rects"
      by auto
    then show ?thesis by auto
  next
    case 2
    then show ?thesis by auto
  qed
qed    
  
theorem start_dec_lane_boundaries:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"    
  shows "lane_detection (rects ! (time - start_time)) = Boundaries [ori_lane]"  
  using assms
proof (induction rects arbitrary: start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from start_dec_lane_case_final[OF case_cons(2-3)] 
  consider "start_dec_lane (tl (a # rects)) ori_lane (start_time + 1) = Some (time, rest)" |
           "lane_detection a = Boundaries [ori_lane] \<and> start_time = time \<and> rest = tl (a # rects)" by auto
  thus ?case
  proof (cases)
    case 1
    hence t: "start_dec_lane rects ori_lane (start_time + 1) = Some (time, rest)" by auto
    from start_dec_lane_at_least[OF this case_cons(3)] have "0 < time - start_time" by auto     
    from case_cons(1)[OF t case_cons(3)] have "lane_detection (rects ! (time - (start_time + 1))) = Boundaries [ori_lane] "
      by auto
    hence *: "lane_detection (rects ! (time - start_time - 1)) = Boundaries [ori_lane]" by auto
    have **: "rects ! (time - start_time - 1) = (a # rects) ! (time - start_time)" 
      using sym[OF nth_Cons_pos[OF `0 < time - start_time`]] by auto   
    from * show ?thesis unfolding ** by auto  
  next
    case 2  
    then show ?thesis by auto
  qed    
qed    
     
theorem start_dec_lane_ori_lane:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"    
  shows "\<forall>t. 0 \<le> t - start_time \<and> t - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (t - start_time)) = Lane ori_lane"
  using assms
proof (induction rects arbitrary:start_time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from start_dec_lane_case_final[OF case_cons(2-3)] 
  consider "lane_detection a = Lane ori_lane \<and> start_dec_lane (tl (a # rects)) ori_lane (start_time + 1) = Some (time, rest)" |
           "lane_detection a = Boundaries [ori_lane] \<and> start_time = time \<and> rest = tl (a # rects)" by auto
  thus ?case
  proof (cases)
    case 1
    hence "lane_detection a = Lane ori_lane" and "start_dec_lane rects ori_lane (start_time + 1) = Some (time, rest)" by auto  
    from case_cons(1)[OF this(2) case_cons(3)]
    have ind: " \<forall>t. 0 \<le> t - (start_time + 1) \<and> t - (start_time + 1) < time - (start_time + 1) \<longrightarrow> lane_detection (rects ! (t - (start_time + 1))) = Lane ori_lane"
      by auto
    show ?thesis
    proof (rule allI, rule impI)
      fix t
      assume asm: "0 \<le> t - start_time \<and> t - start_time < time - start_time"  
      consider "t - start_time \<le> 0" | "0 < t - start_time" by linarith
      thus "lane_detection ((a # rects) ! (t - start_time)) = Lane ori_lane"          
      proof (cases)
        case 1
        then show ?thesis using `lane_detection a = Lane ori_lane` by auto
      next
        case 2
        with asm have "0 \<le> t - (start_time + 1) \<and> t - (start_time + 1) < time - (start_time + 1)" by auto
        with ind have *: "lane_detection (rects ! (t - (start_time + 1))) = Lane ori_lane" by auto
        from sym[OF nth_Cons_pos[OF 2]] have "rects ! (t - start_time - 1) = (a # rects) ! (t - start_time)"
          by auto
        then show ?thesis using * by auto 
      qed         
    qed      
  next
    case 2
    then show ?thesis by auto
  qed
qed    
    
theorem start_dec_lane_general_correctness:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  assumes "ori_lane = Suc n"    
  shows "(LEAST n. start_time \<le> n  \<and> n \<le> start_time + length rects \<and> 
                   lane_detection (rects ! (n - start_time)) = Boundaries [ori_lane] \<and> 
                   (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < n - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)) = time"
proof (rule Least_equality)
  have "start_time \<le> time" using start_dec_lane_at_least[OF assms] by auto
  moreover
  have "time \<le> start_time + length rects" using start_dec_lane_at_most[OF assms] by auto    
  moreover
  have "lane_detection (rects ! (time - start_time)) = Boundaries [ori_lane]"
    using start_dec_lane_boundaries[OF assms] by auto
  moreover
  have "(\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)"    
    using start_dec_lane_ori_lane[OF assms] by auto
  ultimately show "start_time \<le> time \<and>
    time \<le> start_time + length rects \<and>
    lane_detection (rects ! (time - start_time)) = Boundaries [ori_lane] \<and>
    (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)"
    by auto
next
  fix y
  assume bas: "start_time \<le> y \<and>
         y \<le> start_time + length rects \<and>
         lane_detection (rects ! (y - start_time)) = Boundaries [ori_lane] \<and>
         (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < y - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)"
  show "time \<le> y"
  proof (rule ccontr)
    assume "\<not> time \<le> y"  
    hence "y < time" by auto
    from bas have 1: "0 \<le> y - start_time" by auto    
    with `y < time` have 2: "y - start_time < time - start_time" using bas diff_less_mono by blast
    have " (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Lane ori_lane)"
      using start_dec_lane_ori_lane[OF assms] by auto
    with 1 and 2 have "lane_detection (rects ! (y - start_time)) = Lane ori_lane" by auto
    with bas show "False" by auto        
  qed
qed
  
theorem start_dec_lane_correctness0:
  assumes "start_dec_lane rects ori_lane 0 = Some (time, rest)"
  assumes "ori_lane = Suc n"    
  shows "(LEAST n. n \<le> length rects \<and> 
                   lane_detection (rects ! n) = Boundaries [ori_lane] \<and> 
                   (\<forall>m. m < n  \<longrightarrow> lane_detection (rects ! m) = Lane ori_lane)) = time"
  using start_dec_lane_general_correctness[OF assms] by auto    
    
theorem start_dec_lane_drop:
  assumes "start_dec_lane rects ori_lane t1 = Some (t2, rest)"
  assumes "ori_lane = Suc n"    
  shows "rest = drop (t2 - t1 + 1) rects"
  using assms
proof (induction rects arbitrary:t1)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this   
  from start_dec_lane_case_final[OF case_cons(2-3)] 
  consider "lane_detection a = Lane ori_lane \<and> start_dec_lane (tl (a # rects)) ori_lane (t1 + 1) = Some (t2, rest)" |
           "lane_detection a = Boundaries [ori_lane] \<and> t1 = t2 \<and> rest = tl (a # rects)" by auto
  thus ?case
  proof (cases)
    case 1
    hence t: "start_dec_lane rects ori_lane (t1 + 1) = Some (t2, rest)" by auto 
    from start_dec_lane_at_least[OF this case_cons(3)] have "0 < t2 - t1" by auto        
    from case_cons(1)[OF t case_cons(3)] have "rest = drop (t2 - (t1 + 1) + 1) rects" by auto
    hence "rest = drop (t2 - t1) rects" using `0 < t2 - t1` 
      by (metis Nat.le_imp_diff_is_add One_nat_def Suc_leI diff_diff_add)         
    thus ?thesis using drop_cons[OF `0 < t2 - t1`] 
        by (simp add: \<open>\<And>xs x. drop (t2 - t1) (x # xs) = drop (t2 - t1 - 1) xs\<close>)            
  next
    case 2      
    then show ?thesis by auto
  qed    
qed
  
fun finish_dec_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "finish_dec_lane  _ 0 _ = None" | \<comment> \<open>cannot return to original lane if it is the the rightmost lane\<close>
  "finish_dec_lane [] _ _ = None" | 
  "finish_dec_lane (rect # rects) bound_id num = (case lane_detection rect of 
                                                       Outside \<Rightarrow> None 
                                                     | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = bound_id then finish_dec_lane rects bound_id (num + 1) else None) 
                                                     | Lane n \<Rightarrow> (if n = bound_id - 1 then Some (num, rects) else None))" 

theorem finish_dec_lane_not_nil:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  shows "rects \<noteq> []"
  using assms
proof (induction bound_id)
  case 0
  then show ?case by auto
next
  case (Suc bound_id)
  then show ?case by (cases "rects = []") auto
qed  
  
theorem finish_dec_lane_cons:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  obtains a rects' where "rects = a # rects'"
  using finish_dec_lane_not_nil[OF assms]
  by (induction rects) auto

theorem finish_dec_lane_cases_neq:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  shows "ld_res \<noteq> Outside"
proof (rule ccontr)
  assume "\<not> ld_res \<noteq> Outside"
  hence "ld_res = Outside" by auto
  from finish_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'" by auto
  with `ld_res = Outside` have "lane_detection a = Outside" unfolding ld_res_def by auto
  from assms(1) and `ld_res = Outside` show "False" unfolding `rects = a # rects'` `bound_id = Suc n`
    finish_dec_lane.simps `lane_detection a = Outside` by auto 
qed

theorem finish_dec_lane_cases:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)" 
  shows "\<exists>id ids. ld_res = Lane id \<or> ld_res = Boundaries ids"
proof -
  from finish_dec_lane_cases_neq[OF assms(1-2)] have "ld_res \<noteq> Outside"
    unfolding ld_res_def by auto
  thus ?thesis by (induction ld_res) auto
qed      
  
theorem finish_dec_lane_cases2:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  obtains id ids where "ld_res = Lane id \<or> ld_res = Boundaries ids"
  using finish_dec_lane_cases[OF assms(1-2)] ld_res_def by auto

theorem finish_dec_lane_cases_bound:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Boundaries ids"
  shows "ids = [bound_id]"
proof -
  from finish_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"
    by auto
  from assms(4) have "lane_detection a = Boundaries ids" unfolding ld_res_def
    `rects = a # rects'` by auto
  from assms(1) and assms(4) have "(if tl ids = [] \<and> hd ids = Suc n then finish_dec_lane rects' (Suc n) (start_time + 1) else None) = Some (time, rest)" 
    unfolding `rects = a # rects'` `bound_id = Suc n`
    finish_dec_lane.simps `lane_detection a = Boundaries ids` by auto      
  hence "tl ids = [] \<and> hd ids = Suc n"  by (meson option.distinct(1))  
  hence "ids = [Suc n]" 
    using \<open>lane_detection a = Boundaries ids\<close> boundaries_not_empty hd_Cons_tl by force
  thus ?thesis using assms(2) by auto     
qed
  
theorem finish_dec_lane_cases_bound_tail: 
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Boundaries ids"
  shows "finish_dec_lane (tl rects) bound_id (start_time + 1) = Some (time, rest)"
proof -
  from finish_dec_lane_cases_bound[OF assms(1-2)] assms(4) have "ids = [bound_id]"
    unfolding ld_res_def by auto
  from finish_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"  
    by auto  
  from assms(4) have "lane_detection a = Boundaries [bound_id]" unfolding `rects = a #rects'`
    `bound_id = Suc n`  ld_res_def `ids = [bound_id]` by auto
  from assms(1) show "finish_dec_lane (tl rects) bound_id (start_time + 1) = Some (time, rest)" 
    unfolding `rects = a # rects'` `bound_id = Suc n`
    finish_dec_lane.simps `lane_detection a = Boundaries [bound_id]` by auto
qed  
  
theorem finish_dec_lane_cases_lane:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"    
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Lane i"
  shows "i = bound_id - 1"    
proof -
  from finish_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"  
    by auto
  from assms(4) have "lane_detection a = Lane i" unfolding ld_res_def
    `rects = a # rects'` by auto  
  from assms(1) have "(if i = Suc n - 1 then Some (start_time, rects') else None) = Some (time, rest)" 
    unfolding `rects = a # rects'` `bound_id = Suc n` finish_dec_lane.simps `lane_detection a = Lane i` 
    by auto     
  hence "i = Suc n - 1" by (meson option.distinct)
  thus ?thesis using assms(2) by auto
qed
  
theorem finish_dec_lane_cases_lane_tail:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"    
  defines "ld_res \<equiv> lane_detection (hd rects)"
  assumes "ld_res = Lane i"
  shows "start_time = time" and "rest = tl rects"
proof -
  from finish_dec_lane_cases_lane[OF assms(1-2)] assms(4) have "i = bound_id - 1"
    unfolding ld_res_def by auto
  from finish_dec_lane_cons[OF assms(1)] obtain a rects' where "rects = a # rects'"
    by auto
  hence "lane_detection a = Lane (bound_id - 1)" using assms(4) unfolding ld_res_def
    `i = bound_id - 1` by auto
  from assms(1) show "start_time = time" unfolding `rects = a # rects'` `bound_id = Suc n`
    finish_dec_lane.simps `lane_detection a = Lane (bound_id - 1)` by auto
  from assms(1) show "rest = tl rects" unfolding `rects = a # rects'` `bound_id = Suc n`
    finish_dec_lane.simps `lane_detection a = Lane (bound_id - 1)` by auto
qed      
  
theorem finish_dec_lane_cases_imp:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  shows "ld_res = Lane (bound_id -1) \<or> ld_res = Boundaries [bound_id]"
  using assms finish_dec_lane_cases2[OF assms(1-2)] finish_dec_lane_cases_lane[OF assms(1-2)]
  finish_dec_lane_cases_bound[OF assms(1-2)] by auto
  
theorem finish_dec_lane_case_final:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  defines "ld_res \<equiv> lane_detection (hd rects)"
  shows "ld_res = Lane (bound_id - 1) \<and> start_time = time \<and> rest = tl rects \<or> 
         ld_res = Boundaries [bound_id] \<and> finish_dec_lane (tl rects) bound_id (start_time + 1) = Some (time, rest)"          
proof -
  from finish_dec_lane_cases_imp[OF assms(1-2)]
  have "lane_detection (hd rects) = Lane (bound_id - 1) \<or> lane_detection (hd rects) = Boundaries [bound_id]"
    by auto
  moreover
  { assume "lane_detection (hd rects) = Lane (bound_id - 1)"
    with finish_dec_lane_cases_lane_tail[OF assms(1-2) this] have ?thesis unfolding ld_res_def 
      by auto }
  moreover
  { assume "lane_detection (hd rects) = Boundaries [bound_id]"
    with finish_dec_lane_cases_bound_tail[OF assms(1-2) this] have ?thesis unfolding ld_res_def
      by auto }
  ultimately show ?thesis by auto
qed
  
theorem finish_dec_lane_at_least:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  shows "start_time \<le> time" 
  using assms
proof (induction rects arbitrary: start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from finish_dec_lane_case_final[OF case_cons(2-3)]  
  consider " start_time = time \<and> rest = tl (a # rects)" | 
    "finish_dec_lane (tl (a # rects)) bound_id (start_time + 1) = Some (time, rest)"
    by auto
  thus ?case
  proof (cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    hence "finish_dec_lane rects bound_id (start_time + 1) = Some (time, rest)" by auto
    with case_cons(1)[OF this case_cons(3)] show ?thesis by auto  
  qed    
qed    

theorem finish_dec_lane_at_most:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  shows "time \<le> start_time + length rects"
  using assms
proof (induction rects arbitrary:start_time time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from finish_dec_lane_case_final[OF case_cons(2-3)]
  consider "lane_detection (hd (a # rects)) = Lane (bound_id - 1) \<and> start_time = time \<and> rest = tl (a # rects)" |
    "lane_detection (hd (a # rects)) = Boundaries [bound_id] \<and> finish_dec_lane (tl (a # rects)) bound_id (start_time + 1) = Some (time, rest)"    
    by auto    
  thus ?case
  proof (cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    hence "finish_dec_lane rects bound_id (start_time + 1) = Some (time, rest)" by auto
    with case_cons(1)[OF this case_cons(3)] show ?thesis by auto       
  qed        
qed
  
theorem finish_dec_lane_boundaries:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  shows "lane_detection (rects ! (time - start_time)) = Lane (bound_id - 1)"
  using assms
proof (induction rects arbitrary: start_time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from finish_dec_lane_case_final[OF case_cons(2-3)]    
  consider "lane_detection (hd (a # rects)) = Lane (bound_id - 1) \<and> start_time = time \<and> rest = tl (a # rects)" |
    "lane_detection (hd (a # rects)) = Boundaries [bound_id] \<and> finish_dec_lane (tl (a # rects)) bound_id (start_time + 1) = Some (time, rest)"    
    by auto      
  thus ?case
  proof (cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    hence t: "finish_dec_lane rects bound_id (start_time + 1) = Some (time, rest)"
      by auto
    from finish_dec_lane_at_least[OF t case_cons(3)] have "0 < time - start_time" by auto 
    from case_cons(1)[OF t case_cons(3)] have t2: "lane_detection (rects ! (time - (start_time + 1))) = Lane (bound_id - 1)"
      by auto        
    from nth_Cons_pos[OF `0 < time - start_time`] have "(a # rects) ! (time - start_time) = rects ! (time - start_time - 1)"
      by auto
    with t2 show ?thesis by auto 
  qed
qed    
  
theorem finish_dec_lane_bound_id:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  shows "\<forall>t. 0 \<le> t - start_time \<and> t - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (t - start_time)) = Boundaries [bound_id]"    
  using assms
proof (induction rects arbitrary: start_time)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this
  from finish_dec_lane_case_final[OF case_cons(2-3)]    
  consider "lane_detection (hd (a # rects)) = Lane (bound_id - 1) \<and> start_time = time \<and> rest = tl (a # rects)" |
    "lane_detection (hd (a # rects)) = Boundaries [bound_id] \<and> finish_dec_lane (tl (a # rects)) bound_id (start_time + 1) = Some (time, rest)"    
    by auto      
  thus ?case 
  proof (cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    hence t: "finish_dec_lane rects bound_id (start_time + 1) = Some (time, rest)"
      by auto
    from 2 have "lane_detection a = Boundaries [bound_id]" by auto        
    from case_cons(1)[OF t case_cons(3)] have ind: "\<forall>t. 0 \<le> t - (start_time + 1) \<and> t - (start_time + 1) < time - (start_time + 1) \<longrightarrow>
      lane_detection (rects ! (t - (start_time + 1))) = Boundaries [bound_id]"
      by auto                
    show ?thesis
    proof (rule allI, rule impI)
      fix t
      assume asm: "0 \<le> t - start_time \<and> t - start_time < time - start_time"
      consider "t - start_time \<le> 0" | "0 < t - start_time" by linarith
      thus "lane_detection ((a # rects) ! (t - start_time)) = Boundaries [bound_id]"
      proof (cases)
        case 1
        then show ?thesis using `lane_detection a = Boundaries [bound_id]` by auto
      next
        case 2
        with asm have "0 \<le> t - (start_time + 1) \<and> t - (start_time + 1) < time - (start_time + 1)" 
          by auto
        with ind have *: "lane_detection (rects ! (t - (start_time + 1))) = Boundaries [bound_id]"
          by auto
        from sym[OF nth_Cons_pos[OF 2]] have "rects ! (t - start_time - 1) = (a # rects) ! (t - start_time)"
          by auto
        then show ?thesis using * by auto
      qed      
    qed      
  qed    
qed    

theorem finish_dec_lane_general_correctness:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  assumes "bound_id = Suc n"
  shows "(LEAST n. start_time \<le> n \<and> n \<le> start_time + length rects \<and> 
                   lane_detection (rects ! (n - start_time)) = Lane (bound_id - 1) \<and> 
                   (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < n - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])) = time"
proof (rule Least_equality)
  have "start_time \<le> time" using finish_dec_lane_at_least[OF assms] by auto
  moreover
  have "time \<le> start_time + length rects" using finish_dec_lane_at_most[OF assms] by auto    
  moreover
  have "lane_detection (rects ! (time - start_time)) = Lane (bound_id - 1)"
    using finish_dec_lane_boundaries[OF assms] by auto
  moreover
  have "(\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])"    
    using finish_dec_lane_bound_id[OF assms] by auto
  ultimately show "start_time \<le> time \<and>
    time \<le> start_time + length rects \<and>
    lane_detection (rects ! (time - start_time)) = Lane (bound_id - 1) \<and>
    (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])"
    by auto  
next
  fix y
  assume bas: "start_time \<le> y \<and>
         y \<le> start_time + length rects \<and>
         lane_detection (rects ! (y - start_time)) = Lane (bound_id - 1) \<and>
         (\<forall>m. 0 \<le> m - start_time \<and> m - start_time < y - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])"
  show "time \<le> y"
  proof (rule ccontr)
    assume "\<not> time \<le> y"
    hence "y < time" by auto      
    from bas have 1: "0 \<le> y - start_time" by auto
    with `y < time` have 2: "y - start_time < time - start_time" using bas diff_less_mono by auto
    have "(\<forall>m. 0 \<le> m - start_time \<and> m - start_time < time - start_time \<longrightarrow> lane_detection (rects ! (m - start_time)) = Boundaries [bound_id])"
      using finish_dec_lane_bound_id[OF assms] by auto
    with 1 and 2 have "lane_detection (rects ! (y - start_time)) = Boundaries [bound_id]" by auto
    with bas show "False" by auto        
  qed    
qed
  
text "This is the definition (or function) for (detecting) the occurrence of lane changing to the 
  left in right-hand traffic."
  
fun increase_lane :: "rectangle list \<Rightarrow> ((nat \<times> nat) \<times> rectangle list) option" where
  "increase_lane []    = None" |
  "increase_lane rects = (case initial_lane rects of 
                                    Outside \<Rightarrow> None 
                                  | Boundaries _ \<Rightarrow> None  (* it has to start in a lane -- not boundaries or outside *)
                                  | Lane n \<Rightarrow> (case start_inc_lane rects n 0 of 
                                                 None \<Rightarrow> None 
                                               | Some (num1, rest1) \<Rightarrow> (case finish_inc_lane rest1 n num1 of 
                                                                         None \<Rightarrow> None 
                                                                       | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))))" 

fun increase_lane2 :: "rectangle list \<Rightarrow> ((nat \<times> nat) \<times> rectangle list) option" where
  "increase_lane2 []    = None" |
  "increase_lane2 rects = (case initial_lane rects of  Outside \<Rightarrow> None  | Boundaries _ \<Rightarrow> None  
                                  | Lane n \<Rightarrow> do {
                                                (num1, rest1) \<leftarrow> start_inc_lane rects n 0;
                                                (num2, rest2) \<leftarrow> finish_inc_lane rest1 n num1;
                                                Some ((num1, num2), rest2) 
                                              })"
  
lemma increase_lane_some_not_nil:
  assumes "increase_lane rects = Some ((time1, time2) , rest)"
  shows "rects \<noteq> []"
  using assms by auto    

theorem increase_lane_some_outbound:
  assumes "increase_lane rects = Some ((time1, time2), rest)"
  shows "initial_lane rects \<noteq> Outside \<and> initial_lane rects \<noteq> Boundaries bds"
  using assms
proof (rule contrapos_pp)
  assume "\<not> (initial_lane rects \<noteq> Outside \<and> initial_lane rects \<noteq> Boundaries bds)"  
  hence "initial_lane rects = Outside \<or> initial_lane rects = Boundaries bds"
    by auto
  moreover
  { assume "initial_lane rects = Outside"
    hence "increase_lane rects = None" by(induction rects)(auto)
    hence "increase_lane rects \<noteq> Some ((time1, time2), rest)" by auto }
  moreover
  { assume "initial_lane rects = Boundaries bds"
    hence "increase_lane rects = None" by (induction rects) (auto)
    hence "increase_lane rects \<noteq> Some ((time1, time2), rest)" by auto }
  ultimately show "increase_lane rects \<noteq> Some ((time1, time2), rest)" by auto    
qed
    
theorem increase_lane_initial_lane:
  assumes "increase_lane rects = Some ((time1, time2), rest)"
  shows "\<exists>n. initial_lane rects = Lane n"
proof -
  from increase_lane_some_outbound[OF assms] have 
    no: "initial_lane rects \<noteq> Outside" and nb: "(\<forall>bds. initial_lane rects \<noteq> Boundaries bds)" by auto
  show "\<exists>n . initial_lane rects = Lane n"
  proof (induction "initial_lane rects")
    case Outside
    then show ?case using no by auto
  next
    case (Lane x)
    then show ?case by (auto intro: exI[where x="x"])
  next
    case (Boundaries x)
    from sym[OF this] show ?case using nb by auto 
  qed
qed
  
theorem increase_lane_initial_lane_obtains:
  assumes "increase_lane rects = Some ((time1, time2), rest)"
  obtains n where "initial_lane rects = Lane n"
  using increase_lane_initial_lane[OF assms] by auto   
    
theorem increase_lane_start_inc_lane:   
  assumes "increase_lane rects = Some ((time1, time2), rest)"
  shows "start_inc_lane rects ((glane \<circ> initial_lane) rects) 0 = Some (time1, drop (time1 + 1) rects)"
proof -
  from increase_lane_initial_lane_obtains[OF assms] obtain n where "initial_lane rects = Lane n"
    by auto
  from increase_lane_some_not_nil[OF assms] obtain a rects' where rects: "rects = a # rects'"
    by (meson list.exhaust_sel)
  with `initial_lane rects = Lane n` have "initial_lane (a  #rects') = Lane n" by auto
  from assms(1) 
    have *: "(case start_inc_lane (a # rects') n 0 of None \<Rightarrow> None
       | Some (num1, rest1) \<Rightarrow> (case finish_inc_lane rest1 n num1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))) = Some ((time1, time2), rest)" 
    unfolding rects increase_lane.simps `initial_lane (a # rects') = Lane n`
    by auto
  hence "start_inc_lane (a # rects') n 0 \<noteq> None" using option.distinct 
    by (metis (no_types, lifting) option.simps(4))
  then obtain num1 rest1 where "start_inc_lane (a # rects') n 0 = Some (num1, rest1)" by auto
  with * have **: "(case finish_inc_lane rest1 n num1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2)) = Some ((time1, time2), rest)"
    by auto
  hence "finish_inc_lane rest1 n num1 \<noteq> None" using option.distinct   
    by (metis (no_types, lifting) option.simps(4))
  then obtain num2 rest2 where "finish_inc_lane rest1 n num1 = Some (num2, rest2)" by auto
  with ** have "num1 = time1" and "num2 = time2" and "rest2 = rest" by auto
  from start_inc_lane_drop[OF `start_inc_lane (a # rects') n 0 = Some (num1, rest1)`] 
  have "rest1 = drop (num1 + 1) (a # rects')" by auto
  with `num1 = time1` and `start_inc_lane (a # rects') n 0 = Some (num1, rest1)` show ?thesis
    unfolding rects comp_def `initial_lane (a # rects') = Lane n` by auto   
qed
      
theorem 
  assumes "increase_lane rects = Some ((time1, time2),  rest)"
  defines "ori_lane \<equiv> glane (initial_lane rects)"
  defines "rects' \<equiv> drop (time1 + 1) rects"    
  shows "(LEAST n. n \<le> length rects \<and> 
                    lane_detection (rects ! n) = Boundaries [ori_lane + 1] \<and> 
                    (\<forall>m. m < n \<longrightarrow> lane_detection (rects ! m) = Lane ori_lane)) = time1" and 
        "(LEAST n. time1  \<le> n \<and> n \<le> time1  + length rects' \<and> 
                    lane_detection (rects' ! (n - time1)) = Lane ori_lane \<and> 
                    (\<forall>m. 0 \<le> m - time1 \<and> m - time1 < n - time1 \<longrightarrow> lane_detection (rects' ! (m - time1)) = Boundaries [ori_lane])) = time2"        
proof - 
  from assms(1) ori_lane_def
  show "(LEAST n. n \<le> length rects \<and> 
                    lane_detection (rects ! n) = Boundaries [ori_lane + 1] \<and> 
                    (\<forall>m. m < n \<longrightarrow> lane_detection (rects ! m) = Lane ori_lane)) = time1"
  proof (induction rects)
    case Nil
    then show ?case by auto
  next
    case (Cons a rects)
    note case_cons = this
    from increase_lane_some_outbound[OF case_cons(2)] obtain n where "initial_lane (a # rects) = Lane n"
      using detection_opt.exhaust_sel by blast
    hence "initial_lane (a # rects) = Lane ori_lane" unfolding case_cons by auto  
    with `initial_lane (a # rects) = Lane n` have "n = ori_lane" using detection_opt.exhaust_sel by auto    
    from `initial_lane (a # rects) = Lane n` case_cons(2) 
      have cs: "(case start_inc_lane (a # rects) n 0 of None \<Rightarrow> None
         | Some (num1, rest1) \<Rightarrow> (case finish_inc_lane rest1 n num1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))) = Some ((time1, time2), rest)" 
      unfolding increase_lane.simps by auto
    have "\<exists> num1 rest1. start_inc_lane (a # rects) n 0 = Some (num1, rest1)"
    proof (rule ccontr)
      assume "\<nexists>num1 rest1. start_inc_lane (a # rects) n 0 = Some (num1, rest1)"
      hence *: "\<forall>num1 rest1. start_inc_lane (a # rects) n 0 \<noteq> Some (num1, rest1)" by auto
      have "start_inc_lane (a # rects) n 0 = None"
      proof (rule ccontr)
        assume "start_inc_lane (a # rects) n 0 \<noteq> None"
        then obtain val1 val2 where **: "start_inc_lane (a # rects) n 0 = Some (val1, val2)" by auto
        with * have "start_inc_lane (a # rects) n 0 \<noteq> Some (val1, val2)" by auto
        with ** show "False" by auto        
      qed
      with cs have "None = Some ((time1, time2), rest)" by auto
      thus "False" by auto    
    qed
    then obtain num1 rest1 where "start_inc_lane (a # rects) n 0 = Some (num1, rest1)"
      by auto
    with cs have cs2: "(case finish_inc_lane rest1 n num1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2)) = Some ((time1, time2), rest)"
      by auto
    have "\<exists>num2 rest2. finish_inc_lane rest1 n num1 = Some (num2, rest2)" 
    proof (rule ccontr)
      assume " \<nexists>num2 rest2. finish_inc_lane rest1 n num1 = Some (num2, rest2) "  
      hence ***: "\<forall>num2 rest2. finish_inc_lane rest1 n num1 \<noteq> Some (num2, rest2)" by auto
      have "finish_inc_lane rest1 n num1 = None"
      proof (rule ccontr)
        assume "finish_inc_lane rest1 n num1 \<noteq> None"  
        then obtain val1 val2 where finish_some: "finish_inc_lane rest1 n num1 = Some (val1, val2)"
          by auto
        with *** have "finish_inc_lane rest1 n num1 \<noteq> Some (val1, val2)" by auto
        with finish_some show "False" by auto    
      qed
      with cs2 have "None = Some ((time1, time2), rest)" by auto  
      thus False by auto
    qed
    then obtain num2 rest2 where "finish_inc_lane rest1 n num1 = Some (num2, rest2)"by auto
    with cs2 have "time1 = num1" and "time2 = num2" by auto
    with start_inc_lane_correctness0[OF `start_inc_lane (a # rects) n 0 = Some (num1, rest1)`]
      show ?case unfolding `n = ori_lane` by auto
  qed     
next
  from assms(1) ori_lane_def rects'_def
  show "(LEAST n. time1 \<le> n \<and>
              n \<le> time1 + length rects' \<and>
              lane_detection (rects' ! (n - time1)) = Lane ori_lane \<and>
              (\<forall>m. 0 \<le> m - time1 \<and> m - time1 < n - time1 \<longrightarrow> lane_detection (rects' ! (m - time1)) = Boundaries [ori_lane])) = time2"
  proof (induction rects)
    case Nil
    then show ?case by auto
  next
    case (Cons a rects)
    note case_cons = this 
    from increase_lane_some_outbound[OF case_cons(2)] obtain n where "initial_lane (a # rects) = Lane n"
      using detection_opt.exhaust_sel by blast
    hence "initial_lane (a # rects) = Lane ori_lane" unfolding case_cons by auto  
    with `initial_lane (a # rects) = Lane n` have "n = ori_lane" using detection_opt.exhaust_sel by auto    
    from `initial_lane (a # rects) = Lane n` case_cons(2) 
      have cs: "(case start_inc_lane (a # rects) n 0 of None \<Rightarrow> None
         | Some (num1, rest1) \<Rightarrow> (case finish_inc_lane rest1 n num1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))) = Some ((time1, time2), rest)" 
      unfolding increase_lane.simps by auto
    have "\<exists> num1 rest1. start_inc_lane (a # rects) n 0 = Some (num1, rest1)"
    proof (rule ccontr)
      assume "\<nexists>num1 rest1. start_inc_lane (a # rects) n 0 = Some (num1, rest1)"
      hence *: "\<forall>num1 rest1. start_inc_lane (a # rects) n 0 \<noteq> Some (num1, rest1)" by auto
      have "start_inc_lane (a # rects) n 0 = None"
      proof (rule ccontr)
        assume "start_inc_lane (a # rects) n 0 \<noteq> None"
        then obtain val1 val2 where **: "start_inc_lane (a # rects) n 0 = Some (val1, val2)" by auto
        with * have "start_inc_lane (a # rects) n 0 \<noteq> Some (val1, val2)" by auto
        with ** show "False" by auto        
      qed
      with cs have "None = Some ((time1, time2), rest)" by auto
      thus "False" by auto    
    qed
    then obtain num1 rest1 where "start_inc_lane (a # rects) n 0 = Some (num1, rest1)"
      by auto
    with start_inc_lane_drop[OF this] have "rest1 = drop (num1) (rects)" by auto  
    from `start_inc_lane (a # rects) n 0 = Some (num1, rest1)` cs have cs2: 
      "(case finish_inc_lane rest1 n num1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2)) = Some ((time1, time2), rest)"
      by auto
    have "\<exists>num2 rest2. finish_inc_lane rest1 n num1 = Some (num2, rest2)" 
    proof (rule ccontr)
      assume " \<nexists>num2 rest2. finish_inc_lane rest1 n num1 = Some (num2, rest2) "  
      hence ***: "\<forall>num2 rest2. finish_inc_lane rest1 n num1 \<noteq> Some (num2, rest2)" by auto
      have "finish_inc_lane rest1 n num1 = None"
      proof (rule ccontr)
        assume "finish_inc_lane rest1 n num1 \<noteq> None"  
        then obtain val1 val2 where finish_some: "finish_inc_lane rest1 n num1 = Some (val1, val2)"
          by auto
        with *** have "finish_inc_lane rest1 n num1 \<noteq> Some (val1, val2)" by auto
        with finish_some show "False" by auto    
      qed
      with cs2 have "None = Some ((time1, time2), rest)" by auto  
      thus False by auto
    qed
    then obtain num2 rest2 where "finish_inc_lane rest1 n num1 = Some (num2, rest2)"by auto
    with cs2 have "time1 = num1" and "time2 = num2" by auto    
    with `rest1 = drop (num1) (rects)` case_cons(4) have "rects' = rest1" by auto        
    from finish_inc_lane_general_correctness[OF `finish_inc_lane rest1 n num1 = Some (num2, rest2)`]       
    show ?case unfolding sym[OF `time2 = num2`] sym[OF `time1 = num1`] `n = ori_lane` sym[OF `rects' = rest1`]
      by auto      
  qed    
qed
  
theorem increase_lane_decrease_length:
  assumes "increase_lane rects = Some ((t1, t2), rest)"
  shows "length rest < length rects"
proof -
  from assms have "rects \<noteq> []" by auto
  then obtain a rects' where rects: "rects = a # rects'" by (meson list.exhaust_sel)
  from increase_lane_initial_lane_obtains[OF assms] obtain n where il: "initial_lane rects = Lane n"
    by auto
  hence il2: "initial_lane (a # rects') = Lane n" unfolding `rects = a # rects'` by auto      
  from increase_lane_start_inc_lane[OF assms] have sil: "start_inc_lane (a # rects') n 0 = Some (t1, drop (t1 + 1) (a # rects'))"
    unfolding rects comp_def il2 by auto
  from assms(1) 
    have *: "(case finish_inc_lane (drop (t1 + 1) (a # rects')) n t1 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((t1, num2), rest2)) = Some ((t1, t2), rest)" 
    unfolding rects increase_lane.simps il2 using sil by auto
  hence "finish_inc_lane (drop (t1 + 1) (a # rects')) n t1 \<noteq> None" using option.distinct 
    by (metis (no_types, lifting) option.simps(4))
  then obtain num2 rest2 where **: "finish_inc_lane (drop (t1 + 1) (a # rects')) n t1 = Some (num2, rest2)"
    by auto
  with * have "num2 = t2" and "rest2 = rest" by auto 
  with finish_inc_lane_decrease_length[OF **] have "length rest < length (drop (t1 + 1) (a # rects'))"
    by auto
  also have "... \<le> length (a # rects')" by auto
  finally have "length rest < length (a # rects')" by auto    
  thus ?thesis unfolding rects by auto          
qed
  
    
text "This is the definition (or function) for (detecting) the occurrence of lane changing to the 
  right in right-hand traffic."
  
fun decrease_lane :: "rectangle list \<Rightarrow> ((nat \<times> nat) \<times> rectangle list) option" where
  "decrease_lane []    = None" |
  "decrease_lane rects = (case initial_lane rects of 
                                    Outside \<Rightarrow> None 
                                  | Boundaries _ \<Rightarrow> None 
                                  | Lane n \<Rightarrow> (case start_dec_lane rects n 0 of 
                                                 None \<Rightarrow> None 
                                               | Some (num1, rest1) \<Rightarrow> (case finish_dec_lane rest1 n num1 of 
                                                                         None \<Rightarrow> None 
                                                                       | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))))"   
  
fun decrease_lane2 :: "rectangle list \<Rightarrow> ((nat \<times> nat) \<times> rectangle list) option" where
  "decrease_lane2 [] = None" | 
  "decrease_lane2 rects = (case initial_lane rects of 
                                  Outside \<Rightarrow> None
                             |    Boundaries _ \<Rightarrow> None
                             |    Lane n \<Rightarrow> do {
                                              (num1, rest1) \<leftarrow> start_dec_lane rects n 0;
                                              (num2, rest2) \<leftarrow> finish_dec_lane rest1 n num1;
                                              Some ((num1, num2), rest2) 
                                            })"  
  
theorem 
  "decrease_lane2 rects = decrease_lane rects"
proof (induction rects)
  case Nil
  then show ?case by auto
next
  case (Cons a rects)
  note case_cons = this  
  have "\<exists>n ns. initial_lane (a # rects) = Outside \<or> initial_lane (a # rects) = Boundaries ns \<or>
               initial_lane (a # rects) = Lane n" 
  proof (induction "initial_lane (a # rects)")
    case Outside
    then show ?case by auto
  next
    case (Lane x)
    from sym[OF this] show ?case by auto
  next
    case (Boundaries x)
    from sym[OF this] show ?case by auto
  qed  
  then obtain n  ns where "initial_lane (a # rects) = Outside \<or> initial_lane (a # rects) = Boundaries ns \<or>
               initial_lane (a # rects) = Lane n" by auto     
  then consider "initial_lane (a # rects) = Outside" | "initial_lane (a # rects) = Boundaries ns" |
                "initial_lane (a # rects) = Lane n" by auto     
  then show ?case
  proof (cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    then show ?thesis by auto
  next
    case 3
    hence in0: "decrease_lane2 (a # rects) = start_dec_lane (a # rects) n 0 \<bind> (\<lambda>(num1, rest1). finish_dec_lane rest1 n num1 \<bind> (\<lambda>(num2, rest2). Some ((num1, num2), rest2)))"  
      (is "?l0 = ?r0")
      by auto
    have "\<exists> num1 rest1. start_dec_lane (a # rects) n 0 = None \<or> start_dec_lane (a # rects) n 0 = Some (num1, rest1)"
    proof (induction "start_dec_lane (a # rects) n 0")
      case None
      then show ?case by auto
    next
      case (Some option)
      from sym[OF this] show ?case by auto
    qed
    then obtain num1 rest1 where " start_dec_lane (a # rects) n 0 = None \<or> start_dec_lane (a # rects) n 0 = Some (num1, rest1)" 
      by auto   
    moreover
    { assume start_none: "start_dec_lane (a # rects) n 0 = None"
      hence "?r0 = None" by auto 
      also have "... = decrease_lane (a # rects)" unfolding decrease_lane.simps 3 using start_none
        by auto
      finally have "?l0 = decrease_lane (a # rects)" using in0 by auto }
    moreover
    { assume start_some: "start_dec_lane (a # rects) n 0 = Some (num1, rest1)"
      hence in1: "?r0 = finish_dec_lane rest1 n num1 \<bind> (\<lambda>(num2, rest2). Some ((num1, num2), rest2))"
        by auto
      have "\<exists> num2 rest2. finish_dec_lane rest1 n num1 = None \<or> finish_dec_lane rest1 n num1 = Some (num2, rest2)"
      proof (induction "finish_dec_lane rest1 n num1")
        case None
        then show ?case by auto
      next
        case (Some option)
        from sym[OF this] show ?case by auto
      qed  
      then obtain num2 rest2 where "finish_dec_lane rest1 n num1 = None \<or> finish_dec_lane rest1 n num1 = Some (num2, rest2)"
        by auto
      then consider "finish_dec_lane rest1 n num1 = None" | "finish_dec_lane rest1 n num1 = Some (num2, rest2)"
        by auto
      hence "finish_dec_lane rest1 n num1 \<bind> (\<lambda>(num2, rest2). Some ((num1, num2), rest2)) = 
              decrease_lane (a # rects)"
        by (cases) (unfold decrease_lane.simps 3, auto simp add:start_some)
      with in0 and in1 have ?thesis by auto   
    }      
    ultimately show ?thesis by auto                
  qed        
qed

theorem decrease_lane_neq: 
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  shows "rects \<noteq> []"
  using assms by auto

theorem decrease_lane_obtains:
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  obtains a rects' where "rects = a # rects'"
  using decrease_lane_neq[OF assms] by (meson list.exhaust_sel)
    
theorem decrease_lane_neq_outside_or_bound:
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  defines "il \<equiv> initial_lane rects"  
  shows "il \<noteq> Outside \<and> il \<noteq> Boundaries bs"
proof -
  from decrease_lane_obtains[OF assms(1)] obtain a rects' where "rects = a # rects'" by auto
  from assms(1) have "il \<noteq> Outside" unfolding `rects = a # rects'` decrease_lane.simps
    il_def by auto
  from assms(1) have "il \<noteq> Boundaries bs" unfolding `rects = a # rects'` decrease_lane.simps
    il_def by auto
  with `il \<noteq> Outside` show ?thesis by auto      
qed  
    
theorem decrease_lane_eq_lane:
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  defines "il \<equiv> initial_lane rects"
  shows "\<exists>i . il = Lane i"
  using assms(2) 
proof (induction il)
  case Outside
  with decrease_lane_neq_outside_or_bound[OF assms(1)]   show ?case by auto
next
  case (Lane x)
  then show ?case by (auto intro:exI[where x="x"])
next
  case (Boundaries x)
  with decrease_lane_neq_outside_or_bound[OF assms(1)]   show ?case by metis
qed    

theorem decrease_lane_eq_lane_obtains:
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  defines "il \<equiv> initial_lane rects"
  obtains i where "il = Lane i"
  using decrease_lane_eq_lane[OF assms(1)] unfolding il_def by auto
    
theorem start_dec_lane_Suc_n:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  shows "\<exists>n. ori_lane = Suc n"  
proof (rule ccontr)
  assume "\<nexists>n. ori_lane = Suc n"  
  hence "\<forall>n. ori_lane \<noteq> Suc n"  by auto
  hence "ori_lane = 0" using Zero_not_Suc  using not0_implies_Suc by blast
  hence "start_dec_lane rects ori_lane start_time = None" by auto
  with assms(1) show "False" by auto      
qed

theorem start_dec_lane_Suc_n_obtain:
  assumes "start_dec_lane rects ori_lane start_time = Some (time, rest)"
  obtains n where "ori_lane = Suc n" using start_dec_lane_Suc_n[OF assms] by auto
  
theorem decrease_lane_start_dec_lane_not_none:
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  defines "il \<equiv> initial_lane rects"
  shows "start_dec_lane rects (glane il) 0 \<noteq> None"
proof -
  from decrease_lane_eq_lane_obtains[OF assms(1)] obtain i where "il = Lane i"
    unfolding il_def by auto
  hence "glane il = i" by auto
  from decrease_lane_obtains[OF assms(1)] obtain a rects' where "rects = a # rects'" by auto    
  have "initial_lane (a # rects') = Lane i" using `il = Lane i` unfolding il_def `rects = a # rects'`
    by auto      
  from assms(1) `glane il = i` show ?thesis unfolding `rects = a # rects'` decrease_lane.simps    
    il_def `initial_lane (a # rects') = Lane i` 
    by (metis (no_types, lifting) detection_opt.case_eq_if is_Lane_def option.distinct(1) option.simps(4))      
qed      

theorem decrease_lane_start_dec_lane_some:
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  defines "il \<equiv> initial_lane rects"
  shows "\<exists>t rs. start_dec_lane rects (glane il) 0 = Some (t, rs)"
proof -
  from decrease_lane_start_dec_lane_not_none[OF assms(1)] have " start_dec_lane rects (glane (initial_lane rects)) 0 \<noteq> None"
    by auto
  thus ?thesis unfolding il_def  by auto
qed
  
theorem decrease_lane_finish_dec_lane_some:
  assumes "decrease_lane rects = Some ((time1, time2), rest)" 
  defines "il \<equiv> initial_lane rects"
  defines "res \<equiv> start_dec_lane rects (glane il) 0" 
  defines "res2 \<equiv> finish_dec_lane (snd (the res)) (glane il) (fst (the res))"    
  shows "fst (the res) = time1" and "snd (the res) = drop (time1 + 1) rects" and "fst (the res2) = time2" and "snd (the res2) = rest"
proof -
  from decrease_lane_eq_lane_obtains[OF assms(1)] obtain i where "il = Lane i"
    unfolding il_def by auto
  hence "glane il = i" by auto
  from decrease_lane_obtains[OF assms(1)] obtain a rects' where "rects = a # rects'" by auto
  have "initial_lane (a # rects') = Lane i" using `il = Lane i` unfolding il_def `rects = a # rects'`
    by auto
  from decrease_lane_start_dec_lane_some[OF assms(1)] obtain t1 rs1 where
    *: "start_dec_lane (a # rects') i 0 = Some (t1, rs1)" unfolding `rects = a # rects'` 
    `initial_lane (a # rects') = Lane i` by auto
  with assms(3) have "fst (the res) = t1" and "snd (the res) = rs1" unfolding res_def
    `rects = a # rects'` `glane il = i` by auto      
  from * assms(1) have 0: "finish_dec_lane rs1 (glane il) t1 \<noteq> None"
    unfolding `rects = a # rects'` decrease_lane.simps `initial_lane (a # rects') = Lane i`
    by (metis (no_types, lifting) \<open>glane il = i\<close> case_prod_conv decrease_lane.simps(1) 
        detection_opt.simps(10) lane.decrease_lane_neq lane_axioms option.simps(4) option.simps(5))
  from start_dec_lane_Suc_n_obtain[OF *] obtain n where "i = Suc n" by auto      
  from start_dec_lane_drop[OF * this] have "rs1 = drop (t1 + 1) rects" unfolding `rects = a # rects'`
    by auto      
  from 0 obtain t2 rs2 where **: "finish_dec_lane rs1 (glane il) t1 = Some (t2, rs2)"
    by auto    
  from assms(1) have "(case finish_dec_lane rs1 i t1 of None \<Rightarrow> None | 
      Some (num2, rest2) \<Rightarrow> Some ((t1, num2), rest2)) = Some ((time1, time2), rest)" 
     unfolding `rects = a # rects'` decrease_lane.simps
    `initial_lane (a # rects') = Lane i` using * by auto
  with ** have ***:"t1 = time1 \<and> t2 = time2 \<and> rs2 = rest" unfolding `glane il = i` by auto         
  from *** show "fst (the res) = time1" unfolding `fst (the res) = t1` by auto 
  from *** show "fst (the res2) = time2" using ** unfolding res2_def `snd (the res) = rs1` `glane il = i`
      `fst (the res) = time1`  by auto
  from *** show "snd (the res2) = rest" using ** unfolding res2_def `snd (the res) = rs1` 
      `fst (the res) = time1` by auto
  from `snd (the res) = rs1` `rs1 = drop (t1 + 1) rects` show "snd (the res) = drop (time1 + 1) rects"
    using *** by auto    
qed
  
theorem decrease_lane_correctness':  
  assumes "decrease_lane rects = Some ((t1, t2), rest)"
  defines "il \<equiv> initial_lane rects"
  defines "res \<equiv> start_dec_lane rects (glane il) 0" 
  defines "stime \<equiv> fst (the res)"
  defines "rects2 \<equiv> snd (the res)"    
  shows "(LEAST n. n \<le> length rects \<and> 
                   lane_detection (rects ! n) = Boundaries [glane il] \<and> 
                   (\<forall>m. m < n  \<longrightarrow> lane_detection (rects ! m) = Lane (glane il))) = t1" and 
         "(LEAST n. stime \<le> n \<and> n \<le> stime + length rects2 \<and> 
                   lane_detection (rects2 ! (n - stime)) = Lane (glane il - 1) \<and> 
                   (\<forall>m. 0 \<le> m - stime \<and> m - stime < n - stime \<longrightarrow> lane_detection (rects2 ! (m - stime)) = Boundaries [glane il])) = t2"  
proof -
  from decrease_lane_eq_lane_obtains[OF assms(1)] obtain i where "il = Lane i"
    unfolding il_def by auto
  hence "glane il = i" by auto  
  from decrease_lane_finish_dec_lane_some[OF assms(1)] have "fst (the res) = t1"
    unfolding res_def il_def by auto
  from decrease_lane_obtains[OF assms(1)] obtain a rects' where rects: "rects = a # rects'" by auto
  have "initial_lane (a # rects') = Lane i" using `il = Lane i` unfolding il_def `rects = a # rects'`
    by auto      
  from decrease_lane_start_dec_lane_some[OF assms(1)] obtain time1 rs1 where
    *: "start_dec_lane (a # rects') i 0 = Some (time1, rs1)" unfolding `rects = a # rects'` 
    `initial_lane (a # rects') = Lane i` by auto
  from start_dec_lane_Suc_n_obtain[OF *] obtain n where "i = Suc n" by auto      
  from start_dec_lane_correctness0[OF * `i = Suc n`] show "(LEAST n. n \<le> length rects \<and> 
                   lane_detection (rects ! n) = Boundaries [glane il] \<and> 
                   (\<forall>m. m < n  \<longrightarrow> lane_detection (rects ! m) = Lane (glane il))) = t1"
    unfolding rects `glane il = i` using `fst (the res) = t1` unfolding res_def rects `glane il = i`
    * by auto
  define res2 where "res2 \<equiv> finish_dec_lane (snd (the res)) (glane il) (fst (the res))"
  from decrease_lane_finish_dec_lane_some[OF assms(1)] have "fst (the res2) = t2" and "snd (the res2) = rest"
    unfolding res2_def res_def il_def by auto
  hence "res2 = Some (t2, rest)" 
    by (metis (mono_tags, lifting) \<open>il = Lane i\<close> assms(1) detection_opt.simps(10) glane_def il_def 
        lane.decrease_lane.simps(2) lane_axioms option.collapse option.simps(3) option.simps(4) 
        option.simps(5) prod.collapse prod.simps(2) rects res2_def res_def)      
  hence "finish_dec_lane rs1 i time1 = Some (t2, rest)" unfolding res2_def res_def
      rects `glane il = i` * by auto
  from finish_dec_lane_general_correctness[OF this `i = Suc n`] show "(LEAST n. stime \<le> n \<and> n \<le> stime + length rects2 \<and> 
                   lane_detection (rects2 ! (n - stime)) = Lane (glane il - 1) \<and> 
                   (\<forall>m. 0 \<le> m - stime \<and> m - stime < n - stime \<longrightarrow> lane_detection (rects2 ! (m - stime)) = Boundaries [glane il])) = t2"
    unfolding stime_def `fst (the res) = t1`  rects2_def res_def rects `glane il = i` * by auto      
qed  
    
theorem decrease_lane_correctness:  
  assumes "decrease_lane rects = Some ((t1, t2), rest)"    
  defines "bound_id \<equiv> glane (initial_lane rects)"  
  defines "rects2 \<equiv> drop (t1 + 1) rects"
  shows "(LEAST n. n \<le> length rects \<and> 
                   lane_detection (rects ! n) = Boundaries [bound_id] \<and> 
                   (\<forall>m. m < n  \<longrightarrow> lane_detection (rects ! m) = Lane bound_id)) = t1" and 
        "(LEAST n. t1 \<le> n \<and> n \<le> t1 + length rects2 \<and> 
                   lane_detection (rects2 ! (n - t1)) = Lane (bound_id - 1) \<and> 
                   (\<forall>m. 0 \<le> m - t1 \<and> m - t1 < n - t1 \<longrightarrow> lane_detection (rects2 ! (m - t1)) = Boundaries [bound_id])) = t2"    
proof -
  define il where "il \<equiv> initial_lane rects"
  define res where "res \<equiv> start_dec_lane rects (glane il) 0" 
  define stime where "stime \<equiv> fst (the res)"
  define rects' where "rects' \<equiv> snd (the res)"   
  note abb = il_def res_def stime_def rects'_def  
  from decrease_lane_correctness'[OF assms(1)]
  have i1: "(LEAST n. n \<le> length rects \<and> 
                   lane_detection (rects ! n) = Boundaries [glane il] \<and> 
                   (\<forall>m. m < n  \<longrightarrow> lane_detection (rects ! m) = Lane (glane il))) = t1" and 
       i2: "(LEAST n. stime \<le> n \<and> n \<le> stime + length rects' \<and> 
                   lane_detection (rects' ! (n - stime)) = Lane (glane il - 1) \<and> 
                   (\<forall>m. 0 \<le> m - stime \<and> m - stime < n - stime \<longrightarrow> lane_detection (rects' ! (m - stime)) = Boundaries [glane il])) = t2"
    unfolding abb by auto     
  from i1 show "(LEAST n. n \<le> length rects \<and> 
                   lane_detection (rects ! n) = Boundaries [bound_id] \<and> 
                   (\<forall>m. m < n  \<longrightarrow> lane_detection (rects ! m) = Lane bound_id)) = t1"
    unfolding il_def bound_id_def by auto
  from decrease_lane_finish_dec_lane_some[OF assms(1)] have "fst (the res) = t1" and 
    "snd (the res) = drop (t1 + 1) rects" unfolding res_def il_def by auto       
  hence "stime = t1" and "rects' = rects2" unfolding stime_def rects'_def rects2_def by auto
  with i2 show "(LEAST n. t1 \<le> n \<and> n \<le> t1 + length rects2 \<and> 
                   lane_detection (rects2 ! (n - t1)) = Lane (bound_id - 1) \<and> 
                   (\<forall>m. 0 \<le> m - t1 \<and> m - t1 < n - t1 \<longrightarrow> lane_detection (rects2 ! (m - t1)) = Boundaries [bound_id])) = t2"
    unfolding il_def bound_id_def by auto    
qed
  
theorem finish_dec_lane_neq0:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  shows "\<exists>n. bound_id = Suc n"
proof (rule ccontr)
  assume "\<nexists>n. bound_id = Suc n"    
  hence "\<forall>n. bound_id \<noteq> Suc n" by auto
  hence "bound_id = 0" using Zero_not_Suc  using not0_implies_Suc by blast
  with assms(1) show "False" by auto         
qed
  
theorem finish_dec_lane_neq0_obtains:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  obtains n where "bound_id = Suc n"
  using finish_dec_lane_neq0[OF assms] by auto
     
theorem finish_dec_lane_decrease_length:
  assumes "finish_dec_lane rects bound_id start_time = Some (time, rest)"
  shows "length rest < length rects"
  using assms
proof (induction rects arbitrary:start_time)
  case Nil
  from finish_dec_lane_neq0_obtains[OF assms] obtain n where "bound_id = Suc n" by auto  
  then show ?case using Nil by auto
next
  case (Cons a rects)
  note case_cons = this  
  from finish_dec_lane_neq0_obtains[OF assms] obtain n where bds: "bound_id = Suc n" by auto  
  from finish_dec_lane_case_final[OF case_cons(2) bds] have 
    "lane_detection (hd (a # rects)) = Lane (bound_id - 1) \<and> start_time = time \<and> rest = tl (a # rects) \<or>
     lane_detection (hd (a # rects)) = Boundaries [bound_id] \<and> finish_dec_lane (tl (a # rects)) bound_id (start_time + 1) = Some (time, rest) "       
    (is "?c1 \<or> ?c2")
    by auto
  moreover
  { assume "?c1"
    hence "rest = rects" by auto
    hence ?case by auto }
  moreover
  { assume "?c2"
    hence "finish_dec_lane rects bound_id (start_time + 1) = Some (time, rest)"
      by auto
    from case_cons(1)[OF this] have ?case by auto }
  ultimately show ?case by auto
qed
  
theorem decrease_lane_decrease_length:
  assumes "decrease_lane rects = Some ((t3, t4), rest)"
  shows "length rest < length rects"  
proof -
  from assms have "rects \<noteq> []" by auto
  then obtain a rects' where rects: "rects = a# rects'" by (meson list.exhaust_sel)
  from decrease_lane_eq_lane_obtains[OF assms] obtain n where il: "initial_lane (a # rects') = Lane n"
    unfolding rects by auto
  from decrease_lane_finish_dec_lane_some[OF assms] have 
    "fst (the (start_dec_lane rects (glane (initial_lane rects)) 0)) = t3" and
    "snd (the (start_dec_lane rects (glane (initial_lane rects)) 0)) = drop (t3 + 1) rects"
    unfolding rects using surjective_pairing by auto
  hence "start_dec_lane rects (glane (initial_lane rects)) 0 = Some (t3, drop (t3 + 1) rects)"
    by (metis assms decrease_lane_start_dec_lane_not_none option.collapse prod.collapse rects)    
  hence sdl: "start_dec_lane (a # rects') n 0 = Some (t3, drop (t3 + 1) (a # rects'))"
    unfolding rects il by auto
  from assms(1)
  have *: "(case finish_dec_lane (drop (t3 + 1) rects) n t3 of None \<Rightarrow> None | Some (num2, rest2) \<Rightarrow> Some ((t3, num2), rest2)) = 
            Some ((t3, t4), rest)"
    unfolding rects decrease_lane.simps il using sdl by auto
  hence "finish_dec_lane (drop (t3 + 1) (a # rects')) n t3 \<noteq> None" 
    unfolding rects using option.distinct
    by (metis (no_types, lifting) option.simps(4))
  then obtain num2 rest2 where **: "finish_dec_lane (drop (t3 + 1) (a # rects')) n t3 = Some (num2, rest2)"
    by auto
  with * have "num2 = t4" and "rest2 = rest" unfolding rects by auto
  with finish_dec_lane_decrease_length[OF **] have "length rest < length (drop (t3 + 1) (a # rects'))" 
    by auto
  also have "... \<le> length (a # rects')" by auto
  finally have "length rest < length (a # rects')" by auto
  thus ?thesis unfolding rects by auto              
qed
    
theorem increase_lane_decrease_lane_length:
  assumes "increase_lane rects = Some ((t1, t2), rest1)"
  assumes "decrease_lane rest1 = Some ((t3, t4), rest2)"
  shows "length rest2 < length rects"
proof -
  from increase_lane_decrease_length[OF assms(1)] have "length rest1 < length rects"
    by auto
  moreover
  from decrease_lane_decrease_length[OF assms(2)] have "length rest2 < length rest1"
    by auto
  ultimately show ?thesis by auto    
qed
     
function overtaking :: "rectangle list \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) list" where  
  "overtaking [] = []" | 
  "overtaking rects = (case increase_lane rects of 
                          None \<Rightarrow> [] 
                       |  Some ((t1, t2), rest1) \<Rightarrow> (case decrease_lane rest1 of 
                                                            None \<Rightarrow> overtaking rest1
                                                          | Some ((t3, t4), rest2) \<Rightarrow> (t1, t2, t3, t4) # overtaking rest2))"  
  by pat_completeness auto
  termination by (relation "Wellfounded.measure length")          
    (auto simp add:increase_lane_some_not_nil increase_lane_decrease_length 
                   increase_lane_decrease_lane_length)
    
fun time_points_to_ov_bools :: "(nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> bool list" where
  "time_points_to_ov_bools []  = []" | 
  "time_points_to_ov_bools (tp # tps) = (case tp of (t1, t2, t3, t4) \<Rightarrow> 
                                            replicate t1 False @ 
                                            replicate (t4 - t1 + 1) True @ 
                                            time_points_to_ov_bools tps)"
  
definition overtaking_trace :: "rectangle list \<Rightarrow> bool list" where
  "overtaking_trace rects = (time_points_to_ov_bools \<circ> overtaking) rects"       

\<comment> \<open>Detecting on_fast_lane which is interval @{term "{t1 ..< t2}"}\<close>    
fun time_points_to_fl_bools :: "(nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> bool list" where
  "time_points_to_fl_bools []  = []" | 
  "time_points_to_fl_bools (tp # tps) = (case tp of (t1, t2, t3, t4) \<Rightarrow> 
                                            replicate t1 False @ 
                                            replicate (t2 - t1)   True @
                                            replicate (t4 - t2 + 1) False @ 
                                            time_points_to_fl_bools tps)"

definition fast_lane_trace :: "rectangle list \<Rightarrow> bool list" where
  "fast_lane_trace rects = (time_points_to_fl_bools \<circ> overtaking) rects"  
  
text "Detecting merging which is t3 only"
  
fun time_points_to_merge_bools :: "(nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> bool list" where
  "time_points_to_merge_bools []  = []" | 
  "time_points_to_merge_bools (tp # tps) = (case tp of (t1, t2, t3, t4) \<Rightarrow> 
                                            replicate t3 False @ [True] @  
                                            replicate (t4 - t3) False @ 
                                            time_points_to_merge_bools tps)"
  
definition merging_trace :: "rectangle list \<Rightarrow> bool list" where
  "merging_trace rects = (time_points_to_merge_bools \<circ> overtaking) rects"  
  
\<comment> \<open>Detecting returning to original lane which is @{term "{t3 .. t4}"}\<close>
fun time_points_to_ori_bools :: "(nat \<times> nat \<times> nat \<times> nat) list \<Rightarrow>  bool list" where
  "time_points_to_ori_bools [] = []" | 
  "time_points_to_ori_bools (tp # tps) = (case tp of (t1, t2, t3, t4) \<Rightarrow> 
                                            replicate t3 False @   
                                            replicate (t4 - t3 + 1) True @ 
                                            time_points_to_merge_bools tps)"
  
definition original_lane_trace :: "rectangle list \<Rightarrow> bool list" where
  "original_lane_trace rects \<equiv> (time_points_to_ori_bools \<circ> overtaking) rects"
  
end
  


end
