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

theorem curve_eq_imp_closed_segment:
  "t \<in> {0..1} \<Longrightarrow> 
   \<exists>i < length points. curve_eq t \<in> closed_segment (fst (points ! i)) (snd (points ! i))"
  using curve_eq_imp_linepath[of t] atLeastAtMost_iff unfolding linepath_def closed_segment_def by blast
    
theorem linepath_imp_curve_eq: 
  "i < length points \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> 
  \<exists>t' \<in> {0..1}. curve_eq3 (points_path2 points) t' = linepath (fst (points ! i)) (snd (points ! i)) t"
  using linepath_imp_curve_eq' nonempty_points poly_points by auto

theorem closed_segment_imp_curve_eq:
  "i < length points \<Longrightarrow> \<exists>t \<in> {0..1}. curve_eq3 (points_path2 points) t \<in> closed_segment (fst (points ! i)) (snd (points ! i))"
  using linepath_imp_curve_eq[of i] unfolding linepath_def closed_segment_def by fastforce
    
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

lemma monotone_polychain_snd_fst:
  assumes "monotone_polychain xs"
  shows "i1 < length xs \<Longrightarrow> i2 < length xs \<Longrightarrow> i1 < i2 \<Longrightarrow> fst (snd (xs ! i1)) \<le> fst (fst (xs ! i2))" 
proof (induction "i2-i1" arbitrary: i1 i2)
  case 0
  then show ?case using assms by auto
next
  case (Suc x)
  {
    assume "x = 0"
    then have "i2 = Suc i1" using Suc by auto
    then have "fst (snd (xs ! i1)) = fst (fst (xs ! i2))" using Suc assms monotone_polychainD unfolding polychain_def by auto
    then have ?case by auto
  }
  moreover {
    assume "x \<noteq> 0"
    then have "fst (snd (xs ! i1)) = fst (fst (xs ! (Suc i1)))" using Suc assms monotone_polychainD unfolding polychain_def by auto
    also have "\<dots> < fst (snd (xs ! (Suc i1)))" using Suc `x \<noteq> 0` assms unfolding monotone_polychain_def by auto
    also have "fst (snd (xs ! (Suc i1))) \<le> fst (fst (xs ! i2))" using `x \<noteq> 0` Suc by auto
    finally have ?case by auto
  }
  ultimately show ?case by auto
qed
    
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
  
term "curve.setX curve_eq {0..1}" (* lsc.setX *)    
         
lemma lsc_f_of_x_curve_eq:
  assumes "x \<in> lsc.setX" \<comment> \<open>@{term "x \<in> lsc.setX"}\<close>
  assumes "lsc.f_of_x x = y"
  shows "\<exists>t\<in>{0..1}. curve_eq t = (x, y)"
  using assms lsc.f_of_x_curve_eq by auto
    
lemma test2:
  assumes "c \<in> set points"
  assumes "fst (fst c) \<le> x" and "x \<le> fst (snd c)"
  shows "x \<in> lsc.setX"
  using assms nonempty_points monotone curve_eq_is_curve
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
      unfolding e points_path2_def using curve.setX_def[OF case_cons(7)] 
      by (simp add: \<open>x \<in> fst ` linepath (fst a) (snd a) ` {0..1}\<close> e points_path2_def) }    
  
  moreover
  { assume ne: "points = a' # points'"
    with `c \<in> set (a # points)` have "c = a \<or> c \<in> set points" by auto
    moreover
    { assume "c \<in> set points"
      have curve_tail: "curve (curve_eq3 (points_path2 points)) {0..1}"  sorry
      from case_cons(1) [OF `c \<in> set points` case_cons(3) case_cons(4) _ `monotone_polychain points` curve_tail]
      have " x \<in> curve.setX (curve_eq3 (points_path2 points)) {0..1}"  unfolding ne by auto
      hence "x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}" sorry
    }
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
        unfolding ne points_path2_def sorry 
    }  
    ultimately have "x \<in> curve.setX (curve_eq3 (points_path2 (a # points))) {0..1}" by auto
  }        
  ultimately show ?case by blast
qed    
  
lemma test1:
  assumes "c \<in> set points"
  assumes "fst (fst c) \<le> x" and "x \<le> fst (snd c)"
  shows "line_equation (fst c) (snd c) x = lsc.f_of_x x"
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

(* polygonal chain intersection *)

(* checks if two line segments intersect *)
fun segments_intersect :: "(real2 \<times> real2) option \<Rightarrow> (real2 \<times> real2) option \<Rightarrow> bool" where
  "segments_intersect (Some l1) (Some l2) = segment_intersection l1 l2"
| "segments_intersect _ _ = False"
  
fun lanes_intersect' :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) option \<Rightarrow> (real2 \<times> real2) option \<Rightarrow> bool" where
  "lanes_intersect' [] [] l1 l2 \<longleftrightarrow> segments_intersect l1 l2"
| "lanes_intersect' (l # le) [] l1 l2 \<longleftrightarrow> segments_intersect l1 l2 \<or> lanes_intersect' le [] (Some l) l2"
| "lanes_intersect' [] (r # ri) l1 l2 \<longleftrightarrow> segments_intersect l1 l2 \<or> lanes_intersect' [] ri l1 (Some r)"
| "lanes_intersect' (l # le) (r # ri) l1 l2 \<longleftrightarrow> segments_intersect l1 l2 \<or> (
    if fst (fst l) \<le> fst (fst r) then lanes_intersect' le (r # ri) (Some l) l2
                                  else lanes_intersect' (l # le) ri l1 (Some r))"

(* checks if two lanes intersect *)
fun lanes_intersect :: "(real2 \<times> real2) list \<Rightarrow> (real2 \<times> real2) list \<Rightarrow> bool" where
  "lanes_intersect le ri = lanes_intersect' le ri None None"
  
lemma lanes_intersect_ri_empty: "\<not>lanes_intersect' le [] l1 None"
  by (induction le arbitrary: l1) auto

lemma lanes_intersect_le_empty: "\<not>lanes_intersect' [] ri None l2"
  by (induction ri arbitrary: l2) auto

(* we only need to check line segments that have a common x value *)
fun segments_relevant :: "(real2 \<times> real2) \<Rightarrow> (real2 \<times> real2) \<Rightarrow> bool" where
  "segments_relevant l1 l2 \<longleftrightarrow> (fst (fst l1) \<le> fst (fst l2) \<and> fst (fst l2) \<le> fst (snd l1)) \<or> (fst (fst l2) \<le> fst (fst l1) \<and> fst (fst l1) \<le> fst (snd l2))"

lemma segments_non_relevant_imp_segments_non_intersecting:
  assumes "\<not>segments_relevant l1 l2"
  assumes "fst (fst l1) < fst (snd l1)"
  assumes "fst (fst l2) < fst (snd l2)"
  shows "\<not>(\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))"
proof -
  have "fst (fst l1) > fst (fst l2) \<or> fst (fst l2) > fst (snd l1)" "fst (fst l2) > fst (fst l1) \<or> fst (fst l1) > fst (snd l2)"
    using assms by auto
  moreover {
    fix l1 l2 :: "real2 \<times> real2"
    assume *: "fst (fst l1) < fst (snd l1)" "fst (fst l2) < fst (snd l2)" "fst (fst l2) > fst (snd l1)"
    {
      fix p1 p2 :: real2
      assume p1: "p1 \<in> closed_segment (fst l1) (snd l1)"
      assume p2: "p2 \<in> closed_segment (fst l2) (snd l2)"
        
      obtain t1 where t1: "t1 \<in> {0..1}" "p1 = (1 - t1) *\<^sub>R fst l1 + t1 *\<^sub>R snd l1" using p1 unfolding closed_segment_def by auto
      obtain t2 where t2: "t2 \<in> {0..1}" "p2 = (1 - t2) *\<^sub>R fst l2 + t2 *\<^sub>R snd l2" using p2 unfolding closed_segment_def by auto
      
      have "fst p1 = fst ((1 - t1) *\<^sub>R fst l1 + t1 *\<^sub>R snd l1)" using t1 by auto
      also have "\<dots> \<le> fst (snd l1)" using t1 * by (smt atLeastAtMost_iff fst_add fst_scaleR scaleR_collapse scaleR_left_mono)
      also have "\<dots> < fst (fst l2)" using * by auto
      also have "\<dots> \<le> fst ((1 - t2) *\<^sub>R fst l2 + t2 *\<^sub>R snd l2)" using t2 * by (smt atLeastAtMost_iff fst_add fst_scaleR scaleR_collapse scaleR_left_mono)
      also have "\<dots> = fst p2" using t2 by auto
      finally have "fst p1 \<noteq> fst p2" by auto
    }
    then have "\<not>(\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst l2) (snd l2))" by auto
  }
  ultimately show ?thesis using assms by smt
qed
  
locale generalized_lanelet = le: lanelet_simple_boundary points_le + ri: lanelet_simple_boundary points_ri
  for points_le and points_ri
begin

theorem lanes_intersect'_completeness:
  "lanes_intersect' points_le points_ri l1 l2
  \<Longrightarrow> segments_intersect l1 l2
  \<or> (\<exists>i1 < length points_le. segments_intersect (Some (points_le ! i1)) l2)
  \<or> (\<exists>i2 < length points_ri. segments_intersect l1 (Some (points_ri ! i2)))
  \<or> (\<exists>i1 < length points_le. \<exists>i2 < length points_ri. segments_intersect (Some (points_le ! i1)) (Some (points_ri ! i2)))"
proof (induction points_le points_ri l1 l2 rule: lanes_intersect'.induct)
  case (1 l1 l2)
  then show ?case by auto
next
  case (2 l le l1 l2)
  then have "segments_intersect l1 l2 \<or> lanes_intersect' le [] (Some l) l2" by auto
  moreover {
    assume "lanes_intersect' le [] (Some l) l2"
    then have ?case using 2 by auto
  }
  ultimately show ?case by auto
next
  case (3 r ri l1 l2)
  then have "segments_intersect l1 l2 \<or> lanes_intersect' [] ri l1 (Some r)" by auto
  moreover {
    assume "lanes_intersect' [] ri l1 (Some r)"
    then have ?case using 3 by auto
  }
  ultimately show ?case by auto
next
  case (4 l le r ri l1 l2)
  {
    assume *: "fst (fst l) \<le> fst (fst r)"
    then have "segments_intersect l1 l2 \<or> lanes_intersect' le (r # ri) (Some l) l2"
      using 4 by auto
    moreover {
      assume "lanes_intersect' le (r # ri) (Some l) l2"
      then have "segments_intersect (Some l) l2
        \<or> (\<exists>i1 < length le. segments_intersect (Some (le ! i1)) l2)
        \<or> (\<exists>i2 < length (r # ri). segments_intersect (Some l) (Some ((r # ri) ! i2)))
        \<or> (\<exists>i1 < length le. \<exists>i2 < length (r # ri). segments_intersect (Some (le ! i1)) (Some ((r # ri) ! i2)))"
        using 4 * by auto
      moreover {
        assume "\<exists>i2<length (r # ri). segments_intersect (Some l) (Some ((r # ri) ! i2))"
        then obtain i2 where "i2 < length (r # ri)" "segments_intersect (Some l) (Some ((r # ri) ! i2))" by auto
        then have "\<exists>i1 < length (l # le). segments_intersect (Some ((l # le) ! i1)) (Some ((r # ri) ! i2))" by auto
        then have ?case using \<open>i2 < length (r # ri)\<close> by auto
      }
      moreover {
        assume "\<exists>i1<length le. \<exists>i2<length (r # ri). segments_intersect (Some (le ! i1)) (Some ((r # ri) ! i2))"
        then obtain i2 where "i2 < length (r # ri)" "\<exists>i1 < length le. segments_intersect (Some (le ! i1)) (Some ((r # ri) ! i2))"
          by auto
        then have "\<exists>i1 < length (l # le). segments_intersect (Some ((l # le) ! i1)) (Some ((r # ri) ! i2))"
          by auto
        then have ?case using \<open>i2 < length (r # ri)\<close> by auto
      }
      ultimately have ?case by auto
    }
    ultimately have ?case by auto
  }
  moreover {
    assume *: "\<not>fst (fst l) \<le> fst (fst r)"
    then have "segments_intersect l1 l2 \<or> lanes_intersect' (l # le) ri l1 (Some r)"
      using 4 by auto
    moreover {
      assume "lanes_intersect' (l # le) ri l1 (Some r)"
      then have "segments_intersect l1 (Some r)
        \<or> (\<exists>i1 < length (l # le). segments_intersect (Some ((l # le) ! i1)) (Some r))
        \<or> (\<exists>i2 < length ri. segments_intersect l1 (Some (ri ! i2)))
        \<or> (\<exists>i1 < length (l # le). \<exists>i2 < length ri. segments_intersect (Some ((l # le) ! i1)) (Some (ri ! i2)))"
        using 4 * by auto
      moreover {
        assume "\<exists>i1<length (l # le). segments_intersect (Some ((l # le) ! i1)) (Some r)"
        then obtain i1 where "i1 < length (l # le)" "segments_intersect (Some ((l # le) ! i1)) (Some r)" by auto
        then have "\<exists>i2 < length (r # ri). segments_intersect (Some ((l # le) ! i1)) (Some ((r # ri) ! i2))" by auto
        then have ?case using \<open>i1 < length (l # le)\<close> by auto
      }
      moreover {
        assume "\<exists>i1 < length (l # le). \<exists>i2 < length ri. segments_intersect (Some ((l # le) ! i1)) (Some (ri ! i2))"
        then obtain i1 where "i1 < length (l # le)" "\<exists>i2 < length ri. segments_intersect (Some ((l # le) ! i1)) (Some (ri ! i2))"
          by auto
        then have "\<exists>i2 < length (r # ri). segments_intersect (Some ((l # le) ! i1)) (Some ((r # ri) ! i2))"
          by auto
        then have ?case using \<open>i1 < length (l # le)\<close> by auto
      }
      ultimately have ?case by auto
    }
    ultimately have ?case by auto
  }
  ultimately show ?case by auto
qed

theorem lanes_non_intersecting_iff_segments_non_intersecting:
  "(\<forall>t1 \<in> {0..1}. \<forall>t2 \<in> {0..1}. le.curve_eq t1 \<noteq> ri.curve_eq t2) \<longleftrightarrow> (\<forall>i1 < length points_le. \<forall>i2 < length points_ri. \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))))"
proof -
  have "(\<exists>t1 \<in> {0..1}. \<exists>t2 \<in> {0..1}. le.curve_eq t1 = ri.curve_eq t2) \<longleftrightarrow> (\<exists>i1 < length points_le. \<exists>i2 < length points_ri. \<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))"
  proof
    assume "\<exists>t1 \<in> {0..1}. \<exists>t2 \<in> {0..1}. le.curve_eq t1 = ri.curve_eq t2"
    then obtain t1 t2 where *: "t1 \<in> {0..1}" "t2 \<in> {0..1}" "le.curve_eq t1 = ri.curve_eq t2" by auto
    have "\<exists>i1 < length points_le. le.curve_eq t1 \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1))"
      using le.curve_eq_imp_closed_segment[of t1] * by auto
    moreover have "\<exists>i2 < length points_ri. ri.curve_eq t2 \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))"
      using ri.curve_eq_imp_closed_segment[of t2] * by auto
    ultimately show "\<exists>i1 < length points_le. \<exists>i2 < length points_ri. \<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))"
      using * by metis
  next
    assume "\<exists>i1 < length points_le. \<exists>i2 < length points_ri. \<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))"
    then obtain i1 i2 p where *: "i1 < length points_le" "i2 < length points_ri" "p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))"
      by auto
    then obtain t1 t2 where **: "t1 \<in> {0..1}" "t2 \<in> {0..1}" "linepath (fst (points_le ! i1)) (snd (points_le ! i1)) t1 = linepath (fst (points_ri ! i2)) (snd (points_ri ! i2)) t2"
      unfolding closed_segment_def linepath_def by auto
    have "\<exists>t1' \<in> {0..1}. le.curve_eq t1' = linepath (fst (points_le ! i1)) (snd (points_le ! i1)) t1"
      using le.linepath_imp_curve_eq[of i1 t1] * ** by auto
    moreover have "\<exists>t2' \<in> {0..1}. ri.curve_eq t2' = linepath (fst (points_ri ! i2)) (snd (points_ri ! i2)) t2"
      using ri.linepath_imp_curve_eq[of i2 t2] * ** by auto
    ultimately show "\<exists>t1 \<in> {0..1}. \<exists>t2 \<in> {0..1}. le.curve_eq t1 = ri.curve_eq t2" using ** by metis
  qed
  then show ?thesis by auto
qed  

theorem segments_non_intersecting_iff_relevant_segments_non_intersecting:
  "(\<forall>i1 < length points_le. \<forall>i2 < length points_ri. \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))) \<longleftrightarrow>
  (\<forall>i1 < length points_le. \<forall>i2 < length points_ri. segments_relevant (points_le ! i1) (points_ri ! i2) \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))))"
proof
  assume "\<forall>i1 < length points_le. \<forall>i2 < length points_ri. segments_relevant (points_le ! i1) (points_ri ! i2) \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))"
  moreover {
    fix i1 i2
    assume *: "i1 < length points_le" "i2 < length points_ri"
    assume "segments_relevant (points_le ! i1) (points_ri ! i2) \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))"
    moreover have "\<not>segments_relevant (points_le ! i1) (points_ri ! i2) \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))"
      using * le.monotone ri.monotone segments_non_relevant_imp_segments_non_intersecting unfolding monotone_polychain_def by auto
    ultimately have "\<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))" by auto
  }
  ultimately show "\<forall>i1 < length points_le. \<forall>i2 < length points_ri. \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))" by auto
qed auto
  
theorem relevant_segments_intersecting_imp_lanes_intersect:
  "\<not>lanes_intersect' points_le points_ri l1 l2
  \<Longrightarrow> (case l1 of None \<Rightarrow> points_le = [] \<or> monotone_polychain points_le | Some l \<Rightarrow> monotone_polychain (l # points_le))
  \<Longrightarrow> (case l2 of None \<Rightarrow> points_ri = [] \<or> monotone_polychain points_ri | Some r \<Rightarrow> monotone_polychain (r # points_ri))
  \<Longrightarrow> (\<not>segments_intersect l1 l2)
    \<and> (case l1 of None \<Rightarrow> True | Some l \<Rightarrow> (\<forall>i2 < length points_ri. segments_relevant l (points_ri ! i2) \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst l) (snd l) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2)))))
    \<and> (case l2 of None \<Rightarrow> True | Some r \<Rightarrow> (\<forall>i1 < length points_le. segments_relevant (points_le ! i1) r \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst r) (snd r))))
    \<and> (\<forall>i1 < length points_le. \<forall>i2 < length points_ri. segments_relevant (points_le ! i1) (points_ri ! i2) \<longrightarrow> \<not>(\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))))"
proof (induction points_le points_ri _ _ rule: lanes_intersect'.induct)
  case (1 l1 l2)
  then show ?case by (auto simp add: option.split)
next
  case (2 l le l1' l2')
  have "monotone_polychain (l # le)"
    using 2 monotone_polychain_ConsD by (cases l1') auto
  {
    fix i1 l2
    assume *: "l2' = Some l2"
              "i1 < length (l # le)"
              "segments_relevant ((l # le) ! i1) l2"
    then have IH: "\<not>segments_intersect (Some l) (Some l2)"
                  "\<And>i1. i1 < length le \<Longrightarrow> segments_relevant (le ! i1) l2 \<Longrightarrow> (\<nexists>p. p \<in> closed_segment (fst (le ! i1)) (snd (le ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2))"
      using 2 `l2' = Some l2` `monotone_polychain (l # le)` monotone_polychain_ConsD by (auto simp add: option.split)
    {
      assume "i1 = 0"
      then have "(l # le) ! i1 = l" by auto
      then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
        using IH segment_intersection_completeness by auto
    }
    moreover {
      assume "i1 \<noteq> 0"
      then have "i1 - 1 < length le"
                "segments_relevant (le ! (i1-1)) l2"
         using * `i1 < length (l # le)` by auto
      then have "\<nexists>p. p \<in> closed_segment (fst (le ! (i1-1))) (snd (le ! (i1-1))) \<and> p \<in> closed_segment (fst l2) (snd l2)"
        using * IH by auto
      then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
        using `i1 \<noteq> 0` by auto
    }
    ultimately have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
      by blast
  }
  then show ?case using 2 by (auto simp add: option.split)
next
  case (3 r ri l1' l2')
  have "monotone_polychain (r # ri)"
    using 3 monotone_polychain_ConsD by (cases l2') auto
  moreover {
    fix i2 l1
    assume *: "l1' = Some l1"
              "i2 < length (r # ri)"
              "segments_relevant l1 ((r # ri) ! i2)"
    then have IH: "\<not>segments_intersect (Some l1) (Some r)"
                  "\<And>i2. i2 < length ri \<Longrightarrow> segments_relevant l1 (ri ! i2) \<Longrightarrow> (\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst (ri ! i2)) (snd (ri ! i2)))"
      using 3 `l1' = Some l1` `monotone_polychain (r # ri)` monotone_polychain_ConsD by (auto simp add: option.split)
    {
      assume "i2 = 0"
      then have "(r # ri) ! i2 = r" by auto
      then have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        using IH segment_intersection_completeness by auto
    }
    moreover {
      assume "i2 \<noteq> 0"
      then have "i2 - 1 < length ri"
                "segments_relevant l1 (ri ! (i2-1))"
         using * `i2 < length (r # ri)` by auto
      then have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst (ri ! (i2-1))) (snd (ri ! (i2-1)))"
        using * IH by auto
      then have"\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        using `i2 \<noteq> 0` by auto
    }
    ultimately have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
      by blast
  }
  then show ?case using 3 by (auto simp add: option.split)
next
  case (4 l le r ri l1' l2')
  have "monotone_polychain (l # le)" using 4 monotone_polychain_ConsD by (cases l1') auto
  have "monotone_polychain (r # ri)" using 4 monotone_polychain_ConsD by (cases l2') auto
  {
    fix i2 l1
    assume *: "l1' = Some l1"
              "i2 < length (r # ri)"
              "segments_relevant l1 ((r # ri) ! i2)"
    {
      assume **: "fst (fst l) \<le> fst (fst r)"
      then have "\<not>lanes_intersect' le (r # ri) (Some l) l2'" using * 4 by auto
      then have IH: "\<not>segments_intersect (Some l) l2'"
                    "\<And>i2. i2 < length (r # ri) \<Longrightarrow> segments_relevant l ((r # ri) ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst l) (snd l) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
                    "\<And>i1 i2. i1 < length le \<Longrightarrow> i2 < length (r # ri) \<Longrightarrow> segments_relevant (le ! i1) ((r # ri) ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst (le ! i1)) (snd (le ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        using * ** 4 `monotone_polychain (l # le)` monotone_polychain_ConsD by (auto simp add: option.split)
      have "monotone_polychain (l1 # l # le)" using 4 * by auto
      have "fst (fst l) < fst (snd l)" using \<open>monotone_polychain (l # le)\<close> unfolding monotone_polychain_def by auto
      have "fst (fst r) < fst (snd r)" using \<open>monotone_polychain (r # ri)\<close> unfolding monotone_polychain_def by auto
      have "fst (fst l1) < fst (snd l1)" using \<open>monotone_polychain (l1 # l # le)\<close> unfolding monotone_polychain_def by auto

      {
        assume "i2 = 0"
        then have "(r # ri) ! i2 = r" by auto
        have "fst (snd l1) = fst (fst l)" using \<open>monotone_polychain (l1 # l # le)\<close> monotone_polychainD unfolding polychain_def by fastforce
        also have "\<dots> \<le> fst (fst r)" using ** by auto
        finally have "fst (snd l1) \<le> fst (fst r)" .
        moreover {
          assume "fst (snd l1) < fst (fst r)"
          moreover have "fst (fst l1) < fst (snd l1)"
            using \<open>monotone_polychain (l1 # l # le)\<close> unfolding monotone_polychain_def by auto
          ultimately have "\<not>segments_relevant l1 ((r # ri) ! i2)" using \<open>(r # ri) ! i2 = r\<close> by auto
            then have False using * by auto
          }
        moreover {
          assume "fst (snd l1) = fst (fst r)"
          have inter_open_segments: "\<nexists>p. p \<in> open_segment (fst l1) (snd l1) \<and> p \<in> open_segment (fst r) (snd r)"
          proof -
            {
              fix p1 p2 :: real2
              assume p1: "p1 \<in> open_segment (fst l1) (snd l1)"
              assume p2: "p2 \<in> open_segment (fst r) (snd r)"
        
              obtain t1 where t1: "t1 > 0" "t1 < 1" "p1 = (1 - t1) *\<^sub>R fst l1 + t1 *\<^sub>R snd l1" using p1 in_segment(2) by blast
              obtain t2 where t2: "t2 > 0" "t2 < 1" "p2 = (1 - t2) *\<^sub>R fst r + t2 *\<^sub>R snd r" using p2 in_segment(2) by blast
      
              have "fst p1 = fst ((1 - t1) *\<^sub>R fst l1 + t1 *\<^sub>R snd l1)" using t1 by auto
              also have "\<dots> < fst (snd l1)"
              proof -
                {
                  fix t a b :: real
                  assume *: "a < b" "t > 0" "t < 1"
                  
                  have scaleR_mult_mono_strict: "\<And>(x :: real) (y :: real) (z :: real). z > 0 \<Longrightarrow> x > y \<Longrightarrow> x * z > y * z" by auto
  
                  have "(1 - t) *\<^sub>R a + t *\<^sub>R b  = a - t *\<^sub>R a + t *\<^sub>R b" using scaleR_diff_left[of 1 t a] by auto
                  also have "\<dots> = a + t *\<^sub>R (b - a)" using scaleR_diff_right[of t b a] by auto
                  also have "\<dots> < b"
                  proof -
                    have "t *\<^sub>R (b - a) < b - a" using * by auto
                    then show ?thesis by auto
                  qed
                    
                  finally have "(1 - t) *\<^sub>R a + t *\<^sub>R b < b" .
                }
                then show ?thesis using \<open>fst (fst l1) < fst (snd l1)\<close> t1 by auto
              qed
              also have "\<dots> = fst (fst r)" using \<open>fst (snd l1) = fst (fst r)\<close> .
              also have "\<dots> \<le> fst ((1 - t2) *\<^sub>R fst r + t2 *\<^sub>R snd r)"
                using t2 * \<open>fst (fst r) < fst (snd r)\<close> by (smt atLeastAtMost_iff fst_add fst_scaleR scaleR_collapse scaleR_left_mono)
              also have "\<dots> = fst p2" using t2 by auto
              finally have "fst p1 \<noteq> fst p2" by auto
            }
            then show ?thesis by auto
          qed
          moreover have inter_endpoints: "\<nexists>p. p \<in> {fst l1, snd l1} \<and> p \<in> {fst r, snd r}"
          proof -
            have "fst (fst l1) < fst (snd l1)" using \<open>monotone_polychain (l1 # l # le)\<close> unfolding monotone_polychain_def by auto
            then have "fst (fst l1) < fst (fst r)"using \<open>fst (snd l1) = fst (fst r)\<close> by auto
            moreover then have "fst (fst l1) < fst (snd r)" using \<open>monotone_polychain (r # ri)\<close> unfolding monotone_polychain_def by auto
            moreover have "snd l1 \<noteq> fst r"
            proof
              assume "snd l1 = fst r"
              then have "fst l = fst r" using \<open>monotone_polychain (l1 # l # le)\<close> monotone_polychainD unfolding polychain_def by fastforce
              then have "fst l \<in> closed_segment (fst l) (snd l) \<and> fst l \<in> closed_segment (fst r) (snd r)" using ends_in_segment by auto
              then have intersection: "\<exists>p. p \<in> closed_segment (fst l) (snd l) \<and> p \<in> closed_segment (fst r) (snd r)" by blast
              moreover then have "segments_relevant l r"
                using intersection segments_non_relevant_imp_segments_non_intersecting \<open>fst (fst l) < fst (snd l)\<close> \<open>fst (fst r) < fst (snd r)\<close> by blast
              ultimately show False using * IH(2)[of i2] \<open>(r # ri) ! i2 = r\<close> by auto
            qed
            moreover have "fst (snd l1) < fst (snd r)" using \<open>fst (snd l1) = fst (fst r)\<close> \<open>fst (fst r) < fst (snd r)\<close> by auto
            ultimately show ?thesis by auto
          qed                 
          moreover have inter_open_segment_endpoints:
            "\<nexists>p. p \<in> {fst l1, snd l1} \<and> p \<in> open_segment (fst r) (snd r)"
            "\<nexists>p. p \<in> open_segment (fst l1) (snd l1) \<and> p \<in> {fst r, snd r}"
          proof -
            {
              fix p
              assume p: "p \<in> open_segment (fst r) (snd r)"
              have "fst (snd l1) = fst (fst r)" using \<open>fst (snd l1) = fst (fst r)\<close> .
              also have "fst (fst r) < fst p"
              proof -
                obtain t where t: "0 < t" "t < 1" "p = (1 - t) *\<^sub>R (fst r) + t *\<^sub>R (snd r)"
                  using p in_segment(2) by blast
                moreover {
                  fix t a b :: real
                  assume "a < b" "t > 0" "t < 1"
                  have "(1 - t) *\<^sub>R a + t *\<^sub>R b  = a - t *\<^sub>R a + t *\<^sub>R b" using scaleR_diff_left[of 1 t a] by auto
                  also have "\<dots> = a + t *\<^sub>R (b - a)" using scaleR_diff_right[of t b a] by auto
                  also have "\<dots> > a" using \<open>a < b\<close> \<open>t > 0\<close> by auto
                  finally have "(1 - t) *\<^sub>R a + t *\<^sub>R b > a" .
                }
                ultimately show ?thesis
                  using \<open>fst (fst r) < fst (snd r)\<close> t by auto
              qed
              finally have "fst (snd l1) < fst p" .
              moreover have "fst (fst l1) < fst (snd l1)" using \<open>monotone_polychain (l1 # l # le)\<close> unfolding monotone_polychain_def by auto
              ultimately have "p \<notin> {fst l1, snd l1}" by auto
            }
            then show "\<nexists>p. p \<in> {fst l1, snd l1} \<and> p \<in> open_segment (fst r) (snd r)" by auto
          next
            {
              fix p
              assume p: "p \<in> open_segment (fst l1) (snd l1)"
              have "fst p < fst (fst r)"
              proof -
                obtain t where t: "0 < t" "t < 1" "p = (1 - t) *\<^sub>R (fst l1) + t *\<^sub>R (snd l1)"
                  using p in_segment(2) by blast
                moreover {
                  fix t a b :: real
                  assume *: "a < b" "t > 0" "t < 1"
                  
                  have scaleR_mult_mono_strict: "\<And>(x :: real) (y :: real) (z :: real). z > 0 \<Longrightarrow> x > y \<Longrightarrow> x * z > y * z" by auto

                  have "(1 - t) *\<^sub>R a + t *\<^sub>R b  = a - t *\<^sub>R a + t *\<^sub>R b" using scaleR_diff_left[of 1 t a] by auto
                  also have "\<dots> = a + t *\<^sub>R (b - a)" using scaleR_diff_right[of t b a] by auto
                  also have "\<dots> < b"
                  proof -
                    have "t *\<^sub>R (b - a) < b - a" using * by auto
                    then show ?thesis by auto
                  qed
                    
                  finally have "(1 - t) *\<^sub>R a + t *\<^sub>R b < b" .
                }
                ultimately have "fst p < fst (snd l1)" 
                  using \<open>fst (fst l1) < fst (snd l1)\<close> t by auto
                also have "\<dots> = fst (fst l)" using `fst (snd l1) = fst (fst l)` .
                finally show ?thesis using \<open>fst (snd l1) = fst (fst l)\<close> \<open>fst (fst l) \<le> fst (fst r)\<close> by auto
              qed
              moreover have "fst (fst r) < fst (snd r)" using \<open>monotone_polychain (r # ri)\<close> unfolding monotone_polychain_def by auto
              ultimately have "p \<notin> {fst r, snd r}" by auto
            }
            then show "\<nexists>p. p \<in> open_segment (fst l1) (snd l1) \<and> p \<in> {fst r, snd r}" by auto
          qed
          have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst r) (snd r)"
          proof
            assume "\<exists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst r) (snd r)"
            then obtain p where "p \<in> closed_segment (fst l1) (snd l1)" "p \<in> closed_segment (fst r) (snd r)" by auto
            then have "p \<in> open_segment (fst l1) (snd l1) \<or> p \<in> {fst l1, snd l1}"
                      "p \<in> open_segment (fst r) (snd r) \<or> p \<in> {fst r, snd r}" unfolding open_segment_def by auto
            then show False using inter_open_segments inter_endpoints inter_open_segment_endpoints by blast
          qed
        }
        ultimately have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using \<open>(r # ri) ! i2 = r\<close> by fastforce
      }
      moreover {
        assume "i2 \<noteq> 0"
        have "fst (snd l1) = fst (fst l)" using \<open>monotone_polychain (l1 # l # le)\<close> monotone_polychainD unfolding polychain_def by fastforce
        also have "\<dots> \<le> fst (fst r)" using ** by auto
        also have "\<dots> = fst (fst ((r # ri) ! 0))" by auto
        also have "\<dots> < fst (snd ((r # ri) ! 0))"
          using `monotone_polychain (r # ri)` unfolding monotone_polychain_def by auto
        also have "\<dots> \<le> fst (fst ((r # ri) ! i2))" using * `i2 \<noteq> 0` `monotone_polychain (r # ri)` monotone_polychain_snd_fst[of "r # ri" 0] by auto
        finally have "fst (snd l1) < fst (fst ((r # ri) ! i2))" .
        moreover have "fst (fst l1) < fst (snd l1)"
          using `monotone_polychain (l1 # l # le)` unfolding monotone_polychain_def by auto
        ultimately have "\<not>segments_relevant l1 ((r # ri) ! i2)" by auto
        then have False using * by auto
      }
      ultimately have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        by blast
    }
    moreover {
      assume **: "\<not>(fst (fst l) \<le> fst (fst r))"
      then have "\<not>lanes_intersect' (l # le) ri (Some l1) (Some r)" using * 4 by auto
      then have IH: "\<not> segments_intersect (Some l1) (Some r)"
                    "\<And>i2. i2 < length ri \<Longrightarrow> segments_relevant l1 (ri ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst (ri ! i2)) (snd (ri ! i2))"
        using * ** `monotone_polychain (r # ri)` 4 monotone_polychain_ConsD by (auto simp add: option.split)
      {
        assume "i2 = 0"
        then have "(r # ri) ! i2 = r" by auto
        then have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using IH segment_intersection_completeness by auto
      }
      moreover {
        assume "i2 \<noteq> 0"
        then have "i2 - 1 < length ri"
                  "segments_relevant l1 (ri ! (i2-1))"
           using * `i2 < length (r # ri)` by auto
        then have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst (ri ! (i2-1))) (snd (ri ! (i2-1)))"
          using * IH by auto
        then have"\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using `i2 \<noteq> 0` by auto
      }
      ultimately have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        by blast
    }
    ultimately have "\<nexists>p. p \<in> closed_segment (fst l1) (snd l1) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))" by auto
  }
  moreover {   
    fix i1 l2
    assume *: "l2' = Some l2"
              "i1 < length (l # le)"
              "segments_relevant ((l # le) ! i1) l2"            
    {
      assume **: "fst (fst l) \<le> fst (fst r)"
      then have "\<not>lanes_intersect' le (r # ri) (Some l) (Some l2)" using * 4 by auto
      then have IH: "\<not> segments_intersect (Some l) (Some l2)"
                    "\<And>i1. i1 < length le \<Longrightarrow> segments_relevant (le ! i1) l2 \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst (le ! i1)) (snd (le ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
        using * ** `monotone_polychain (l # le)` 4 monotone_polychain_ConsD by (auto simp add: option.split)
      {
        assume "i1 = 0"
        then have "(l # le) ! i1 = l" by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
          using IH segment_intersection_completeness by auto
      }
      moreover {
        assume "i1 \<noteq> 0"
        then have "i1 - 1 < length le"
                  "segments_relevant (le ! (i1 - 1)) l2"
           using * `i1 < length (l # le)` by auto
        then have "\<nexists>p. p \<in> closed_segment (fst (le ! (i1-1))) (snd (le ! (i1-1))) \<and> p \<in> closed_segment (fst l2) (snd l2)"
          using * IH by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
          using `i1 \<noteq> 0` by auto
      }
      ultimately have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst l2) (snd l2)"
        by blast
    }
    moreover {
      assume **: "\<not>(fst (fst l) \<le> fst (fst r))"
      then have "\<not>lanes_intersect' (l # le) ri l1' (Some r)" using * 4 by auto
      then have IH: "\<not>segments_intersect l1' (Some r)"
                    "\<And>i1. i1 < length (l # le) \<Longrightarrow> segments_relevant ((l # le) ! i1) r \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst r) (snd r)"
                    "\<And>i1 i2. i1 < length (l # le) \<Longrightarrow> i2 < length ri \<Longrightarrow> segments_relevant ((l # le) ! i1) (ri ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst (ri ! i2)) (snd (ri ! i2))"
        using * ** 4 `monotone_polychain (r # ri)` monotone_polychain_ConsD by (auto simp add: option.split)
      have "monotone_polychain (l2 # r # ri)" using 4 * by auto
      have "fst (fst l) < fst (snd l)" using \<open>monotone_polychain (l # le)\<close> unfolding monotone_polychain_def by auto
      have "fst (fst r) < fst (snd r)" using \<open>monotone_polychain (r # ri)\<close> unfolding monotone_polychain_def by auto
      have "fst (fst l2) < fst (snd l2)" using \<open>monotone_polychain (l2 # r # ri)\<close> unfolding monotone_polychain_def by auto
      {
        assume "i1 = 0"
        then have "(l # le) ! i1 = l" by auto
        have "fst (snd l2) = fst (fst r)" using \<open>monotone_polychain (l2 # r # ri)\<close> monotone_polychainD unfolding polychain_def by fastforce
        also have "\<dots> \<le> fst (fst l)" using ** by auto
        finally have "fst (snd l2) \<le> fst (fst l)" .
        moreover {
          assume "fst (snd l2) < fst (fst l)"
          moreover have "fst (fst l2) < fst (snd l2)"
            using \<open>monotone_polychain (l2 # r # ri)\<close> unfolding monotone_polychain_def by auto
          ultimately have "\<not>segments_relevant ((l # le) ! i1) l2" using \<open>(l # le) ! i1 = l\<close> by auto
            then have False using * by auto
        }
        moreover {
          assume "fst (snd l2) = fst (fst l)"
          have inter_open_segments: "\<nexists>p. p \<in> open_segment (fst l) (snd l) \<and> p \<in> open_segment (fst l2) (snd l2)"
          proof -
            {
              fix p1 p2 :: real2
              assume p1: "p1 \<in> open_segment (fst l) (snd l)"
              assume p2: "p2 \<in> open_segment (fst l2) (snd l2)"
        
              obtain t1 where t1: "t1 > 0" "t1 < 1" "p1 = (1 - t1) *\<^sub>R fst l + t1 *\<^sub>R snd l" using p1 in_segment(2) by blast
              obtain t2 where t2: "t2 > 0" "t2 < 1" "p2 = (1 - t2) *\<^sub>R fst l2 + t2 *\<^sub>R snd l2" using p2 in_segment(2) by blast
      
              have "fst p2 = fst ((1 - t2) *\<^sub>R fst l2 + t2 *\<^sub>R snd l2)" using t2 by auto
              also have "\<dots> < fst (snd l2)"
              proof -
                 {
                  fix t a b :: real
                  assume *: "a < b" "t > 0" "t < 1"
                  
                  have scaleR_mult_mono_strict: "\<And>(x :: real) (y :: real) (z :: real). z > 0 \<Longrightarrow> x > y \<Longrightarrow> x * z > y * z" by auto
  
                  have "(1 - t) *\<^sub>R a + t *\<^sub>R b  = a - t *\<^sub>R a + t *\<^sub>R b" using scaleR_diff_left[of 1 t a] by auto
                  also have "\<dots> = a + t *\<^sub>R (b - a)" using scaleR_diff_right[of t b a] by auto
                  also have "\<dots> < b"
                  proof -
                    have "t *\<^sub>R (b - a) < b - a" using * by auto
                    then show ?thesis by auto
                  qed
                    
                  finally have "(1 - t) *\<^sub>R a + t *\<^sub>R b < b" .
                }
                then show ?thesis using \<open>fst (fst l2) < fst (snd l2)\<close> t2 by auto
              qed
              also have "\<dots> = fst (fst l)" using \<open>fst (snd l2) = fst (fst l)\<close> .
              also have "\<dots> \<le> fst ((1 - t1) *\<^sub>R fst l + t1 *\<^sub>R snd l)"
                using t1 * \<open>fst (fst l) < fst (snd l)\<close> by (smt atLeastAtMost_iff fst_add fst_scaleR scaleR_collapse scaleR_left_mono)
              also have "\<dots> = fst p1" using t1 by auto
              finally have "fst p1 \<noteq> fst p2" by auto
            }
            then show ?thesis by auto
          qed
          moreover have inter_endpoints: "\<nexists>p. p \<in> {fst l, snd l} \<and> p \<in> {fst l2, snd l2}"
          proof -
            have "fst (fst l2) < fst (snd l2)" using \<open>monotone_polychain (l2 # r # ri)\<close> unfolding monotone_polychain_def by auto
            then have "fst (fst l2) < fst (fst l)"using \<open>fst (snd l2) = fst (fst l)\<close> by auto
            moreover then have "fst (fst l2) < fst (snd l)" using \<open>monotone_polychain (l # le)\<close> unfolding monotone_polychain_def by auto
            moreover have "snd l2 \<noteq> fst l"
            proof
              assume "snd l2 = fst l"
              then have "fst l = fst r" using \<open>monotone_polychain (l2 # r # ri)\<close> monotone_polychainD unfolding polychain_def by fastforce
              then have "fst l \<in> closed_segment (fst l) (snd l) \<and> fst l \<in> closed_segment (fst r) (snd r)" using ends_in_segment by auto
              then have intersection: "\<exists>p. p \<in> closed_segment (fst l) (snd l) \<and> p \<in> closed_segment (fst r) (snd r)" by blast
              moreover then have "segments_relevant l r"
                using intersection segments_non_relevant_imp_segments_non_intersecting \<open>fst (fst l) < fst (snd l)\<close> \<open>fst (fst r) < fst (snd r)\<close> by blast
              ultimately show False using * IH(2)[of i1] \<open>(l # le) ! i1 = l\<close> by auto
            qed
            moreover have "fst (snd l2) < fst (snd l)" using \<open>fst (snd l2) = fst (fst l)\<close> \<open>fst (fst l) < fst (snd l)\<close> by auto
            ultimately show ?thesis by auto
          qed                 
          moreover have inter_open_segment_endpoints:
            "\<nexists>p. p \<in> {fst l, snd l} \<and> p \<in> open_segment (fst l2) (snd l2)"
            "\<nexists>p. p \<in> open_segment (fst l) (snd l) \<and> p \<in> {fst l2, snd l2}"
          proof -
            {
              fix p
              assume p: "p \<in> open_segment (fst l2) (snd l2)"
              have "fst p < fst (fst l)"
              proof -
                obtain t where t: "0 < t" "t < 1" "p = (1 - t) *\<^sub>R (fst l2) + t *\<^sub>R (snd l2)"
                  using p in_segment(2) by blast
                moreover {
                  fix t a b :: real
                  assume *: "a < b" "t > 0" "t < 1"
                  
                  have scaleR_mult_mono_strict: "\<And>(x :: real) (y :: real) (z :: real). z > 0 \<Longrightarrow> x > y \<Longrightarrow> x * z > y * z" by auto

                  have "(1 - t) *\<^sub>R a + t *\<^sub>R b  = a - t *\<^sub>R a + t *\<^sub>R b" using scaleR_diff_left[of 1 t a] by auto
                  also have "\<dots> = a + t *\<^sub>R (b - a)" using scaleR_diff_right[of t b a] by auto
                  also have "\<dots> < b"
                  proof -
                    have "t *\<^sub>R (b - a) < b - a" using * by auto
                    then show ?thesis by auto
                  qed
                    
                  finally have "(1 - t) *\<^sub>R a + t *\<^sub>R b < b" .
                }
                ultimately have "fst p < fst (snd l2)" 
                  using \<open>fst (fst l2) < fst (snd l2)\<close> t by auto
                also have "\<dots> = fst (fst r)" using `fst (snd l2) = fst (fst r)` .
                finally show ?thesis using \<open>fst (snd l2) = fst (fst r)\<close> \<open>\<not>(fst (fst l) \<le> fst (fst r))\<close> by auto
              qed
              moreover have "fst (fst l) < fst (snd l)" using \<open>monotone_polychain (l # le)\<close> unfolding monotone_polychain_def by auto
              ultimately have "p \<notin> {fst l, snd l}" by auto
            }
            then show "\<nexists>p. p \<in> {fst l, snd l} \<and> p \<in> open_segment (fst l2) (snd l2)" by auto
          next
            {
              fix p
              assume p: "p \<in> open_segment (fst l) (snd l)"
              have "fst (snd l2) = fst (fst l)" using \<open>fst (snd l2) = fst (fst l)\<close> .
              also have "fst (fst l) < fst p"
              proof -
                obtain t where t: "0 < t" "t < 1" "p = (1 - t) *\<^sub>R (fst l) + t *\<^sub>R (snd l)"
                  using p in_segment(2) by blast
                moreover {
                  fix t a b :: real
                  assume "a < b" "t > 0" "t < 1"
                  have "(1 - t) *\<^sub>R a + t *\<^sub>R b  = a - t *\<^sub>R a + t *\<^sub>R b" using scaleR_diff_left[of 1 t a] by auto
                  also have "\<dots> = a + t *\<^sub>R (b - a)" using scaleR_diff_right[of t b a] by auto
                  also have "\<dots> > a" using \<open>a < b\<close> \<open>t > 0\<close> by auto
                  finally have "(1 - t) *\<^sub>R a + t *\<^sub>R b > a" .
                }
                ultimately show ?thesis
                  using \<open>fst (fst l) < fst (snd l)\<close> t by auto
              qed
              finally have "fst (snd l2) < fst p" .
              moreover have "fst (fst l2) < fst (snd l2)"
                using \<open>monotone_polychain (l2 # r # ri)\<close> unfolding monotone_polychain_def by auto
              ultimately have "p \<notin> {fst l2, snd l2}" by auto
            }
            then show "\<nexists>p. p \<in> open_segment (fst l) (snd l) \<and> p \<in> {fst l2, snd l2}" by auto
          qed
          have "\<nexists>p. p \<in> closed_segment (fst l2) (snd l2) \<and> p \<in> closed_segment (fst l) (snd l)"
          proof
            assume "\<exists>p. p \<in> closed_segment (fst l2) (snd l2) \<and> p \<in> closed_segment (fst l) (snd l)"
            then obtain p where "p \<in> closed_segment (fst l2) (snd l2)" "p \<in> closed_segment (fst l) (snd l)" by auto
            then have "p \<in> open_segment (fst l2) (snd l2) \<or> p \<in> {fst l2, snd l2}"
                      "p \<in> open_segment (fst l) (snd l) \<or> p \<in> {fst l, snd l}" unfolding open_segment_def by auto
            then show False using inter_open_segments inter_endpoints inter_open_segment_endpoints by blast
          qed
        }
        ultimately have "\<nexists>p. p \<in> closed_segment (fst l2) (snd l2) \<and> p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1))"
          using \<open>(l # le) ! i1 = l\<close> by fastforce
      }
      moreover {
        assume "i1 \<noteq> 0"
        have "fst (snd l2) = fst (fst r)" using \<open>monotone_polychain (l2 # r # ri)\<close> monotone_polychainD unfolding polychain_def by fastforce
        also have "\<dots> \<le> fst (fst l)" using ** by auto
        also have "\<dots> = fst (fst ((l # le) ! 0))" by auto
        also have "\<dots> < fst (snd ((l # le) ! 0))"
          using `monotone_polychain (l # le)` unfolding monotone_polychain_def by auto
        also have "\<dots> \<le> fst (fst ((l # le) ! i1))" using * `i1 \<noteq> 0` `monotone_polychain (l # le)` monotone_polychain_snd_fst[of "l # le" 0] by auto
        finally have "fst (snd l2) < fst (fst ((l # le) ! i1))" .
        moreover have "fst (fst l2) < fst (snd l2)"
          using `monotone_polychain (l2 # r # ri)` unfolding monotone_polychain_def by auto
        ultimately have "\<not>segments_relevant l2 ((l # le) ! i1)" by auto
        then have False using * by auto
      }
      ultimately have "\<nexists>p. p \<in> closed_segment (fst l2) (snd l2) \<and> p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1))"
        by blast
    }
    ultimately have "\<nexists>p. p \<in> closed_segment (fst l2) (snd l2) \<and> p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1))" by auto        
  }
  moreover {
    fix i1 i2
    assume *: "i1 < length (l # le)"
              "i2 < length (r # ri)"
              "segments_relevant ((l # le) ! i1) ((r # ri) ! i2)"
    {
      assume **: "fst (fst l) \<le> fst (fst r)"
      then have "\<not>lanes_intersect' le (r # ri) (Some l) l2'" using * 4 by auto
      then have IH: "\<not>segments_intersect (Some l) l2'"
                    "\<And>i2. i2 < length (r # ri) \<Longrightarrow> segments_relevant l ((r # ri) ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst l) (snd l) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
                    "\<And>i1 i2. i1 < length le \<Longrightarrow> i2 < length (r # ri) \<Longrightarrow> segments_relevant (le ! i1) ((r # ri) ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst (le ! i1)) (snd (le ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        using * ** 4 `monotone_polychain (l # le)` monotone_polychain_ConsD by (auto simp add: option.split)
      {
        assume "i1 = 0"
        then have "(l # le) ! i1 = l" by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using * IH by auto
      }
      moreover {
        assume "i1 \<noteq> 0"
        then have "i1 - 1 < length le"
                  "segments_relevant (le ! (i1-1)) ((r # ri) ! i2)" using * by auto
        then have "\<nexists>p. p \<in> closed_segment (fst (le ! (i1-1))) (snd (le ! (i1-1))) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using * IH by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using `i1 \<noteq> 0` by auto
      }
      ultimately have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        by blast
    }
    moreover {
      assume **: "\<not>(fst (fst l) \<le> fst (fst r))"
      then have "\<not>lanes_intersect' (l # le) ri l1' (Some r)" using * 4 by auto
      then have IH: "\<not>segments_intersect l1' (Some r)"
                    "\<And>i1. i1 < length (l # le) \<Longrightarrow> segments_relevant ((l # le) ! i1) r \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst r) (snd r)"
                    "\<And>i1 i2. i1 < length (l # le) \<Longrightarrow> i2 < length ri \<Longrightarrow> segments_relevant ((l # le) ! i1) (ri ! i2) \<Longrightarrow> \<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst (ri ! i2)) (snd (ri ! i2))"
        using * ** 4 `monotone_polychain (r # ri)`  monotone_polychain_ConsD by (auto simp add: option.split)
      {
        assume "i2 = 0"
        then have "(r # ri) ! i2 = r" by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using * IH by auto
      }
      moreover {
        assume "i2 \<noteq> 0"
        then have "i2 - 1 < length ri"
                  "segments_relevant ((l # le) ! i1) (ri ! (i2-1))" using * by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst (ri ! (i2-1))) (snd (ri ! (i2-1)))"
          using * IH by auto
        then have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
          using `i2 \<noteq> 0` by auto
      }
      ultimately have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
        by blast
    }
    ultimately have "\<nexists>p. p \<in> closed_segment (fst ((l # le) ! i1)) (snd ((l # le) ! i1)) \<and> p \<in> closed_segment (fst ((r # ri) ! i2)) (snd ((r # ri) ! i2))"
      by auto
  }
  moreover have "\<not> segments_intersect l1' l2'" using 4 by auto
  ultimately show ?case using 4
    by (smt case_optionE option.simps(4) option.simps(5))
qed
  
theorem lanes_intersect_correctness:
  assumes "\<not>lanes_intersect points_le points_ri"
  shows "\<forall>t1 \<in> {0..1}. \<forall>t2 \<in> {0..1}. le.curve_eq t1 \<noteq> ri.curve_eq t2"
  using assms le.monotone ri.monotone
    relevant_segments_intersecting_imp_lanes_intersect segments_non_intersecting_iff_relevant_segments_non_intersecting lanes_non_intersecting_iff_segments_non_intersecting
  by auto
    
theorem lanes_intersect_completeness:
  assumes "lanes_intersect points_le points_ri"
  shows "\<exists>t1 \<in> {0..1}. \<exists>t2 \<in> {0..1}. le.curve_eq t1 = ri.curve_eq t2"
proof -
  obtain i1 i2 where "i1 < length points_le" "i2 < length points_ri" "segments_intersect (Some (points_le ! i1)) (Some (points_ri ! i2))"
    using assms lanes_intersect'_completeness[of None None] by auto
  then have "\<exists>p. p \<in> closed_segment (fst (points_le ! i1)) (snd (points_le ! i1)) \<and> p \<in> closed_segment (fst (points_ri ! i2)) (snd (points_ri ! i2))"
    using segment_intersection_correctness by auto
  then show ?thesis using lanes_non_intersecting_iff_segments_non_intersecting \<open>i1 < length points_le\<close> \<open>i2 < length points_ri\<close> by auto
qed
  
theorem lanes_intersect_iff: "lanes_intersect points_le points_ri \<longleftrightarrow> (\<exists>t1 \<in> {0..1}. \<exists>t2 \<in> {0..1}. le.curve_eq t1 = ri.curve_eq t2)"
  using lanes_intersect_correctness lanes_intersect_completeness by auto

end  
  
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
  
theorem 
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
   
end
    
definition (in lanelet_simple_boundary) rectangle_intersect :: "rectangle \<Rightarrow> bool" where
  "rectangle_intersect rect \<equiv> (let lines = get_lines rect in 
                               segments_intersect_polychain (lines ! 0) points \<or> 
                               segments_intersect_polychain (lines ! 1) points \<or> 
                               segments_intersect_polychain (lines ! 2) points \<or> 
                               segments_intersect_polychain (lines ! 3) points)"  
    
subsection "Lane : composition of lanelets"

term "lanelet.rectangle_inside"  

fun it_in_lane :: "(real2 \<times> real2) list list \<Rightarrow> rectangle \<Rightarrow> nat \<Rightarrow> nat option" where
  "it_in_lane [bound1, bound2] rect num = 
          (if lanelet.rectangle_inside bound1 bound2 rect then Some num else None)" | 
  "it_in_lane (bound1 # bound2 # bounds) rect num = 
          (if lanelet.rectangle_inside bound1 bound2 rect then Some num else it_in_lane (bound2 # bounds) rect (num + 1))" |
  "it_in_lane _ rect num = None"  

fun boundaries_touched :: "(real2 \<times> real2) list list \<Rightarrow> rectangle \<Rightarrow> nat \<Rightarrow> nat list" where
  "boundaries_touched [] rect _ = []" | 
  "boundaries_touched (bound # bounds) rect num = 
    (if lanelet_simple_boundary.rectangle_intersect bound rect then num # boundaries_touched bounds rect (num + 1) 
     else boundaries_touched bounds rect (num + 1))"  
  
(* return type of lane detection *)  
datatype detection_opt = Outside | Lane nat | Boundaries "nat list"  
  
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

fun lane_boundaries_touched :: "rectangle \<Rightarrow> nat list" where
  "lane_boundaries_touched rect = boundaries_touched boundaries rect 0"  
  
fun lane_detection :: "rectangle \<Rightarrow> detection_opt" where
  "lane_detection rect = (case in_lane rect of Some x \<Rightarrow> Lane x 
                                             | None \<Rightarrow> (case lane_boundaries_touched rect of 
                                                          [] \<Rightarrow> Outside
                                                        | ns \<Rightarrow> Boundaries ns))"  

text "Finding initial position of the trace --- where trace is regarded as a series of 
   rectangles. A rectangle signify the occupancy of a vehicle."
  
fun initial_lane :: "rectangle list \<Rightarrow> detection_opt" where
  "initial_lane rects = lane_detection (hd rects)"  
  
fun start_inc_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "start_inc_lane [] ori_lane _ = None" | 
  "start_inc_lane (rect # rects) ori_lane num = (case lane_detection rect of
                                                      Outside \<Rightarrow> None 
                                                    (* If it suddenly jumps to the next lane without touching boundaries, it is not considered as part of overtaking *)
                                                    | Lane n  \<Rightarrow> (if n = ori_lane then start_inc_lane rects n (num + 1) else None) 
                                                    (* If the it touches more than one boundaries or not the specified boundary, it will not be considered as initial part of overtaking *)
                                                    | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = ori_lane + 1 then Some (num, rects) else None))"
                                                                         
fun finish_inc_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "finish_inc_lane [] _ _ = None" | 
  "finish_inc_lane (rect # rects) bound_id num = (case lane_detection rect of 
                                                       Outside \<Rightarrow> None
                                                     (* If the it touches more than one boundaries or not the specified boundary, it will not be considered as initial part of overtaking *)                                                    
                                                     | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = bound_id then finish_inc_lane rects bound_id (num + 1) else None) 
                                                     (* If it does not arrive on the lane specified, then it will not be considered as part of overtaking*)
                                                     | Lane n \<Rightarrow> (if n = bound_id then Some (num, rects) else None))" 

fun start_dec_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "start_dec_lane _ 0 _ = None" |  \<comment> \<open>cannot return to original lane if it is the the rightmost lane\<close>
  "start_dec_lane [] ori_lane _ = None" | 
  "start_dec_lane (rect # rects) ori_lane num = (case lane_detection rect of
                                                      Outside \<Rightarrow> None 
                                                    | Lane n  \<Rightarrow> (if n = ori_lane then start_dec_lane rects n (num + 1) else Some (num, rects)) 
                                                    | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = ori_lane - 1 then Some (num, rects) else None))" 
  
fun finish_dec_lane :: "rectangle list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> rectangle list) option" where
  "finish_dec_lane  _ 0 _ = None" | \<comment> \<open>cannot return to original lane if it is the the rightmost lane\<close>
  "finish_dec_lane [] _ _ = None" | 
  "finish_dec_lane (rect # rects) bound_id num = (case lane_detection rect of 
                                                       Outside \<Rightarrow> None 
                                                     | Boundaries ns \<Rightarrow> (if tl ns = [] \<and> hd ns = bound_id then finish_dec_lane rects bound_id (num + 1) else None) 
                                                     | Lane n \<Rightarrow> (if n = bound_id - 1 then Some (num, rects) else None))" 
                                                
(* TODO : Use monad syntax here *) 
  
text "This is the definition (or function) for (detecting) the occurrence of lane changing to the 
  left in right-hand traffic."
  
fun increase_lane :: "rectangle list \<Rightarrow> ((nat \<times> nat) \<times> rectangle list) option" where
  "increase_lane []    = None" |
  "increase_lane rects = (case initial_lane rects of 
                                    Outside \<Rightarrow> None 
                                  | Boundaries _ \<Rightarrow> None  (* it has to start in a lane -- not boundaries or outside *)
                                  | Lane n \<Rightarrow> (case start_inc_lane rects n 0 of 
                                                 None \<Rightarrow> None 
                                               | Some (num1, rest1) \<Rightarrow> (case finish_inc_lane rest1 (n + 1) (num1 + 1) of 
                                                                         None \<Rightarrow> None 
                                                                       | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))))"   

text "This is the definition (or function) for (detecting) the occurrence of lane changing to the 
  right in right-hand traffic."
  
fun decrease_lane :: "rectangle list \<Rightarrow> ((nat \<times> nat) \<times> rectangle list) option" where
  "decrease_lane []    = None" |
  "decrease_lane rects = (case initial_lane rects of 
                                    Outside \<Rightarrow> None 
                                  | Boundaries _ \<Rightarrow> None 
                                  | Lane n \<Rightarrow> (case start_dec_lane rects n 0 of 
                                                 None \<Rightarrow> None 
                                               | Some (num1, rest1) \<Rightarrow> (case finish_dec_lane rest1 n (num1 + 1) of 
                                                                         None \<Rightarrow> None 
                                                                       | Some (num2, rest2) \<Rightarrow> Some ((num1, num2), rest2))))"   
  
fun overtaking :: "rectangle list \<Rightarrow> (nat \<times> nat) list" where  
  "overtaking [] = []" | 
  "overtaking rects = (case increase_lane rects of 
                          None \<Rightarrow> [] 
                       |  Some ((start1, end1), rest1) \<Rightarrow> (case decrease_lane rest1 of 
                                                            None \<Rightarrow> overtaking (tl rects)
                                                          | Some ((start2, end2), _) \<Rightarrow> (start1, end2) # overtaking (tl rects)))"  


  
end
  


end
