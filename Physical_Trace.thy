theory Physical_Trace
  imports Complex_Main Analysis
  Overtaking_Aux
  "$AFP/Affine_Arithmetic/Affine_Arithmetic"         
begin
  
section "Auxiliaries"
  
subsection "singleton"

lemma two_elements_not_singleton:
  "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> is_singleton S"
  by (metis is_singleton_def singletonD)  
 
subsection "Strict monotonicity  and anti-monotonicity"

definition strict_mono_in :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strict_mono_in f S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x < y \<longrightarrow> f x < f y)"
  
lemma strict_mono_inI[intro]:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x < y \<Longrightarrow> f x < f y"
  shows "strict_mono_in f S"  
  using assms unfolding strict_mono_in_def by auto
    
lemma strict_mono_inD:
  assumes "strict_mono_in f S"
  assumes "x \<in> S"
  assumes "y \<in> S"
  assumes "x < y"
  shows "f x < f y"
  using assms unfolding strict_mono_in_def by auto    
  
definition mono_in :: "('a :: order \<Rightarrow> 'b :: order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mono_in f S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x \<le> y \<longrightarrow> f x \<le> f y)" 

lemma mono_inI[intro]:
  fixes S :: "('a :: order) set"
  fixes f :: "'a  \<Rightarrow> 'b :: order"  
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "mono_in f S"    
  using assms unfolding mono_in_def by auto
      
lemma strict_mono_in_mono_in: 
  "strict_mono_in f S \<Longrightarrow> mono_in f S"
  unfolding strict_mono_in_def mono_in_def by (simp add: le_less)
    
lemma strict_imp_inj_on:
  fixes S :: "'a ::linorder set"
  assumes "strict_mono_in f S"
  shows "inj_on f S"
  unfolding inj_on_def
proof (rule ballI, rule ballI, rule impI, rule ccontr)
  fix x y
  assume "x \<in> S"
  assume "y \<in> S"
  assume "f x = f y"
  assume "x \<noteq> y"
  then consider "x < y" | "x > y" using less_linear by auto
  hence  "f x \<noteq> f y"
  proof (cases)
    case 1
    hence "f x < f y" using strict_mono_inD[OF assms \<open>x \<in> S\<close> \<open>y \<in> S\<close>] by auto 
    then show ?thesis by auto
  next
    case 2
    hence "f y < f x" using strict_mono_inD[OF assms \<open>y \<in>S\<close> \<open>x \<in> S\<close>] by auto
    then show ?thesis by auto
  qed
  with \<open>f x = f y\<close> show "False" by auto  
qed
  
  
definition strict_antimono_in :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strict_antimono_in f S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x < y \<longrightarrow> f x > f y)"
  
definition antimono_in :: "('a :: order \<Rightarrow> 'b :: order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "antimono_in f S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x \<le> y \<longrightarrow> f x \<ge> f y)"

lemma strict_antimono_in_antimono_in:
  "strict_antimono_in f S \<Longrightarrow> antimono_in f S"
  unfolding strict_antimono_in_def antimono_in_def by (simp add:le_less)  

    
\<comment> \<open>A function @{term "f"} is always strictly antimonotonic in a set with single element.\<close>  
lemma "strict_antimono_in f {x}"
  unfolding strict_antimono_in_def by auto
   
subsection "Non-boundedness"
  
lemma bounded_lt: "\<not> bounded {..< (u::real)}"  
proof (rule notI, cases "0 \<le> u")
  case True
  assume "bounded {..<u}"   
  then obtain a where 0:"\<forall>x \<in> {..<u}. \<bar>x\<bar> \<le> a" unfolding bounded_real by auto          
  have 1:"0 < a"
  proof -
    have f1: "(0 \<le> - 1 + a) = (1 \<le> a)"
      by auto
    have f2: "\<not> (0::real) \<le> - 1"
      by auto
    have f3: "\<forall>r. r \<in> {..<u} \<longrightarrow> (if r < 0 then - r else r) \<le> a"
      by (metis \<open>\<forall>x\<in>{..<u}. \<bar>x\<bar> \<le> a\<close> abs_if_raw)
  have f4: "\<forall>r. (r \<in> {..<u} \<longrightarrow> (if r < 0 then - r else r) \<le> a) = (r \<notin> {..<u} \<or> (if r < 0 then - 1 * r else r) \<le> a)"
    by auto
  have "\<forall>r. (if (r::real) < 0 then - 1 * r else r) = (if 0 \<le> r then r else - 1 * r)"
    by simp
    then have f5: "\<forall>r. r \<notin> {..<u} \<or> 0 \<le> a + - 1 * (if 0 \<le> r then r else - 1 * r)"
      using f4 f3 by fastforce
    have f6: "\<forall>x0. a + (if 0 \<le> x0 then - 1 * x0 else x0) = (if 0 \<le> x0 then - 1 * x0 + a else x0 + a)"
      by fastforce
    have f7: "\<forall>x0. - (1::real) * (if 0 \<le> x0 then x0 else - 1 * x0) = (if 0 \<le> x0 then - 1 * x0 else x0)"
      by simp
    have "- 1 \<in> {..<u}"
      using \<open>0 \<le> u\<close> by auto
    then have "1 \<le> a"
    using f7 f6 f5 f2 f1 by presburger
      then show ?thesis
        by auto
    qed    
  with True have "-(a+1) \<in> {..<u}" by auto
  with 0 have "abs (-(a+1)) \<le> a" by auto
  thus "False" by auto       
next
  case False
  assume "bounded {..<u}"
  then obtain a where 0:"\<forall>x \<in> {..<u}. abs x \<le> a" unfolding bounded_real by auto
  have "0 \<le> a" 
  proof (rule ccontr)    
    assume "\<not> 0 \<le> a"
    hence "a < 0" by auto
    with 0 have "\<forall>x \<in> {..<u}. abs x < 0" by auto
    with abs_ge_zero have "\<forall>x \<in> {..<u}. abs x < 0 \<and> 0 \<le> abs x" by auto            
    hence "\<forall>x \<in> {..<u}. False" by auto
    hence "{..<u} = {}" by (simp add: lessThan_def)
    with lessThan_non_empty[of "u"] show "False" by auto        
  qed
  hence "- (a + 1) < 0" by auto    
  have "-a < u"
  proof (rule ccontr)    
    assume "\<not> -a < u"
    hence "-a \<ge> u" by auto
    have "u - 1 < u" by auto
    with 0 have "abs (u - 1) \<le> a" by auto
    with False have "1 - u \<le> a" by auto
    hence "1 - a \<le> u" by auto
    with \<open>-a \<ge> u\<close> show "False" by auto           
  qed  
  hence "- (a + 1) < u" by auto
  with 0 have "abs (- (a + 1)) \<le> a" by auto
  with \<open>- (a + 1) < 0\<close> have "a + 1 \<le> a" by auto            
  then show "False" by auto
qed  
  
lemma bounded_leq: "\<not> bounded {..(u::real)}"  
proof -
  have "{..<u} \<subseteq> {..u}" by auto
  with bounded_subset[where S="{..<u}" and T="{..u}"] and bounded_lt
    show "\<not> bounded {..u}" by auto      
qed
    
lemma bounded_gt: "\<not> bounded {(l::real)<..}"    
  unfolding bounded_real      
proof (rule notI)
  assume "\<exists>a . \<forall>x \<in> {l<..}. abs x \<le> a"  
  then obtain a where 0: "\<forall>x \<in> {l<..}. abs x \<le> a" by auto
  hence "l < a" by (rule ballE[where x="l+1"])(auto)  
  hence 1: "l < a + 1" by auto
  have "0 \<le> a"
  proof (rule ccontr)
    assume "\<not> 0 \<le> a"
    hence "a < 0" by auto
    with 0 have "\<forall>x \<in> {l <..}. abs x < 0" by auto
    with abs_ge_zero have "\<forall>x \<in> {l <..}. False" by auto
    hence "{l<..} = {}" by blast
    with greaterThan_non_empty show "False" by auto      
  qed      
  from 0 and 1 have 2: "abs (a + 1) \<le> a" by auto        
  with \<open>0 \<le> a\<close> show "False" by auto      
qed  
  
lemma bounded_geq: "\<not> bounded {(l::real)..}"
proof -
  have "{l<..} \<subseteq> {l..}" by auto
  with bounded_subset[where S="{l<..}" and T="{l..}"] and bounded_gt
    show "\<not> bounded {l..}" by auto
  qed
    
subsection "Non-closedness"
  
lemma closedness_gt_lt:"(l :: real) < u \<Longrightarrow> \<not> closed {l <..< u}"  
  unfolding closed_limpt
  by (auto intro!:islimpt_greaterThanLessThan2)    
        
lemma islimpt_gt_leq: 
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "a islimpt {a<..b}"
  using assms islimpt_greaterThanLessThan1
  by (metis islimpt_Un ivl_disj_un_singleton(4))
        
lemma closedness_gt: "(l ::real) < u \<Longrightarrow> \<not> closed {l <.. u}"
  unfolding closed_limpt
  using islimpt_gt_leq greaterThanAtMost_iff by blast  
  
lemma islimpt_geq_lt: 
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "b islimpt {a..<b}"
  using assms islimpt_greaterThanLessThan2
  by (metis atLeastLessThan_iff greaterThanLessThan_iff islimptE islimptI less_imp_le)    
        
lemma closedness_lt: "(l::real) < u \<Longrightarrow> \<not> closed {l..<u}"
  unfolding closed_limpt
  using islimpt_geq_lt atLeastLessThan_iff by blast
  
theorem compact_convex_closed_interval:
  fixes domain :: "real set"
  assumes compact: "compact domain"
  assumes convex: "convex domain"
  obtains a b where "domain = {a .. b}"    
proof -
  from convex have 0: "is_interval domain" by (auto simp add:is_interval_convex_1)
  obtain l u where
    "domain = {} \<or> domain = UNIV \<or> domain = {..<u} \<or> domain = {..u} \<or> domain = {l<..} \<or> domain = {l..} \<or> 
     domain = {l<..<u} \<or> domain = {l<..u} \<or> domain = {l..<u} \<or> domain = {l..u}"
    using is_real_interval[OF 0] by auto
  moreover have "\<not> bounded (UNIV :: real set)" and "\<not> bounded {..<u}" and "\<not> bounded {..u}"
    and "\<not> bounded {l<..}" and "\<not> bounded {l..}"
    by (auto simp add: bounded_lt bounded_leq bounded_gt bounded_geq)
  moreover have "l < u \<Longrightarrow> \<not> closed {l<..<u}" and "l < u \<Longrightarrow> \<not> closed {l<..u}" and
                "l < u \<Longrightarrow> \<not> closed {l..<u}"
    by (auto simp add:closedness_gt_lt closedness_gt closedness_lt)
  ultimately have "domain = {} \<or> domain = {l .. u}"  using compact greaterThanLessThan_empty_iff 
    greaterThanAtMost_empty_iff  atLeastLessThan_empty_iff unfolding compact_eq_bounded_closed  
    by smt
  thus ?thesis 
    by (smt atLeastatMost_empty bot_set_def that)
qed  
             
section "Trace"    
\<comment> \<open>Represent the state of a (dynamic) road user as a record.\<close>

datatype vehicle = Pedestrian | Cyclist | Motorised

record raw_state = rectangle +
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
type_synonym black_boxes = "runs list"  
  
section "Environment"

text "At the moment, we focus on highway (freeway) scenario first without forks and joints. There 
are multiple lanes in one road. The road is characterised with left boundary, right boundary, and
lane boundaries. Left, right, and lane boundaries are formalised as curve in mathematical sense."
  
\<comment> \<open>A general definition of plane curve; a curve is define by a parametric function — or map in 
mathematics parlance. The only requirement is that the function must be continuous; this ensures
that the function is defined everywhere (no hole).\<close>
      
subsection "Curve"
  
locale curve =
  fixes curve_eq :: "real \<Rightarrow> real2"
  fixes domain :: "real set"
  assumes convex_domain: "convex domain"
  assumes compact_domain: "compact domain"
  assumes continuous: "continuous_on domain curve_eq"
begin
      
\<comment> \<open>convexity of the domain means that domain is an interval\<close>    
lemma "is_interval domain"
  using convex_domain by (auto simp add: is_interval_convex_1)

\<comment> \<open>in fact, it is a closed interval\<close>
lemma closed_domain:
  "closed domain" 
  using compact_domain by (auto intro:compact_imp_closed) 
    
\<comment> \<open>the domain is path connected too\<close>
lemma path_connected_domain: "path_connected domain"
  using convex_domain by (auto intro:convex_imp_path_connected)
    
lemma bdd_below_domain: 
  "bdd_below domain"
  using compact_domain unfolding compact_eq_bounded_closed
  using bounded_imp_bdd_below by auto
    
lemma bdd_above_domain:
  "bdd_above domain"
  using compact_domain unfolding compact_eq_bounded_closed
  using bounded_imp_bdd_above by auto
  
definition setX where
  "setX \<equiv> fst ` (curve_eq ` domain)"
  
definition setY where
  "setY \<equiv> snd ` (curve_eq ` domain)"
    
\<comment> \<open>parametric equation for x only.\<close>  
definition curve_eq_x :: "real \<Rightarrow> real" where
  "curve_eq_x \<equiv> \<lambda>s. fst (curve_eq s)"
  
lemma setX_alt_def: "setX = curve_eq_x ` domain"
  unfolding setX_def curve_eq_x_def by auto  
  
lemma cont_param_x: "continuous_on domain curve_eq_x"
  unfolding curve_eq_x_def by (auto intro: continuous_on_fst simp add:continuous)

lemma compact_setX: "compact setX"    
  unfolding setX_alt_def
  by (rule compact_continuous_image)(auto simp add: compact_domain  cont_param_x)
    
lemma path_connected_setX: "path_connected setX"
  unfolding setX_alt_def
  by (rule path_connected_continuous_image) (auto simp add: cont_param_x path_connected_domain)

lemma interval_setX: "is_interval setX"
  unfolding is_interval_path_connected_1
  using path_connected_setX by auto
    
lemma convex_setX: "convex setX"    
  using is_interval_convex_1 interval_setX by auto
     
theorem setX_closed_interval_or_empty:
  "(\<exists> a b. setX = {a .. b})" 
  using compact_convex_closed_interval[OF compact_setX convex_setX] 
  by meson
      
corollary closed_setX: "closed setX"
  using setX_closed_interval_or_empty closed_atLeastAtMost closed_empty
  by auto
      
\<comment> \<open>parametric equation for y only.\<close>
definition curve_eq_y :: "real \<Rightarrow> real" where
  "curve_eq_y \<equiv> \<lambda>s. snd (curve_eq s)"
 
lemma setY_alt_def: "setY = curve_eq_y ` domain"
  unfolding setY_def curve_eq_y_def by auto

lemma cont_param_y: "continuous_on domain curve_eq_y"
  unfolding curve_eq_y_def by (auto intro:continuous_on_snd simp add:continuous)  

lemma "compact setY"
  unfolding setY_alt_def
  by (rule compact_continuous_image) (auto simp add:compact_domain cont_param_y)  

lemma path_connected_setY: "path_connected setY"
  unfolding setY_alt_def
  by (rule path_connected_continuous_image) (auto simp add: cont_param_y path_connected_domain) 

lemma "is_interval setY"
  unfolding is_interval_path_connected_1
  using path_connected_setY by auto    
    
theorem domain_interval: 
  "\<exists> a b. domain = {a .. b}"    
  using compact_convex_closed_interval[OF compact_domain convex_domain] by meson    
end  
  
subsection "Simple boundary"
  
\<comment> \<open>A simple boundary in traffic scenario is a simple curve. That is the parametric function for the
curve is injective (or one-to-one). This ensures that the curve will have no common point. This is 
adequate to model highway without forks and joins.\<close>
  
locale simple_boundary = curve +
  assumes simple: "inj_on curve_eq domain"
  assumes bij_betw: "bij_betw curve_eq_x domain setX"
begin
      
lemma curve_eq_x_strict_mono_or_antimono:
  assumes "domain \<noteq> {}"
  shows "strict_mono_in curve_eq_x domain \<or> strict_antimono_in curve_eq_x domain"
proof -
  from domain_interval obtain a b where 0: "domain = {a .. b}" by auto  
  with assms have "a \<le> b" by auto    
  from continuous_inj_imp_mono[where f="curve_eq_x" and a="a" and b="b"] cont_param_x bij_betw
  have 1: "\<forall>x. a < x \<longrightarrow> x < b \<longrightarrow> curve_eq_x a < curve_eq_x x \<and> curve_eq_x x < curve_eq_x b \<or> 
                                   curve_eq_x b < curve_eq_x x \<and> curve_eq_x x < curve_eq_x a" 
    unfolding bij_betw_def 0 strict_mono_def strict_antimono_in_def strict_mono_in_def by auto
  show ?thesis
  proof (cases "\<forall>x. a < x \<longrightarrow> x < b \<longrightarrow> curve_eq_x a < curve_eq_x x \<and> curve_eq_x x < curve_eq_x b")
    case True
    have "strict_mono_in curve_eq_x {a .. b}" 
      unfolding strict_mono_in_def  
    proof (rule ballI, rule ballI, rule impI, rule ccontr)
      fix x y
      assume "x \<in> {a .. b}" "y \<in> {a .. b}"
      hence "a \<le> x" by auto
      assume "x < y"
      assume "\<not> curve_eq_x x < curve_eq_x y"
      hence 2:"curve_eq_x y \<le> curve_eq_x x" by auto
      have 3: "curve_eq_x a \<le> curve_eq_x y"        
      proof (cases "y \<noteq> b")
        assume "y \<noteq> b"
        with \<open>y \<in> {a .. b}\<close> have "y \<in> {a ..< b}" by auto
        with True show ?thesis  by force                   
      next
        case False
        hence "y = b" by auto
        show ?thesis                            
        proof (cases "a = b")
          case True
          then show ?thesis using \<open>y = b\<close> by auto
        next
          case False
          with \<open>a \<le> b\<close> have "a < b" by auto
          then obtain c where "a < c \<and> c < b" using dense[OF \<open>a < b\<close>] by auto
          with True have "curve_eq_x a < curve_eq_x c \<and> curve_eq_x c < curve_eq_x b" by auto
          thus ?thesis using \<open>y=b\<close> by auto                            
        qed          
      qed        
      have ax_subset: "{a .. x} \<subseteq> {a .. b}"
        using \<open>x \<in> {a .. b}\<close> by auto        
      have 4: "continuous_on {a..x} curve_eq_x" 
        using continuous_on_subset[OF cont_param_x] ax_subset unfolding 0 by auto                 
      hence "\<exists>z\<ge>a. z \<le> x \<and> curve_eq_x z = curve_eq_x y"
        using IVT'[of "curve_eq_x" "a" "curve_eq_x y" "x", OF 3 2 \<open>a \<le> x\<close> 4] 
        by auto
      from this obtain z where 5: "curve_eq_x z = curve_eq_x y" and "z \<in> {a .. x}"  by auto          
      with \<open>x < y\<close> have 6: "z \<noteq> y" by auto  
      from \<open>z \<in> {a .. x}\<close> have "z \<in> {a .. b}" using ax_subset by auto    
      with bij_betw 5 6 show "False" unfolding bij_betw_def 0 inj_on_def using \<open>y \<in> {a .. b}\<close>
        by auto
    qed
    from this show ?thesis using 0 by auto                       
  next
    case False
    with 1 have 2: "\<forall>x. a < x \<longrightarrow> x < b \<longrightarrow> curve_eq_x b < curve_eq_x x \<and> curve_eq_x x < curve_eq_x a"
      by smt
    have "strict_antimono_in curve_eq_x {a .. b}"
      unfolding strict_antimono_in_def
    proof (rule ballI, rule ballI, rule impI, rule ccontr)
      fix x y
      assume "x \<in> {a .. b}" "y \<in> {a .. b}"
      hence "a \<le> x" by auto
      assume "x < y"
      assume "\<not> curve_eq_x y < curve_eq_x x"
      hence 3: "curve_eq_x x \<le> curve_eq_x y" by auto
          
      have 4: "curve_eq_x y \<le> curve_eq_x a"
      proof (cases "y \<noteq> b")
        case True
        with \<open>y \<in> {a .. b}\<close> have "y \<in> {a ..< b}" by auto
        with 2 show ?thesis by force
      next
        case False
        hence "y = b" by auto
        show ?thesis
        proof (cases "a = b")
          case True
          then show ?thesis using \<open>y = b\<close> by auto
        next
          case False
          with \<open>a \<le> b\<close> have "a < b" by auto
          then obtain c where "a < c \<and> c < b" using dense[OF \<open>a < b\<close>] by auto
          with 2 have "curve_eq_x b < curve_eq_x c \<and> curve_eq_x c < curve_eq_x a" by auto
          thus ?thesis using \<open>y=b\<close> by auto                            
        qed  
      qed
      have ax_subset: "{a .. x} \<subseteq> {a .. b}"
        using \<open>x \<in> {a .. b}\<close> by auto        
      have 5: "continuous_on {a..x} curve_eq_x" 
        using continuous_on_subset[OF cont_param_x] ax_subset unfolding 0 by auto          
      have "\<exists>z\<ge> a. z \<le> x \<and> curve_eq_x z = curve_eq_x y"
        using IVT2'[of "curve_eq_x" "x" "curve_eq_x y" "a", OF 3 4 \<open>a \<le> x\<close> 5] .
      then obtain z where "a \<le> z" and "z \<le> x" and "curve_eq_x z = curve_eq_x y" by auto
      with bij_betw show "False" unfolding bij_betw_def 0 inj_on_def using ax_subset \<open>y \<in> {a .. b}\<close>  
        by (smt \<open>x < y\<close> atLeastAtMost_iff)          
    qed        
    then show ?thesis unfolding 0 ..
  qed
qed
    
lemma checking_strict_mono: 
  assumes "domain \<noteq> {}"
  assumes "curve_eq_x (Inf domain) < curve_eq_x (Sup domain)"
  shows "strict_mono_in curve_eq_x domain"
proof (rule ccontr) 
  assume "\<not> strict_mono_in curve_eq_x domain"
  with curve_eq_x_strict_mono_or_antimono[OF assms(1)] have anti: "strict_antimono_in curve_eq_x domain"
    by auto
  have "is_singleton domain \<or> \<not> is_singleton domain" by auto
  moreover      
  { assume "is_singleton domain"
    then obtain x where "domain = {x}" unfolding is_singleton_def by auto
    hence "Inf domain = Sup domain" by auto        
    hence "curve_eq_x (Inf domain) = curve_eq_x (Sup domain)" by auto   
    with assms(2) have "False" by auto }
  moreover    
  { assume "\<not> is_singleton domain"
    with assms(1) obtain a b where domain_eq: "domain = {a .. b}" and "a < b" using domain_interval by force
    hence inf_id: "Inf domain = a" and sup_id: "Sup domain = b" by auto
    from anti have "curve_eq_x a > curve_eq_x b"  unfolding strict_antimono_in_def
      using domain_eq  \<open>a < b\<close> by auto
    with assms(2) have "False" using inf_id sup_id by auto }    
  ultimately show False by blast      
qed
  
lemma checking_strict_antimono:
  assumes "domain \<noteq> {}"
  assumes "curve_eq_x (Inf domain) > curve_eq_x (Sup domain)"
  shows "strict_antimono_in curve_eq_x domain"
  using assms(2)
proof (rule contrapos_pp)
  assume "\<not> strict_antimono_in curve_eq_x domain"
  with curve_eq_x_strict_mono_or_antimono[OF assms(1)] have mono: "strict_mono_in curve_eq_x domain"
    by auto
  have "Inf domain \<le> Sup domain" using cInf_le_cSup[OF assms(1) bdd_above_domain bdd_below_domain] .     
  hence "curve_eq_x (Inf domain) \<le> curve_eq_x (Sup domain)"
    using strict_mono_in_mono_in[OF mono] closed_contains_Inf[OF assms(1) bdd_below_domain closed_domain] 
    closed_contains_Sup[OF assms(1) bdd_above_domain closed_domain] unfolding mono_in_def
    by auto
  thus "\<not> curve_eq_x (Sup domain) < curve_eq_x (Inf domain)" by auto
qed
  
lemma impossible_equal_endpoints_value:
  assumes "domain \<noteq> {}" and "\<not> is_singleton domain"
  shows "curve_eq_x (Inf domain) \<noteq> curve_eq_x (Sup domain)"
proof -
  from assms obtain a b where domain_eq: "domain = {a .. b}" and "a < b" using domain_interval by force
  hence "Inf domain = a" and "Sup domain = b" by auto
  with \<open>a < b\<close> bij_betw show ?thesis unfolding bij_betw_def domain_eq inj_on_def
    by (smt atLeastAtMost_iff)
qed        
      
definition inv_curve_x where
  "inv_curve_x \<equiv> the_inv_into domain curve_eq_x" 
  
lemma "bij_betw inv_curve_x setX domain"  
  using bij_betw_the_inv_into[OF bij_betw] unfolding inv_curve_x_def by auto
        
lemma strict_mono_inverse:
  assumes "strict_mono_in curve_eq_x domain"
  shows "strict_mono_in inv_curve_x setX"
  using assms 
  by (smt bij_betw bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw inv_curve_x_def 
                                                                                 strict_mono_in_def)    
    
lemma strict_antimono_inverse:
  assumes "strict_antimono_in curve_eq_x domain"
  shows "strict_antimono_in inv_curve_x setX"
  unfolding strict_antimono_in_def
proof (rule ballI, rule ballI, rule impI)
  fix x y
  assume "x \<in> setX" "y \<in> setX" "x < y"
  from this obtain dx dy :: real where "dx = inv_curve_x x" and "dx \<in> domain" and 
                                       "dy = inv_curve_x y" and "dy \<in> domain"
    by (metis bij_betw bij_betw_imp_inj_on image_eqI inv_curve_x_def setX_alt_def the_inv_into_onto)
  hence 0: "curve_eq_x dx = x" and 1: "curve_eq_x dy = y" using f_the_inv_into_f_bij_betw[OF bij_betw] 
    bij_betw \<open>x \<in> setX\<close> \<open>y \<in> setX\<close> unfolding inv_curve_x_def by auto        
  have "antimono_in curve_eq_x domain" using strict_antimono_in_antimono_in[OF assms] .   
  hence "dx > dy" unfolding antimono_in_def using \<open>dx \<in> domain\<close> \<open>dy \<in> domain\<close> 0 1 \<open>x < y\<close>
      by fastforce
  thus " inv_curve_x y < inv_curve_x x" using \<open>dx = inv_curve_x x\<close> \<open>dy = inv_curve_x y\<close> by simp 
qed    
           
lemma image_inverse: 
  "inv_curve_x ` setX \<subseteq> domain"  
  using bij_betw unfolding bij_betw_def inv_curve_x_def
  using the_inv_into_onto by fastforce 

\<comment> \<open>the inverse of parametric curve for x dimension is also continuous\<close>
lemma inv_x_cont: "continuous_on setX inv_curve_x"
  using bij_betw
  unfolding inv_curve_x_def setX_alt_def  bij_betw_def
  by (auto intro!: continuous_on_inv_into simp add:cont_param_x compact_domain ) 
       
definition f_of_x where
  "f_of_x \<equiv> curve_eq_y \<circ> inv_curve_x"
      
theorem domain_and_range_f_of_x: "f_of_x \<in> setX \<rightarrow> setY"
proof (rule funcsetI)
  fix x
  assume 0: "x \<in> setX"
  hence "f_of_x x = (curve_eq_y (inv_curve_x x))" unfolding f_of_x_def by auto
  also have 1: "... = (curve_eq_y (THE y. y \<in> domain \<and> curve_eq_x y = x))" unfolding inv_curve_x_def
      the_inv_into_def by auto
  also have "... \<in> setY" unfolding setY_def using curve_eq_y_def inv_curve_x_def 0 1
    by (metis (no_types, lifting)  bij_betw bij_betwE bij_betw_the_inv_into image_eqI)
  finally show "f_of_x x \<in> setY" by auto      
qed  

theorem f_of_x_curve_eq:
  assumes "x \<in> setX"
  assumes "f_of_x x = y"
  shows "\<exists>t \<in> domain. curve_eq t = (x,y)"  
proof -
  from \<open>x \<in> setX\<close> obtain t where "t \<in> domain \<and> (fst \<circ> curve_eq) t = x"
    unfolding setX_def comp_def by auto
  from assms have "y \<in> setY" using domain_and_range_f_of_x by auto
  from assms(2) have "(snd \<circ> curve_eq) t = y" unfolding f_of_x_def 
    by (metis \<open>t \<in> domain \<and> (fst \<circ> curve_eq) t = x\<close> bij_betw bij_betw_imp_inj_on comp_def 
                  curve.curve_eq_y_def curve_axioms curve_eq_x_def inv_curve_x_def the_inv_into_f_f)
  with \<open>t \<in> domain \<and> (fst \<circ> curve_eq) t = x\<close> show ?thesis by(auto intro:bexI[where x="t"])                
qed  
  
theorem cont_f_of_x: "continuous_on setX f_of_x"
  unfolding f_of_x_def
proof (rule continuous_on_compose)
  from inv_x_cont show " continuous_on setX inv_curve_x" by auto
next
  have "inv_curve_x ` setX = domain" unfolding inv_curve_x_def
    by (metis bij_betw bij_betw_imp_inj_on setX_alt_def the_inv_into_onto)
  thus "continuous_on (inv_curve_x ` setX) curve_eq_y" using cont_param_y by auto
qed    
  
lemma param_y_via_f_of_x:
  assumes "d \<in> domain"
  shows "curve_eq_y d = (f_of_x \<circ> curve_eq_x) d"
  unfolding f_of_x_def comp_def  using the_inv_into_f_f[of "curve_eq_x" "domain" "d"]
  using assms bij_betw unfolding bij_betw_def inv_curve_x_def 
  by auto        
end
  
subsection "Simple road"   
  
\<comment> \<open>The locale for defining a simple road which consists of single lane only. This locale is 
parametrised further with two simple boundaries, for left and right boundary.\<close>

(*
          ------------------------------    left boundary
          
              DRIVABLE AREA 
              
          ------------------------------    right boundary
    y
    |
    |
    -----> x (global coordinate)
*)

(* TODO: add @{term"common_setX \<noteq> {}"} as one of the assumption in the locale. It simplifies 
  the theorem inside. *)

locale simple_road =  le: simple_boundary curve_left domain +  ri: simple_boundary curve_right domain 
  for curve_left and curve_right and domain +
  assumes nonempty: "le.setX \<inter> ri.setX \<noteq> {}"
  assumes above': "x \<in> le.setX \<inter> ri.setX \<Longrightarrow> ri.f_of_x x \<noteq> le.f_of_x x"
begin
    
definition common_setX where
  "common_setX \<equiv> le.setX \<inter> ri.setX"  
      
lemma inverse_image_common_left: 
  "le.inv_curve_x ` common_setX \<subseteq> domain"
  using le.image_inverse  by (simp add: subset_eq common_setX_def)  

lemma inverse_image_common_right:
  "ri.inv_curve_x ` common_setX \<subseteq> domain"
  using ri.image_inverse by (simp add:subset_eq common_setX_def)
    
definition between_setY where
  "between_setY x \<equiv> {min (ri.f_of_x x) (le.f_of_x x) <..< max (ri.f_of_x x) (le.f_of_x x)}"
  
lemma convex_common_setX: "convex (common_setX)"
  using le.convex_setX  ri.convex_setX convex_Int common_setX_def by auto

lemma compact_common_setX: "compact (common_setX)"
  using le.compact_setX ri.compact_setX le.closed_setX compact_Int common_setX_def
  by auto
    
theorem common_setX_interval: 
  "\<exists> a b. common_setX = {a .. b}"    
  using compact_convex_closed_interval[OF compact_common_setX convex_common_setX] by meson
 
lemma bdd_below_common: 
  "bdd_below common_setX"
  using compact_common_setX unfolding compact_eq_bounded_closed
  using bounded_imp_bdd_below by auto
    
lemma bdd_above_common:
  "bdd_above common_setX"
  using compact_common_setX unfolding compact_eq_bounded_closed
  using bounded_imp_bdd_above by auto
    
\<comment> \<open>lower bound and upper bound of @{term "common_setX"}.\<close>    
definition lb_x where
  "lb_x \<equiv> Inf common_setX"
        
lemma common_contains_lb: 
  "lb_x \<in> common_setX"
  using compact_common_setX bdd_below_common  closed_contains_Inf nonempty
  unfolding lb_x_def compact_eq_bounded_closed common_setX_def
  by meson  
            
definition ub_x where
  "ub_x \<equiv> Sup common_setX"
  
lemma common_contains_ub: 
  "ub_x \<in> common_setX"  
  using compact_common_setX bdd_above_common closed_contains_Sup nonempty
  unfolding ub_x_def compact_eq_bounded_closed common_setX_def
  by meson  
        
theorem common_setX_interval2:
  "common_setX = {lb_x .. ub_x}"
  unfolding common_setX_def
  using common_setX_interval lb_x_def nonempty ub_x_def 
  by (metis atLeastatMost_empty' cInf_atLeastAtMost cSup_atLeastAtMost common_setX_def)
    
lemma lb_x_leq_ub_x:
  "lb_x \<le> ub_x"
  unfolding lb_x_def ub_x_def using common_setX_def bdd_below_common bdd_above_common
  by (auto intro!: cInf_le_cSup simp add: common_setX_def nonempty)
          
lemma common_setX_closed_segment:
  "common_setX = closed_segment lb_x ub_x"
  using lb_x_leq_ub_x common_setX_interval2 closed_segment_real by auto

abbreviation open_common_setX where
  "open_common_setX \<equiv> common_setX - {lb_x, ub_x}"
    
lemma open_common_setX_open_segment:
  "open_common_setX = open_segment lb_x ub_x"
  unfolding open_segment_def using common_setX_closed_segment by auto
      
lemma lb_x_extreme_point:
  "lb_x extreme_point_of common_setX" 
  unfolding common_setX_closed_segment
  using extreme_point_of_segment by auto

lemma ub_x_extreme_point:
  "ub_x extreme_point_of common_setX"
  unfolding common_setX_closed_segment
  using extreme_point_of_segment by auto
        
lemma convex_open_common_setX: "convex (open_common_setX)"
  using lb_x_extreme_point ub_x_extreme_point extreme_point_of_stillconvex convex_common_setX
  common_contains_ub common_contains_lb 
  by (simp add: open_common_setX_open_segment)
    
definition direction_right :: bool where
  "direction_right \<equiv> ri.f_of_x lb_x < le.f_of_x lb_x"  
    
definition direction_left :: bool where
  "direction_left \<equiv> ri.f_of_x lb_x > le.f_of_x lb_x"  
  
theorem direction_right_neq_left[simp]:
  "\<not> direction_left \<longleftrightarrow> direction_right"
  unfolding direction_right_def direction_left_def using above' common_contains_lb common_setX_def
  by fastforce
    
lemma direction_right_cond:
  assumes "direction_right"
  shows "\<forall>x \<in> common_setX. ri.f_of_x x < le.f_of_x x"
proof (rule ccontr)
  assume "\<not> (\<forall>x \<in> common_setX. ri.f_of_x x < le.f_of_x x)"
  from this obtain x where "x \<in> common_setX" and "le.f_of_x x \<le> ri.f_of_x x" by fastforce
  from \<open>x \<in> common_setX\<close> have "lb_x \<le> x" and "x \<le> ub_x" using common_setX_interval2 by auto
  define f where "f \<equiv> \<lambda>x. ri.f_of_x x - le.f_of_x x" 
  from assms have 0: "f lb_x \<le> 0" unfolding f_def direction_right_def by auto
  from \<open>le.f_of_x x \<le> ri.f_of_x x\<close> have 1: "f x \<ge> 0" unfolding f_def by auto
  from le.cont_f_of_x and ri.cont_f_of_x have "continuous_on common_setX le.f_of_x" and 
    "continuous_on common_setX ri.f_of_x" by (auto intro:continuous_on_subset simp add:common_setX_def)    
  hence cont: "continuous_on common_setX f" unfolding f_def by (auto intro:continuous_on_diff)
  from \<open>lb_x \<le> x\<close> and \<open>x \<le> ub_x\<close> have "{lb_x .. x} \<subseteq> common_setX" using common_setX_interval2
    by auto
  with cont have 2: "continuous_on {lb_x .. x} f" by (auto intro:continuous_on_subset)      
  from IVT'[where f="f" and a="lb_x" and y="0" and b="x", OF 0 1 \<open>lb_x \<le> x\<close> 2] obtain x' where
    "lb_x \<le> x'" and "x' \<le> x" and "f x' = 0" by blast   
  hence "x' \<in> common_setX" using \<open>x \<le> ub_x\<close> and common_setX_interval2 by auto
  with \<open>f x' = 0\<close> and above' show "False" unfolding f_def common_setX_def by auto    
qed
  
lemma direction_left_cond:
  assumes "direction_left"
  shows "\<forall>x \<in> common_setX. ri.f_of_x x > le.f_of_x x"
proof (rule ccontr)
  assume "\<not> (\<forall>x \<in> common_setX. ri.f_of_x x > le.f_of_x x)"
  from this obtain x where "x \<in> common_setX" and "le.f_of_x x \<ge> ri.f_of_x x" by fastforce
  from \<open>x \<in> common_setX\<close> have "lb_x \<le> x" and "x \<le> ub_x" using common_setX_interval2 by auto
  define f where "f \<equiv> \<lambda>x. le.f_of_x x - ri.f_of_x x" 
  from assms have 0: "f lb_x \<le> 0" unfolding f_def direction_left_def by auto
  from \<open>le.f_of_x x \<ge> ri.f_of_x x\<close> have 1: "f x \<ge> 0" unfolding f_def by auto
  from le.cont_f_of_x and ri.cont_f_of_x have "continuous_on common_setX le.f_of_x" and 
    "continuous_on common_setX ri.f_of_x" by (auto intro:continuous_on_subset simp add:common_setX_def)    
  hence cont: "continuous_on common_setX f" unfolding f_def by (auto intro:continuous_on_diff)
  from \<open>lb_x \<le> x\<close> and \<open>x \<le> ub_x\<close> have "{lb_x .. x} \<subseteq> common_setX" using common_setX_interval2
    by auto
  with cont have 2: "continuous_on {lb_x .. x} f" by (auto intro:continuous_on_subset)      
  from IVT'[where f="f" and a="lb_x" and y="0" and b="x", OF 0 1 \<open>lb_x \<le> x\<close> 2] obtain x' where
    "lb_x \<le> x'" and "x' \<le> x" and "f x' = 0" by blast   
  hence "x' \<in> common_setX" using \<open>x \<le> ub_x\<close> and common_setX_interval2 by auto
  with \<open>f x' = 0\<close> and above' show "False" unfolding f_def using common_setX_def by fastforce    
qed

theorem between_setY_right_def:
  assumes "direction_right"
  assumes "x \<in> common_setX"
  shows "between_setY x = {ri.f_of_x x <..< le.f_of_x x}"
  using assms unfolding between_setY_def using direction_right_cond[OF assms(1)]  by force  

theorem between_setY_left_def:
  assumes "direction_left"
  assumes "x \<in> common_setX"
  shows "between_setY x = {le.f_of_x x <..< ri.f_of_x x}"
  using assms unfolding between_setY_def using direction_left_cond above' by force
        
lemma between_setY_nonempty: "x \<in> common_setX \<Longrightarrow> between_setY x \<noteq> {}"
proof (cases direction_right)
  case True
  assume "x \<in> common_setX"
  with direction_right_cond[OF True] have "ri.f_of_x x < le.f_of_x x" by auto    
  from Rats_dense_in_real[OF this] obtain r where "r \<in> between_setY x" 
    unfolding between_setY_right_def[OF True \<open>x \<in> common_setX\<close>]
    using greaterThanLessThan_iff by blast      
  thus "between_setY x \<noteq> {}" using ex_in_conv 
    unfolding between_setY_right_def[OF True \<open>x \<in> common_setX\<close>] by auto    
next
  case False
  hence "direction_left" using direction_right_neq_left  by blast  
  assume "x \<in> common_setX"
  with direction_left_cond[OF \<open>direction_left\<close>] have "ri.f_of_x x > le.f_of_x x" by auto    
  from Rats_dense_in_real[OF this] obtain r where "r \<in> between_setY x" 
    unfolding between_setY_left_def[OF \<open>direction_left\<close> \<open>x \<in> common_setX\<close>]
    using greaterThanLessThan_iff by blast     
  thus "between_setY x \<noteq> {}" using ex_in_conv 
    unfolding between_setY_left_def[OF \<open>direction_left\<close> \<open>x \<in> common_setX\<close>] by auto    
qed  
  
lemma between_setY_nonempty': "x \<in> open_common_setX \<Longrightarrow> between_setY x \<noteq> {}"
  using between_setY_nonempty by auto
        
definition drivable_area :: "real2 set" where
  "drivable_area \<equiv> {(x,y). x \<in> open_common_setX \<and> y \<in> between_setY x}"  
  
lemma drivable_areaI:
  assumes "x \<in> open_common_setX"
  assumes "y \<in> between_setY x"
  shows "(x,y) \<in> drivable_area"
using assms unfolding drivable_area_def by auto
      
lemma drivable_areaD1: "z \<in> drivable_area \<Longrightarrow> fst z \<in> common_setX"
  by (auto simp add:drivable_area_def)
    
lemma drivable_areaD1' : "z \<in> drivable_area \<Longrightarrow> fst z \<in> open_common_setX"
  by (auto simp add:drivable_area_def)
    
lemma drivable_areaD2: "z \<in> drivable_area \<Longrightarrow> snd z \<in> between_setY (fst z)"
  by (auto simp add:drivable_area_def)
       
lemma drivable_area_alt_def: 
  "drivable_area = Sigma open_common_setX between_setY"
proof (unfold set_eq_subset, rule conjI, rule_tac [!] subsetI)  
  fix x
  assume "x \<in> drivable_area"
  hence 0: "fst x \<in> open_common_setX \<and> snd x \<in> between_setY (fst x)"
    unfolding drivable_area_def by auto
  have "(fst x, snd x) \<in> Sigma open_common_setX between_setY"    
    apply (rule SigmaI)  using 0 by auto
  thus "x \<in> Sigma open_common_setX between_setY"
    using surjective_pairing by auto 
next
  fix x
  assume 1: "x \<in> Sigma open_common_setX between_setY"
  show "x \<in> drivable_area"
  proof (rule SigmaE2[of "fst x" "snd x" "open_common_setX" "between_setY"])    
    from 1 show "(fst x, snd x) \<in> Sigma open_common_setX between_setY"
      using surjective_pairing by auto
  next
    assume "fst x \<in> open_common_setX" and "snd x \<in> between_setY (fst x)"
    thus "x \<in> drivable_area" unfolding drivable_area_def by auto
  qed
qed  
    
theorem drivable_area_nonempty: "open_common_setX \<noteq> {} \<Longrightarrow> drivable_area \<noteq> {}"  
  unfolding drivable_area_alt_def common_setX_def
  using Sigma_empty_iff between_setY_nonempty' common_setX_def
  by fastforce
      
lemma fst_path_image:
  assumes "fst z1 = fst z2"
  defines "g \<equiv> linepath z1 z2"
  shows "fst ` (path_image g) = {fst z2}"
proof -
  from assms have "\<forall>t \<in> {0 .. 1} . fst (g t) = fst z2"
    unfolding linepath_def by auto
  thus ?thesis unfolding path_image_def
    by (simp add: assms linepath_image_01)        
qed  
    
lemma snd_path_image:
  fixes z1 z2 :: real2
  assumes "fst z1 = fst z2"
  defines "g \<equiv> linepath z1 z2"
  defines "lb \<equiv> min (snd z1) (snd z2)"
  defines "ub \<equiv> max (snd z1) (snd z2)"
  shows "snd ` (path_image g) \<subseteq> {lb .. ub}"    
proof -
  have "path_image g = (closed_segment z1 z2)" and "path_image g = closed_segment z2 z1"
    unfolding path_image_def g_def using linepath_image_01[of "z1" "z2"] by auto
  hence "\<And>x y. (x, y) \<in> path_image g \<Longrightarrow> y \<in> closed_segment (snd z1) (snd z2) \<and> 
                                          y \<in> closed_segment (snd z2) (snd z1)"
    using closed_segment_PairD surjective_pairing by metis      
  hence "snd ` (path_image g) \<subseteq> closed_segment (snd z1) (snd z2)" and
        "snd ` (path_image g) \<subseteq> closed_segment (snd z2) (snd z1)" by auto
  thus ?thesis using closed_segment_eq_real_ivl assms(2) 
    unfolding lb_def ub_def  by smt 
qed  
  
lemma snd_path_image':
  fixes z1 z2 :: real2
  assumes "fst z1 = fst z2"
  assumes "z1 \<in> drivable_area" and "z2 \<in> drivable_area"
  defines "g \<equiv> linepath z1 z2"
  defines "lb \<equiv> min (snd z1) (snd z2)"
  defines "ub \<equiv> max (snd z1) (snd z2)"    
  shows "snd ` (path_image g) \<subseteq> between_setY (fst z2)"
proof (cases "direction_right")
  case True
  from snd_path_image have "snd ` (path_image g) \<subseteq> {lb .. ub}"
    using assms by auto
  moreover from assms(2-3) have "ri.f_of_x (fst z1) < snd z1" and "snd z2 < le.f_of_x (fst z2)"
    unfolding drivable_area_def using between_setY_right_def[OF True] by auto
  moreover from assms(2-3) have "ri.f_of_x (fst z2) < snd z2" and "snd z1 < le.f_of_x (fst z1)"
    unfolding drivable_area_def using between_setY_right_def[OF True] by auto
  ultimately show ?thesis using assms(1) between_setY_right_def[OF True] unfolding lb_def ub_def     
    by (smt assms(3) atLeastAtMost_iff drivable_areaD1 greaterThanLessThan_iff subset_eq)
next
  case False
  from snd_path_image have "snd ` (path_image g) \<subseteq> {lb .. ub}"
    using assms by auto
  moreover from assms(2-3) have "ri.f_of_x (fst z1) > snd z1" 
    unfolding drivable_area_def using between_setY_left_def False by fastforce 
  moreover from assms(2-3) have "snd z2 > le.f_of_x (fst z2)" 
    unfolding drivable_area_def using between_setY_left_def False by fastforce       
  moreover from assms(2-3) have "ri.f_of_x (fst z2) > snd z2" 
    unfolding drivable_area_def using between_setY_left_def False by fastforce
  moreover from assms(2-3) have "snd z1 > le.f_of_x (fst z1)" 
    unfolding drivable_area_def using between_setY_left_def False by fastforce       
  ultimately show ?thesis using assms(1) between_setY_left_def False unfolding lb_def ub_def     
      by (smt assms(3) atLeastAtMost_iff direction_right_neq_left drivable_areaD1 greaterThanLessThan_iff subset_eq)
qed
    
definition midcurve_points :: "real2 set" where
  "midcurve_points \<equiv> {(x,y) . x \<in> open_common_setX \<and> y = (le.f_of_x x + ri.f_of_x x) / 2}"
  
lemma midcurve_pointsI:
  assumes "x \<in> open_common_setX"
  assumes "y =(le.f_of_x x + ri.f_of_x x) * inverse 2 "
  shows "(x, y) \<in> midcurve_points"
  unfolding midcurve_points_def using assms by auto    
  
lemma midcurve_points_inside_drivable_area: 
  "midcurve_points \<subseteq> drivable_area"
proof (rule subsetI, rename_tac "z")
  fix z :: real2
  assume 0: "z \<in> midcurve_points"
  from this obtain x y where 1: "z = (x,y)" by fastforce
  with 0 have 2: "x \<in> open_common_setX \<and> y = (le.f_of_x x + ri.f_of_x x) / 2" 
    unfolding midcurve_points_def by auto
  hence "y \<in> between_setY x"
    using simple_road.between_setY_nonempty simple_road_axioms  between_setY_left_def 
    between_setY_right_def direction_right_neq_left by fastforce
  with 2 have "z \<in> Sigma open_common_setX between_setY" using 1 by auto
  thus "z \<in> drivable_area" using drivable_area_alt_def by auto      
qed

definition midcurve_fun :: "real \<Rightarrow> real" where
  "midcurve_fun x = (le.f_of_x x + ri.f_of_x x) * inverse 2"  
  
lemma midcurve_fun_midcurve_points:
  "x \<in> open_common_setX \<Longrightarrow> (x, midcurve_fun x) \<in> midcurve_points"
  using mem_Collect_eq midcurve_fun_def midcurve_points_def by auto

lemma midcurve_fun_inside_drivable_area:
  "x \<in> open_common_setX \<Longrightarrow> (x, midcurve_fun x) \<in> drivable_area"
  using midcurve_fun_midcurve_points midcurve_points_inside_drivable_area
  by auto
          
\<comment> \<open>Use @{term "linepath"} instead.\<close>    
definition rep_mid :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "rep_mid start end \<equiv> (\<lambda>s. start + (end - start) * s)"
        
(* TODO: combine these two lemmas to make it more general! *)  
lemma image_rep_mid:
  assumes "start \<le> end"
  shows "(rep_mid start end) ` {0 .. 1} = {start .. end}"      
proof -
  have "(rep_mid start end) ` {0 .. 1} = closed_segment start end"
    unfolding rep_mid_def closed_segment_real_eq by auto
  thus ?thesis unfolding closed_segment_eq_real_ivl using assms by auto
qed      

lemma image_rep_mid2:
  assumes "end \<le> start"
  shows "(rep_mid start end) ` {0 .. 1} = {end .. start}"      
proof -
  have "(rep_mid start end) ` {0 .. 1} = closed_segment start end"
    unfolding rep_mid_def closed_segment_real_eq by auto
  thus ?thesis unfolding closed_segment_eq_real_ivl using assms by auto
qed      
        
definition mid_path where
  "mid_path start end \<equiv> (\<lambda>s. (rep_mid start end s, midcurve_fun (rep_mid start end s)))"
        
lemma continuous_midcurve:
  assumes "start \<in> common_setX" and "end \<in> common_setX"
  shows "continuous_on {start .. end} midcurve_fun"
  unfolding midcurve_fun_def 
(* TODO: the proof for the two subgoals have the same structure. Generalise!*)
proof (rule continuous_on_mult_right, rule continuous_on_add)
  from convex_common_setX have "{start .. end} \<subseteq> common_setX"
    by (metis assms atLeastAtMost_iff atLeastatMost_subset_iff common_setX_interval)
  thus "continuous_on {start .. end} le.f_of_x"
    using le.cont_f_of_x assms continuous_on_subset common_setX_def by auto
next
  from convex_common_setX have "{start .. end} \<subseteq> common_setX"
    by (metis assms atLeastAtMost_iff atLeastatMost_subset_iff common_setX_interval)
  thus "continuous_on {start .. end} ri.f_of_x"
    using ri.cont_f_of_x assms continuous_on_subset common_setX_def by auto
qed  

lemma path_mid_path:
  assumes "start \<in> common_setX" and "end \<in> common_setX"
  shows "path (mid_path start end)"
  unfolding path_def mid_path_def  
proof (rule continuous_on_Pair)
  show "continuous_on {0..1} (rep_mid start end)"
    unfolding rep_mid_def by (auto intro!:continuous_intros)
next
  have "continuous_on {0..1} (midcurve_fun \<circ> rep_mid start end)"
  proof (rule continuous_on_compose)
    show "continuous_on {0 .. 1} (rep_mid start end)" unfolding rep_mid_def 
      by (auto intro!:continuous_intros)
  next
    show "continuous_on (rep_mid start end ` {0 .. 1}) midcurve_fun"
    proof (cases "start \<le> end")
      case True
      then show ?thesis unfolding image_rep_mid[OF True] using continuous_midcurve[OF assms] by auto          
    next
      case False
      hence 0: "end \<le> start" by auto
      then show ?thesis unfolding image_rep_mid2[OF 0] using continuous_midcurve[OF assms(2) assms(1)]
        by auto          
    qed  
  qed
  thus " continuous_on {0..1} (\<lambda>x. midcurve_fun (rep_mid start end x))" unfolding comp_def .    
qed
          
lemma pathstart_mid_path:
  fixes left_x right_x :: real
  assumes "left_x \<in> common_setX" and "right_x \<in> common_setX"
  shows "pathstart (mid_path left_x right_x) = (left_x, midcurve_fun left_x)"
  using assms  unfolding pathstart_def mid_path_def rep_mid_def by auto 
              
lemma pathfinish_mid_path:
  fixes left_x right_x :: real
  assumes "left_x \<in> common_setX" and "right_x \<in> common_setX"
  shows "pathfinish (mid_path left_x right_x) = (right_x, midcurve_fun right_x)"
  using assms  unfolding pathfinish_def mid_path_def rep_mid_def by auto

lemma rep_mid_in_common_setX:
  assumes "s \<in> {0 .. 1}"
  assumes "start \<in> open_common_setX" and "end \<in> open_common_setX"      
  shows "rep_mid start end s \<in> open_common_setX"    
proof (cases "start \<le> end")
  case True
  hence "rep_mid start end ` {0 .. 1} = {start .. end}"
    using image_rep_mid[OF True] by auto
  also have "... \<subseteq> open_common_setX" using convex_open_common_setX assms(2 - 3)   
  by (metis True closed_segment_eq_real_ivl convex_contains_segment)      
  finally show "rep_mid start end s \<in> open_common_setX" using assms(1) by blast      
next
  case False
  hence False2: "end \<le> start" by auto
  hence "rep_mid start end ` {0 .. 1} = {end .. start}" 
    using image_rep_mid2[OF False2] by auto
  also have "... \<subseteq> open_common_setX" using convex_open_common_setX assms(2 - 3)
    by (metis False closed_segment_eq_real_ivl convex_contains_segment)      
  finally show "rep_mid start end s \<in> open_common_setX" using assms(1) by blast     
qed
  
lemma mid_path_in_midcurve_points:
  assumes "s \<in> {0 .. 1}"
  assumes "start \<in> open_common_setX" and "end \<in> open_common_setX"  
  shows "mid_path start end s \<in> midcurve_points"
  unfolding mid_path_def midcurve_fun_def using rep_mid_in_common_setX assms    
  by (auto intro: midcurve_pointsI) 
     
lemma mid_path_in_midcurve_points2:
  assumes "x1 \<in> open_common_setX" and "x2 \<in> open_common_setX"
  shows "mid_path x1 x2 ` {0 .. 1} \<subseteq> midcurve_points"
  using assms mid_path_in_midcurve_points
  unfolding mid_path_def by auto
    
lemma path_image_mid_path:
  assumes "x1 \<in> open_common_setX" and "x2 \<in> open_common_setX"  
  shows "path_image (mid_path x1 x2) \<subseteq> drivable_area"
  using assms mid_path_in_midcurve_points2 midcurve_points_inside_drivable_area 
  unfolding path_image_def by auto
                        
theorem path_connected_drivable_area: 
  "path_connected drivable_area"
  unfolding path_connected_def
proof (rule ballI, rule ballI, rename_tac z1 z2)
  fix z1 z2
  assume z1_d:"z1 \<in> drivable_area" and z2_d:"z2 \<in> drivable_area"
  from this obtain x1 y1 x2 y2 where z1: "z1 = (x1, y1)" and z2: "z2 = (x2, y2)"    
    using drivable_area_def by auto
  note z1z2 = z1 z1_d z2 z2_d drivable_areaD1 drivable_areaD1'    
  show "\<exists>g. path g \<and> path_image g \<subseteq> drivable_area \<and> pathstart g = z1 \<and> pathfinish g = z2"
  proof (cases "x1 = x2")
    case True
    define g where "g \<equiv> linepath z1 z2"
      
    \<comment> \<open>proving first conjunct @{term "path g"}\<close>
    hence "path g" unfolding path_def by auto        
              
    \<comment> \<open>proving second conjunct @{term "path_image g \<subseteq> drivable_area"}\<close> 
    moreover have "path_image g \<subseteq> drivable_area"
      unfolding drivable_area_def
    proof (rule subsetI, rename_tac z, unfold mem_Collect_eq) 
      fix z
      assume 0: "z \<in> path_image g"
      from this obtain x y where 1: "z = (x,y)" using prod.exhaust by blast
      from fst_path_image[of "z1" "z2"] have "fst ` (path_image g) = {x2}"
        unfolding g_def using z1 z2 True by auto
      with 0 and 1 have "x = x2"  by (metis Domain.DomainI Domain_fst singletonD)
      with z2 have 2: "x \<in> open_common_setX" using drivable_areaD1'[OF z2_d] by auto           
      moreover from snd_path_image'[of "z1" "z2"] have "y \<in> between_setY x"
        using z1_d z2_d z1 z2 True 0 1 g_def \<open>x = x2\<close> image_subset_iff by auto          
      ultimately show "case z of (x,y) \<Rightarrow> x \<in> open_common_setX \<and> y \<in> between_setY x"           
        using 1 by auto      
    qed
      
    ultimately show ?thesis using pathstart_linepath pathfinish_linepath g_def
      by fastforce      
  next
    case False
    define g1 where "g1 \<equiv> linepath z1 (x1, midcurve_fun x1) "
    define g2 where "g2 \<equiv> mid_path x1 x2 " 
    define g3 where "g3 \<equiv> linepath (x2, midcurve_fun x2) z2"
    define g where "g \<equiv> (g1 +++ g2) +++ g3"
      
    have "pathfinish g1 = (x1, midcurve_fun x1)" unfolding g1_def by auto
    moreover  have "pathstart g2 = (x1, midcurve_fun x1)" unfolding g2_def 
      using pathstart_mid_path[of "x1" "x2"] z1 z1_d z2 z2_d drivable_areaD1 by auto           
    ultimately have 0: "pathfinish g1 = pathstart g2" by auto          
    have 1: "path (g1 +++ g2)"  
    proof (rule path_join_imp)   
      show "path g1" unfolding g1_def by auto
    next
      show "path g2" unfolding g2_def using path_mid_path[of "x1" "x2"] using z1z2 by auto
    next
      show "pathfinish g1 = pathstart g2" unfolding g1_def g2_def 
        using pathstart_mid_path[of "x1" "x2"] z1z2  by auto          
    qed      
    have 2: "path g3" unfolding g3_def by auto
    have "pathfinish g2 = (x2, midcurve_fun x2)" unfolding g2_def
      using pathfinish_mid_path[of "x1" "x2"] z1z2  by auto
    moreover have "pathstart g3 = (x2, midcurve_fun x2)" unfolding g3_def by auto
    ultimately have "pathfinish g2 = pathstart g3" by auto                    
    hence "pathfinish (g1 +++ g2) = pathstart g3" by auto        

    \<comment> \<open>proving first conjunct @{term "path g"}\<close> 
    hence "path g" unfolding g_def using 1 2 by auto          
     
    \<comment> \<open>proving third and fourth conjuncts\<close>
    have "pathstart g1 = z1" unfolding g1_def by auto
    hence "pathstart g = z1" unfolding g_def g1_def by auto
    have "pathfinish g3 = z2" unfolding g3_def by auto    
    hence "pathfinish g = z2" unfolding g_def g3_def by auto 
      
    \<comment> \<open>proving the second conjunct\<close> 
    have "path_image g \<subseteq> drivable_area"
      unfolding drivable_area_def g_def
    (* TODO : first and third subgoal has the SAME proof structure. Generalise this! *)        
    proof (rule subset_path_image_join, rule subset_path_image_join,  rule_tac[!] subsetI, 
          rename_tac[!] z, unfold mem_Collect_eq) 
      fix z
      assume 0: "z \<in> path_image g1"        
      from this obtain x y where 1: "z = (x, y)" unfolding g1_def by fastforce  
      from fst_path_image[of "z1" "(x1, midcurve_fun x1)"] have "fst ` (path_image g1) = {x1}"
        unfolding g1_def using z1  by auto
      with 0 and 1 have "x = x1" by (metis Domain.DomainI Domain_fst singletonD)
      with z1 have 2: "x \<in> open_common_setX" using drivable_areaD1'[OF z1_d] by auto           
      moreover from snd_path_image'[of "z1" "(x1, midcurve_fun x1)"] have "y \<in> between_setY x1"
        using z1_d z1 0 1 g1_def \<open>x = x1\<close> image_subset_iff midcurve_fun_inside_drivable_area
        calculation by auto
      ultimately show "case z of (x,y) \<Rightarrow> x \<in> open_common_setX \<and> y \<in> between_setY x"           
        using 1 \<open>x = x1\<close> by auto
    next
      fix z
      assume "z \<in> path_image g2"
      hence "z \<in> drivable_area" unfolding g2_def
        using path_image_mid_path[of "x1" "x2"] using z1z2 by auto
      thus "case z of (x,y) \<Rightarrow> x \<in> open_common_setX \<and> y \<in> between_setY x"  
        unfolding drivable_area_alt_def by auto
    next
      fix z
      assume 0: "z \<in> path_image g3"
      then obtain x y where 1:"z = (x, y)" unfolding g3_def by fastforce
      from fst_path_image[of "z2" "(x2, midcurve_fun x2)"] have "fst ` (path_image g3) = {x2}"
        unfolding g3_def using z2 by auto
      with 0 and 1 have "x = x2" by (metis Domain.DomainI Domain_fst singletonD)
      with z2 have 2: "x \<in> open_common_setX" using drivable_areaD1'[OF z2_d] by auto
      moreover from snd_path_image'[of "z2" "(x2, midcurve_fun x2)"] have "y \<in> between_setY x2"
        using z2_d z2 0 1 g3_def \<open>x = x2\<close> image_subset_iff midcurve_fun_inside_drivable_area
        by (metis (no_types, lifting) calculation fst_conv snd_conv snd_path_image')
      ultimately show "case z of (x,y) \<Rightarrow> x \<in> open_common_setX \<and> y \<in> between_setY x" 
        using 1 \<open>x=x2\<close> by auto
    qed      
    thus ?thesis using \<open>path g\<close> \<open>pathstart g = z1\<close> \<open>pathfinish g = z2\<close> by auto
  qed      
qed        
end  

  
subsection "A generalised simple road"
       
lemma det3_nonneg_scaleR3:
  "0 < e \<Longrightarrow> det3 0 xr P > 0 \<Longrightarrow> det3 0 xr (e *\<^sub>R (P - xr) + xr) > 0"
  by (auto simp add: det3_def' algebra_simps)  

lemma det3_nonneg_scaleR3':
  "0 < e \<Longrightarrow> det3 0 xr P \<le> 0 \<Longrightarrow> det3 0 xr (e *\<^sub>R (P - xr) + xr) \<le> 0"
  by (auto simp add: det3_def' algebra_simps)  
    
lemma det3_nonneg_scaleR4:    
  assumes "0 < e"
  assumes "det3 0 xr P > 0"
  shows "det3 0 (xr + e *\<^sub>R xr) (P + e *\<^sub>R xr) > 0"
proof -
  from assms(2) have 0: "fst P * snd xr < fst xr * snd P" unfolding det3_def' 
    by (auto simp add:algebra_simps)
  with assms(1) have "e * (fst P * snd xr) < e * (fst xr * snd P)" by auto
  with 0 have "fst P * snd xr + e * (fst P * snd xr) < fst xr * snd P + e * (fst xr * snd P)"      
    by auto
  thus ?thesis by (auto simp add:det3_def' algebra_simps)      
qed
          
lemma det3_nonneg_scaleR4':    
  assumes "0 < e"
  assumes "det3 0 xr P \<le> 0"
  shows "det3 0 (xr + e *\<^sub>R xr) (P + e *\<^sub>R xr) \<le> 0"
proof -
  from assms(2) have 0: "fst P * snd xr \<ge> fst xr * snd P" unfolding det3_def' 
    by (auto simp add:algebra_simps)
  with assms(1) have "e * (fst P * snd xr) \<ge> e * (fst xr * snd P)" by auto
  with 0 have "fst P * snd xr + e * (fst P * snd xr) \<ge> fst xr * snd P + e * (fst xr * snd P)"      
    by auto
  thus ?thesis by (auto simp add:det3_def' algebra_simps)      
qed
        
lemma det3_invariant1:
  assumes "0 < e"
  assumes "det3 p q r > 0" 
  shows "det3 p q (e *\<^sub>R (r - q) + q) > 0"
  using assms
proof -                                                              
  from assms(2) have "det3 0 (q - p) (r - p) > 0" using det3_translate_origin by auto
  hence "det3 0 (q - p) (e *\<^sub>R ((r - p) - (q - p)) + (q - p)) > 0" 
    using det3_nonneg_scaleR3[OF assms(1), of "q - p" "r - p"] by simp 
  hence "det3 0 (q - p) (e *\<^sub>R (r - q) + (q - p)) > 0" by (auto simp add: det3_def' algebra_simps)    
  thus "det3 p q (e *\<^sub>R (r - q) + q) > 0" by (auto simp add:det3_def' algebra_simps)    
qed
  
lemma det3_invariant1':
  assumes "0 < e"
  assumes "det3 p q r > 0"
  shows "det3 (p - e *\<^sub>R (q - p)) q r > 0"
  using assms  
proof - 
  from assms(2) have "det3 0 (q - p) (r - p) > 0" using det3_translate_origin by auto
  from det3_nonneg_scaleR4[OF assms(1) this] show ?thesis using det3_translate_origin
    by (metis (no_types, lifting) NO_MATCH_def add_uminus_conv_diff diff_diff_add diff_minus_eq_add)      
qed
  
lemma det3_invariant2:
  assumes "0 < e"
  assumes "det3 p q r \<le> 0"
  shows "det3 p q (e *\<^sub>R (r - q) + q) \<le> 0"
proof -
  from assms(2) have "det3 0 (q - p) (r - p) \<le> 0" using det3_translate_origin by auto
  hence "det3 0 (q - p) (e *\<^sub>R ((r - p) - (q - p)) + (q - p)) \<le> 0" 
    using det3_nonneg_scaleR3'[OF assms(1), of "q - p" "r - p"] by simp 
  hence "det3 0 (q - p) (e *\<^sub>R (r - q) + (q - p)) \<le> 0" by (auto simp add: det3_def' algebra_simps)    
  thus "det3 p q (e *\<^sub>R (r - q) + q) \<le> 0" by (auto simp add:det3_def' algebra_simps)    
qed

lemma det3_invariant2':
  assumes "0 < e"
  assumes "det3 p q r \<le> 0"
  shows "det3 (p - e *\<^sub>R (q - p)) q r \<le> 0"
  using assms  
proof - 
  from assms(2) have "det3 0 (q - p) (r - p) \<le> 0" using det3_translate_origin by auto
  from det3_nonneg_scaleR4'[OF assms(1) this] show ?thesis using det3_translate_origin
    by (metis (no_types, lifting) NO_MATCH_def add_uminus_conv_diff diff_diff_add diff_minus_eq_add)      
qed

theorem ccw_invariant:
  assumes "0 < e"
  shows "ccw' p q r = ccw' p q (e *\<^sub>R (r - q) + q)"
  unfolding ccw'_def  
  using det3_invariant1[OF assms] det3_invariant2[OF assms]  
proof -
  have "\<forall>x0 x1 x2. (0 < det3 x2 x1 x0) = (\<not> det3 x2 x1 x0 \<le> 0)"
    by linarith
  then show "(0 < det3 p q r) = (0 < det3 p q (e *\<^sub>R (r - q) + q))"
    by (metis (no_types) \<open>\<And>r q p. 0 < det3 p q r \<Longrightarrow> 0 < det3 p q (e *\<^sub>R (r - q) + q)\<close> 
                         \<open>\<And>r q p. det3 p q r \<le> 0 \<Longrightarrow> det3 p q (e *\<^sub>R (r - q) + q) \<le> 0\<close>)
qed  
  
theorem ccw_invariant':
  assumes "0 < e"
  shows "ccw' p q r = ccw' (p - e *\<^sub>R (q - p)) q r"
  unfolding ccw'_def
  using det3_invariant1'[OF assms] det3_invariant2'[OF assms]    
  by smt    
    
lemma det3_nonneg_scaleR1_eq':
  "0 < e \<Longrightarrow> det3 0 (e*\<^sub>Rxr) P < 0 \<longleftrightarrow> det3 0 xr P < 0"
  by (auto simp add: det3_def' algebra_simps)
    
lemma det3_nonneg_scaleR1_eq'':
  "0 < e \<Longrightarrow> det3 0 (e*\<^sub>Rxr) P = 0 \<longleftrightarrow> det3 0 xr P = 0"
  by (auto simp add: det3_def' algebra_simps)
    
lemma det3_nonneg_scaleR_segment1':
  assumes "det3 x y z < 0"
  assumes "0 \<le> a" "a < 1"
  shows "det3 ((1 - a) *\<^sub>R x + a *\<^sub>R y) y z < 0"
proof -
  from assms have "det3 0 ((1 - a) *\<^sub>R (y - x)) (z - x + (- a) *\<^sub>R (y - x)) < 0"    
    by (subst det3_nonneg_scaleR1_eq') (auto simp add: det3_def' algebra_simps)
  thus ?thesis
    by (auto simp: algebra_simps det3_translate_origin)
qed    
  
lemma det3_nonneg_scaleR_segment1'':
  assumes "det3 x y z \<noteq> 0"
  assumes "0 \<le> a" "a < 1"
  shows "det3 ((1 - a) *\<^sub>R x + a *\<^sub>R y) y z \<noteq> 0"
proof -
  from assms have "det3 0 ((1 - a) *\<^sub>R (y - x)) (z - x + (- a) *\<^sub>R (y - x)) \<noteq> 0"    
    by (subst det3_nonneg_scaleR1_eq'') (auto simp add: det3_def' algebra_simps)
  thus ?thesis
    by (auto simp: algebra_simps det3_translate_origin)
qed   
    
theorem ccw_invariant'':
  assumes "0 \<le> e" and "e < 1"
  shows "ccw' p q r = ccw' ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r"
  unfolding ccw'_def    
proof (rule iffI, rule_tac[2] contrapos_np[where Q="\<not> 0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r"]) 
  assume "0 < det3 p q r"
  hence "0 \<le> det3 p q r" and "det3 p q r \<noteq> 0" by auto    
  from det3_nonneg_scaleR_segment1[OF this(1) assms] have "0 \<le> det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r " 
    by auto    
  moreover    
  from det3_nonneg_scaleR_segment1''[OF \<open>det3 p q r \<noteq> 0\<close> assms] have "det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r \<noteq> 0"
    by auto
  ultimately show "0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r" by auto
next
  assume "0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r"
  thus "\<not> \<not> 0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r" by auto
next
  assume "\<not> 0 < det3 p q r"
  hence "det3 p q r \<le> 0" by auto
  hence "det3 p q r < 0 \<or> det3 p q r = 0" by auto
  moreover    
  { assume "det3 p q r < 0"
    from det3_nonneg_scaleR_segment1'[OF this assms] have " det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r < 0" .
    hence "\<not> 0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r" by auto }
    
  moreover
  { assume "det3 p q r = 0"
    with det3_nonneg_scaleR_segment1''[OF _ assms, of "p" "q" "r"] have "det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r = 0"
      using assms(1) assms(2) coll_convex det3_rotate by auto
    hence "\<not> 0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r" by auto }
    
  ultimately show "\<not> 0 < det3 ((1 - e) *\<^sub>R p + e *\<^sub>R q) q r" by auto
qed      
    
definition line_equation :: "real2 \<Rightarrow> real2 \<Rightarrow> real \<Rightarrow> real" where
  "line_equation p1 p2 \<equiv> (\<lambda>x. (snd p2 - snd p1) / (fst p2 - fst p1) * (x - fst p1) + snd p1)"
  
lemma line_equation_alt_def:
  "line_equation p1 p2 \<equiv> (\<lambda>x. (snd p2 - snd p1) / (fst p2 - fst p1) * x - (snd p2 - snd p1) / (fst p2 - fst p1) * fst p1 + snd p1)"
  unfolding line_equation_def using right_diff_distrib[of "(snd p2 - snd p1) / (fst p2 - fst p1)" _ "fst p1"]
  by auto
            
lemma
  "line_equation p1 p2 (fst p1) = (snd p1)"
  unfolding line_equation_def by (auto simp add:algebra_simps)
    
lemma
  assumes "fst p1 \<noteq> fst p2"
  shows "line_equation p1 p2 (fst p2) = (snd p2)"
  unfolding line_equation_def using assms by (auto simp add:divide_simps) 
    
theorem line_eq_differentiable:
  assumes "fst p1 \<noteq> fst p2"
  shows "line_equation p1 p2 differentiable at x"
  using assms unfolding line_equation_def by (auto intro:derivative_intros)    
        
theorem 
  assumes "fst p1 \<noteq> fst p2"
  shows "((line_equation) p1 p2 has_field_derivative ((snd p2 - snd p1) / (fst p2 - fst p1))) (at x within s)"
proof -
  have "fst p2 - fst p1 \<noteq> 0" using assms by auto   
  hence 0: "line_equation p1 p2 \<equiv> (\<lambda>x. (snd p2 - snd p1) / (fst p2 - fst p1) * x - (snd p2 - snd p1) / (fst p2 - fst p1) * fst p1 + snd p1)"
    unfolding line_equation_alt_def by auto
  define const :: "real \<Rightarrow> real" where "const \<equiv> \<lambda>x. snd p1 - (snd p2 - snd p1) / (fst p2 - fst p1) * fst p1"
  hence cdx: "const differentiable at x" using assms by (auto intro:derivative_intros)
  define inner :: "real \<Rightarrow> real" where "inner \<equiv> \<lambda>x. (snd p2 - snd p1) / (fst p2 - fst p1) * x"
  hence idx: "inner differentiable at x" using assms by (auto intro:derivative_intros)
  have idx':"(inner has_field_derivative (snd p2 - snd p1) / (fst p2 - fst p1)) (at x within s)"
    unfolding inner_def using DERIV_cmult_Id[of "(snd p2 - snd p1) / (fst p2 - fst p1)"] by blast 
  have 1: "line_equation p1 p2 \<equiv> \<lambda>x. inner x + const x" unfolding 0 inner_def const_def 
    by (auto simp add:algebra_simps)      
  have "(line_equation p1 p2 has_field_derivative ((snd p2 - snd p1) / (fst p2 - fst p1)) + 0) (at x within s)"
    unfolding 1 by (intro Deriv.field_differentiable_add) (auto simp add:idx' const_def) 
  thus ?thesis by auto              
qed  
  
lemma line_equation_closed_segment:
  assumes "p \<in> closed_segment p1 p2"
  assumes "fst p1 \<noteq> fst p2"  
  shows "line_equation p1 p2 (fst p) = snd q"
  sorry
      
locale simple_road2 =  le: simple_boundary curve_left domain +  ri: simple_boundary curve_right domain 
  for curve_left and curve_right and domain +
  assumes domain_nonempty: "domain \<noteq> {}"   
  \<comment>\<open>The following assumption can be easily checked with @{thm "simple_boundary.checking_strict_mono"}.\<close>
  assumes mono_x_le: "strict_mono_in le.curve_eq_x domain" 
      and mono_x_ri: "strict_mono_in ri.curve_eq_x domain"
  assumes non_intersecting: "\<forall>t\<in>domain. curve_left t \<noteq> curve_right t"      
  assumes diff:"curve_right differentiable (at_right (Inf domain))"
  assumes diff_le: "curve_left differentiable (at_right (Inf domain))"    
begin
      
abbreviation common_setX where
  "common_setX \<equiv> le.setX \<inter> ri.setX"    
  
definition left_start_boundary :: "real \<Rightarrow> real2" where
  "left_start_boundary \<equiv> (let t_inf = Inf domain; le_inf = curve_left t_inf; 
                              ri_inf = curve_right t_inf;  le_x = fst le_inf; ri_x = fst ri_inf 
                          in 
                            if le_x \<le> ri_x then linepath le_inf ri_inf else linepath ri_inf le_inf)"  
    
theorem left_boundary_param_x_strict_mono:
  assumes "fst (curve_left (Inf domain)) \<noteq> fst (curve_right (Inf domain))"
  shows "strict_mono_in (fst \<circ> left_start_boundary) {0..1}"
  unfolding comp_def left_start_boundary_def Let_def 
proof (split if_splits, rule conjI, rule_tac[!] impI, rule_tac[!] strict_mono_inI)
  fix x y :: real
  assume "x \<in> {0..1}" and "y \<in> {0..1}"
  assume "x < y"
  hence "0 < y - x" by auto  
  assume "fst (curve_left (Inf domain)) \<le> fst (curve_right (Inf domain))"
  with assms have 0: "fst (curve_left (Inf domain)) < fst (curve_right (Inf domain))" by auto
  define cli where "cli \<equiv> curve_left (Inf domain)"
  define cri where "cri \<equiv> curve_right (Inf domain)"
  with cli_def and 0 have "fst cli < fst cri" by auto  
  have 1: "fst \<circ> (linepath cli cri) = (\<lambda>x. (1 - x) * (fst cli) + x * (fst cri))" 
    unfolding comp_def linepath_def by auto
  have "(fst \<circ> (linepath cli cri)) x < (fst \<circ> (linepath cli cri)) y"
  proof -
    from \<open>fst cli < fst cri\<close> have "fst cli * (y - x) < fst cri *(y - x)" (is "?lhs1 < ?rhs1")
      using \<open>x < y\<close> mult_strict_right_mono by auto
    hence "fst cli + ?lhs1 < fst cli + ?rhs1" by linarith
    hence "(1 - x) * fst cli + x * fst cri < (1 - y) * fst cli + y * fst cri"
      by (auto simp add:algebra_simps)
    with 1 show ?thesis by auto        
  qed
  thus "fst (linepath (curve_left (Inf domain)) (curve_right (Inf domain)) x)
           < fst (linepath (curve_left (Inf domain)) (curve_right (Inf domain)) y)"
    unfolding comp_def cli_def cri_def by auto
next
  fix x y :: real
  assume "x \<in> {0..1}" and "y \<in> {0..1}"
  assume "x < y"
  define cli where "cli \<equiv> curve_left (Inf domain)"
  define cri where "cri \<equiv> curve_right (Inf domain)"
  assume "\<not> fst (curve_left (Inf domain)) \<le> fst (curve_right (Inf domain))"    
  hence "fst cli > fst cri" unfolding cli_def cri_def by auto
  have 2: "fst \<circ> (linepath cri cli) = (\<lambda>x. (1 - x) * (fst cri) + x * (fst cli))"
    unfolding comp_def linepath_def by auto
  have "(fst \<circ> (linepath cri cli)) x < (fst \<circ> (linepath cri cli)) y"
  proof -
    from \<open>fst cri < fst cli\<close> have "fst cri * (y - x) < fst cli *(y - x)" (is "?lhs1 < ?rhs1")
      using \<open>x < y\<close> mult_strict_right_mono by auto
    hence "fst cri + ?lhs1 < fst cri + ?rhs1" by linarith
    hence "(1 - x) * fst cri + x * fst cli < (1 - y) * fst cri + y * fst cli"
      by (auto simp add:algebra_simps)
    with 2 show ?thesis by auto        
  qed   
  thus " fst (linepath (curve_right (Inf domain)) (curve_left (Inf domain)) x)
           < fst (linepath (curve_right (Inf domain)) (curve_left (Inf domain)) y)"
    unfolding comp_def cli_def cri_def by auto
qed
    
definition right_start_boundary :: "real \<Rightarrow> real2" where
  "right_start_boundary \<equiv> (let t_sup = Sup domain; le_sup = curve_left t_sup; 
                               ri_sup = curve_right t_sup; le_x = fst le_sup; ri_x = fst ri_sup
                           in
                            if ri_x \<le> le_x then linepath ri_sup le_sup else linepath le_sup ri_sup)"
  
theorem right_boundary_param_x_strict_mono:
  assumes "fst (curve_left (Sup domain)) \<noteq> fst (curve_right (Sup domain))"
  shows "strict_mono_in (fst \<circ> right_start_boundary) {0..1}"
  unfolding comp_def right_start_boundary_def Let_def 
proof (split if_splits, rule conjI, rule_tac[!] impI, rule_tac[!] strict_mono_inI)
  fix x y :: real
  assume "x \<in> {0..1}" and "y \<in> {0..1}"
  assume "x < y"
  hence "0 < y - x" by auto  
  assume "fst (curve_right (Sup domain)) \<le> fst (curve_left (Sup domain))"
  with assms have 0: "fst (curve_right (Sup domain)) < fst (curve_left (Sup domain))" by auto
  define cls where "cls \<equiv> curve_left (Sup domain)"
  define crs where "crs \<equiv> curve_right (Sup domain)"
  with cls_def and 0 have "fst crs < fst cls" by auto  
  have 1: "fst \<circ> (linepath crs cls) = (\<lambda>x. (1 - x) * (fst crs) + x * (fst cls))" 
    unfolding comp_def linepath_def by auto
  have "(fst \<circ> (linepath crs cls)) x < (fst \<circ> (linepath crs cls)) y"
  proof -
    from \<open>fst crs < fst cls\<close> have "fst crs * (y - x) < fst cls *(y - x)" (is "?lhs1 < ?rhs1")
      using \<open>x < y\<close> mult_strict_right_mono by auto
    hence "fst cls + ?lhs1 < fst cls + ?rhs1" by linarith
    hence "(1 - x) * fst crs + x * fst cls < (1 - y) * fst crs + y * fst cls"
      by (auto simp add:algebra_simps)
    with 1 show ?thesis by auto        
  qed
  thus "fst (linepath (curve_right (Sup domain)) (curve_left (Sup domain)) x)
           < fst (linepath (curve_right (Sup domain)) (curve_left (Sup domain)) y)"
    unfolding comp_def cls_def crs_def by auto
next
  fix x y :: real
  assume "x \<in> {0..1}" and "y \<in> {0..1}"
  assume "x < y"
  hence "0 < y - x" by auto  
  define cls where "cls \<equiv> curve_left (Sup domain)"
  define crs where "crs \<equiv> curve_right (Sup domain)"
  assume "\<not> fst (curve_right (Sup domain)) \<le> fst (curve_left (Sup domain))"
  hence "fst crs > fst cls" using cls_def crs_def by auto    
  have 1: "fst \<circ> (linepath cls crs) = (\<lambda>x. (1 - x) * (fst cls) + x * (fst crs))" 
    unfolding comp_def linepath_def by auto
  have "(fst \<circ> (linepath cls crs)) x < (fst \<circ> (linepath cls crs)) y"
  proof -
    from \<open>fst crs > fst cls\<close> have "fst crs * (y - x) > fst cls *(y - x)" (is "?lhs1 > ?rhs1")
      using \<open>x < y\<close> mult_strict_right_mono by auto
    hence "fst crs + ?lhs1 > fst crs + ?rhs1" by linarith
    hence "(1 - x) * fst cls + x * fst crs < (1 - y) * fst cls + y * fst crs"
      by (auto simp add:algebra_simps)
    with 1 show ?thesis by auto        
  qed
  thus "fst (linepath (curve_left (Sup domain)) (curve_right (Sup domain)) x)
           < fst (linepath (curve_left (Sup domain)) (curve_right (Sup domain)) y)"
    unfolding comp_def cls_def crs_def by auto
qed             
    
theorem domain_inf_sup:
  "domain = {Inf domain .. Sup domain}"
proof -
  from le.domain_interval obtain a and b where "domain = {a .. b}" by auto
  with domain_nonempty have "a \<le> b" by auto
  with \<open>domain = {a .. b}\<close> have "Inf domain = a" and "Sup domain = b" by auto
  with \<open>domain = {a .. b}\<close> show ?thesis by auto      
qed               
        
theorem domain_closed_segment_inf_sup:
  "domain = closed_segment (Inf domain) (Sup domain)"
  using domain_inf_sup closed_segment_real  cInf_le_cSup[OF domain_nonempty le.bdd_above_domain 
    le.bdd_below_domain] by auto
    
theorem inf_in_dom:
  "Inf domain \<in> domain"
  using closed_contains_Inf[OF domain_nonempty le.bdd_below_domain le.closed_domain] by auto
                                              
theorem sup_in_dom:
  "Sup domain \<in> domain"    
  using closed_contains_Sup[OF domain_nonempty le.bdd_above_domain le.closed_domain] by auto    
    
definition ri_tangent_at_inf where
  "ri_tangent_at_inf \<equiv> vector_derivative curve_right (at_right (Inf domain))"  

definition le_tangent_at_inf where
  "le_tangent_at_inf \<equiv> vector_derivative curve_left (at_right (Inf domain))"
  
theorem ri_v_deriv_at_inf:
  "(curve_right has_vector_derivative ri_tangent_at_inf) (at_right (Inf domain))"
  using diff by (auto simp add: vector_derivative_works ri_tangent_at_inf_def)
    
theorem le_v_deriv_at_inf:   
  "(curve_left has_vector_derivative le_tangent_at_inf) (at_right (Inf domain))"
  using diff_le by (auto simp add: vector_derivative_works le_tangent_at_inf_def)
      
\<comment>\<open>The tangent line for the right curve at 0.\<close>  
definition cr_tangent_line :: "real2 set" where
  "cr_tangent_line \<equiv> {(x, y). \<exists>t>0. (x, y) = curve_right 0 + t *\<^sub>R ri_tangent_at_inf}"  
  
definition cl_tangent_line :: "real2 set" where
  "cl_tangent_line \<equiv> {(x, y). \<exists>t>0. (x, y) = curve_left 0 + t *\<^sub>R le_tangent_at_inf}"  
  
theorem cr_tangent_line_nonempty:
  "\<exists>x. x \<in> cr_tangent_line"
proof -
  obtain x and y where "(x,y) = curve_right 0 + 1 *\<^sub>R ri_tangent_at_inf" using prod.collapse by blast
  hence "\<exists>t>0. (x, y) = curve_right 0 + t *\<^sub>R ri_tangent_at_inf" 
    by (auto intro: exI[where x="1"])
  thus ?thesis unfolding cr_tangent_line_def by auto        
qed
  
theorem cl_tangent_line_nonempty:
  "\<exists>x. x \<in> cl_tangent_line"  
proof -
  obtain x and y where "(x,y) = curve_left 0 + 1 *\<^sub>R le_tangent_at_inf" using prod.collapse by blast
  hence "\<exists>t>0. (x, y) = curve_left 0 + t *\<^sub>R le_tangent_at_inf" 
    by (auto intro: exI[where x="1"])
  thus ?thesis unfolding cl_tangent_line_def by auto        
qed
  
theorem cr_tangent_line_D1:
  assumes "x \<in> cr_tangent_line"  
  obtains t where "x = curve_right 0 + t *\<^sub>R ri_tangent_at_inf" and "0 < t"
  using assms prod.collapse unfolding cr_tangent_line_def by auto    
    
theorem cl_tangent_line_D1:
  assumes "x \<in> cl_tangent_line"  
  obtains t where "x = curve_left 0 + t *\<^sub>R le_tangent_at_inf" and "0 < t"
  using assms prod.collapse unfolding cl_tangent_line_def by auto    
      
\<comment>\<open>Basically we can use any point in the tangent line to determine the direction of the simple road.
  To be more exact, all points in the direction of the tangent line.\<close>    
theorem ri_ccw'_on_tangent_line:
  assumes "p1 \<in> cr_tangent_line" and "p2 \<in> cr_tangent_line"    
  shows "ccw' (curve_left 0) (curve_right 0) p1 = ccw' (curve_left 0) (curve_right 0) p2"
proof -
  from assms obtain t1 where "p1 = curve_right 0 + t1 *\<^sub>R ri_tangent_at_inf" and "0 < t1"
    using cr_tangent_line_D1 by blast
  hence "ri_tangent_at_inf = (1 / t1) *\<^sub>R (p1 - curve_right 0)" by (auto simp add:divide_simps)      
  moreover    
  from assms obtain t2 where "p2 = curve_right 0 + t2 *\<^sub>R ri_tangent_at_inf" and "0 < t2" 
    using cr_tangent_line_D1 by blast
  ultimately have *: "p2 = curve_right 0 + (t2 / t1) *\<^sub>R (p1 - curve_right 0)" and "0 < t2 / t1"
    using \<open>0 < t1\<close> by (auto simp add:divide_simps)    
  show ?thesis unfolding *
    using ccw_invariant[OF \<open>0 < t2 / t1\<close>, of "curve_left 0" "curve_right 0" "p1"] 
    by (auto simp add:algebra_simps)             
qed
    
theorem le_ccw'_on_tangent_line:
  assumes "p1 \<in> cl_tangent_line" and "p2 \<in> cl_tangent_line"    
  shows "ccw' p1 (curve_left 0) (curve_right 0) = ccw' p2 (curve_left 0) (curve_right 0)"
proof -
  from assms obtain t1 where t1_cond: "p1 = curve_left 0 + t1 *\<^sub>R le_tangent_at_inf" and "0 < t1"
    using cl_tangent_line_D1 by blast
  hence letai_def: "le_tangent_at_inf = (1 / t1) *\<^sub>R (p1 - curve_left 0)" by (auto simp add:divide_simps)          
  from assms obtain t2 where t2_cond: "p2 = curve_left 0 + t2 *\<^sub>R le_tangent_at_inf" and "0 < t2" 
    using cl_tangent_line_D1 by blast
  have "t1 < t2 \<or> t1 \<ge> t2 " by auto
  moreover    
  { assume "t1 < t2"
    from t1_cond and t2_cond have "p2 = p1 + (t2 - t1) *\<^sub>R le_tangent_at_inf" 
      by (auto simp add:algebra_simps)
    with letai_def have p2_def: "p2 = p1 + ((t2 - t1) / t1) *\<^sub>R (p1 - curve_left 0)"
      by (auto simp add:field_simps)
    from \<open>t1 < t2\<close> and \<open>0 < t1\<close> have "0 < (t2 - t1) / t1" by auto
    have ?thesis unfolding p2_def
      using ccw_invariant'[OF \<open>0 < (t2 - t1) / t1\<close>, of "p1" "curve_left 0" "curve_right 0"] 
      by (simp add: add_diff_eq diff_diff_eq2 real_vector.scale_right_diff_distrib) }    
  moreover    
  { assume "t1 \<ge> t2"
    from t1_cond and t2_cond and letai_def 
      have "p2 = curve_left 0 + (t2 / t1) *\<^sub>R (p1 - curve_left 0)" and "0 < t2 / t1"
      using \<open>0 < t1\<close> \<open>0 < t2\<close> by (auto simp add:divide_simps)  
    hence *: "p2 = (1 - t2 / t1) *\<^sub>R (curve_left 0) + (t2 / t1) *\<^sub>R p1"
      by (smt add.commute add.left_commute diff_add_cancel scaleR_add_left scaleR_add_right scaleR_one)
    hence **: "p2 = (1 - t2 / t1) *\<^sub>R (curve_left 0) + (1 - (1 - t2 / t1)) *\<^sub>R p1" 
      by auto
    from \<open>0 < t2 /t1\<close> \<open>t1 \<ge> t2\<close> and \<open>0 < t1\<close> have "0 \<le> 1 - t2 / t1" and "1 - t2 / t1 < 1"  by auto 
    from ccw_invariant''[OF this] have ?thesis using **  by (metis add.commute) }
  ultimately show ?thesis by auto    
qed
    
definition direction_right :: bool where
  "direction_right \<equiv> (let 
                           inf_dom = Inf domain; 
                           cl_inf = curve_left inf_dom;  cr_inf = curve_right inf_dom; 
                           tgt_ri = cr_inf + 1 *\<^sub>R ri_tangent_at_inf;
                           tgt_le = cl_inf + 1 *\<^sub>R le_tangent_at_inf  
                      in 
                           if min2D cr_inf cl_inf = cr_inf then 
                             ccw' cl_inf cr_inf tgt_ri 
                           else 
                             ccw' tgt_le cl_inf cr_inf)"  

definition direction_left :: bool where
  "direction_left \<equiv> (let 
                           inf_dom = Inf domain; 
                           cl_inf = curve_left inf_dom;  cr_inf = curve_right inf_dom; 
                           tgt_ri = cr_inf + 1 *\<^sub>R ri_tangent_at_inf;
                           tgt_le = cl_inf + 1 *\<^sub>R le_tangent_at_inf  
                      in 
                           if min2D cr_inf cl_inf = cr_inf then 
                             det3 cl_inf cr_inf tgt_ri < 0
                           else 
                             det3 tgt_le cl_inf cr_inf < 0)"  
    
definition open_domain :: "real set" where
  "open_domain \<equiv> domain - {Inf domain, Sup domain}"
  
theorem convex_open_domain:
  "convex open_domain"
  unfolding open_domain_def  using le.convex_domain extreme_point_of_stillconvex[of "domain"] 
  domain_closed_segment_inf_sup inf_in_dom sup_in_dom 
  by (metis atLeastAtMost_diff_ends convex_real_interval(8) domain_inf_sup)
  
lemma open_domain_subset_domain:
  "t \<in> open_domain \<Longrightarrow> t \<in> domain"
  unfolding open_domain_def by auto  
  
definition inside :: "real2 set" where
  "inside \<equiv> {(x,y). \<exists>t \<in> open_domain. (x,y) \<in> open_segment (curve_left t) (curve_right t)}"
  
definition insideP :: "real2 \<Rightarrow> bool" where
  "insideP x \<equiv> \<exists>t \<in> open_domain. x \<in> open_segment (curve_left t) (curve_right t)"  

theorem insideP_eq:
  "(x \<in> inside) = insideP x"
  unfolding insideP_def inside_def by auto
    
theorem insidePI[intro]:
  assumes "t \<in> open_domain"
  assumes "x \<in> open_segment (curve_left t) (curve_right t)"
  shows "insideP x"  
  using assms unfolding insideP_def by auto
    
theorem insidePD:
  assumes "insideP x"
  obtains t where "t \<in> open_domain \<and> x \<in> open_segment (curve_left t) (curve_right t)"
  using assms unfolding insideP_def by auto
  
definition midcurve_eq :: "real \<Rightarrow> real2" where
  "midcurve_eq  \<equiv> \<lambda>t. (1 / 2) *\<^sub>R (curve_left t + curve_right t)"
  
theorem midcurve_inside:
  assumes "t \<in> open_domain"
  shows "midcurve_eq t \<in> inside"
  unfolding midcurve_eq_def insideP_eq
proof (intro insidePI, rule assms, unfold in_segment(2), rule conjI)
  from assms have "t \<in> domain" using open_domain_subset_domain by auto
  with non_intersecting show "curve_left t \<noteq> curve_right t" by auto      
next
  show "\<exists>u>0. u < 1 \<and> (1 / 2) *\<^sub>R (curve_left t + curve_right t) = 
                                                      (1 - u) *\<^sub>R curve_left t + u *\<^sub>R curve_right t "  
    by(rule exI[where x="1/2"]) (auto simp add:algebra_simps)  
qed
  
theorem midcurve_in_open_segment:
  assumes "t \<in> open_domain"
  shows "midcurve_eq t \<in> open_segment (curve_left t) (curve_right t)"
  unfolding midcurve_eq_def in_segment(2)
proof 
  from assms have "t \<in> domain" unfolding open_domain_def by auto
  with non_intersecting show "curve_left t \<noteq> curve_right t" by auto
next
  show "\<exists>u>0. u < 1 \<and> (1 / 2) *\<^sub>R (curve_left t + curve_right t) = 
                                                      (1 - u) *\<^sub>R curve_left t + u *\<^sub>R curve_right t "  
    by(rule exI[where x="1/2"]) (auto simp add:algebra_simps)    
qed
  
theorem continuous_midcurve_eq:
  "continuous_on domain midcurve_eq"
  unfolding midcurve_eq_def using le.continuous ri.continuous
  by (auto simp add:continuous_intros)
    
theorem
  "path_connected inside"
  unfolding path_connected_def
proof (rule ballI, rule ballI, rename_tac z1 z2)
  fix z1 z2
  assume "z1 \<in> inside" and "z2 \<in> inside"
  hence "insideP z1" and inz2: "insideP z2" using insideP_eq by auto
  then obtain t1 where "t1 \<in> open_domain" and "z1 \<in> open_segment (curve_left t1) (curve_right t1)"
    using insidePD by blast
  from inz2 obtain t2 where "t2 \<in> open_domain" and "z2 \<in> open_segment (curve_left t2) (curve_right t2)"
    using insidePD by blast  
  obtain z1' and z2' where "z1' = midcurve_eq t1" and "z2' = midcurve_eq t2" by auto      
  obtain path1 and path2 where path1_def: "path1 \<equiv> linepath z1 z1'" and 
                               path2_def: "path2 \<equiv> linepath z2' z2" by auto
  define path_mid where path_mid_def: "path_mid \<equiv> midcurve_eq \<circ> (linepath t1 t2)"    
  define path_g where "path_g \<equiv> (path1 +++ path_mid) +++ path2"      
    
  have 0: "path (path1 +++ path_mid)"
  proof (rule path_join_imp)
    from path1_def show "path (path1)"  by auto
  next
    have *: "path_image (linepath t1 t2) = closed_segment t1 t2"
      using path_image_linepath  by auto
    from \<open>t1 \<in> open_domain\<close> and \<open>t2 \<in> open_domain\<close> have "t1 \<in> domain" and "t2 \<in> domain" 
      unfolding open_domain_def by auto         
    hence "closed_segment t1 t2 \<subseteq> domain" using closed_segment_subset using le.convex_domain
      by auto
    hence 2: "continuous_on (path_image (linepath t1 t2)) midcurve_eq" using * continuous_midcurve_eq
      by (auto simp add: continuous_on_subset)                
    thus "path (path_mid)" unfolding path_mid_def 
      by (auto intro:path_continuous_image)  
  next      
    have "pathfinish path1 = z1'" unfolding path1_def by auto
    moreover
    have "pathstart path_mid = z1'" unfolding path_mid_def comp_def \<open>z1' = midcurve_eq t1\<close>
      by (simp add: linepath_def path_defs(2))
    ultimately show "pathfinish path1 = pathstart path_mid" by auto          
  qed
            
  have pg: "path (path_g)"
    unfolding path_g_def
  proof (rule path_join_imp, rule 0)
    show "path path2" using path2_def by auto
  next
    have "pathfinish (path1 +++ path_mid) = pathfinish path_mid" by auto
    also have "... = z2'" unfolding path_mid_def comp_def \<open>z2' = midcurve_eq t2\<close>
      by (metis  path_defs(3) pathfinish_linepath)
    also have "... = pathstart path2" using path2_def by auto    
    finally show "pathfinish (path1 +++ path_mid) = pathstart path2" by auto        
  qed
    
  have 1: "path_image path1 \<subseteq> inside"
  proof (rule subsetI, unfold insideP_eq, intro insidePI, rule \<open>t1 \<in> open_domain\<close>)
    fix x
    assume "x \<in> path_image path1"
    have *: "path_image path1 = closed_segment z1 z1'" unfolding path1_def by auto
    have "z1' \<in> open_segment (curve_left t1) (curve_right t1)" unfolding \<open>z1' = midcurve_eq t1\<close>
      using midcurve_in_open_segment[OF  \<open>t1 \<in> open_domain\<close>] .      
    with \<open>z1 \<in> open_segment (curve_left t1) (curve_right t1)\<close> have 
      "closed_segment z1 z1' \<subseteq> open_segment (curve_left t1) (curve_right t1)" 
      by (auto simp add:closed_segment_subset)  
    with * show "x \<in> path_image path1 \<Longrightarrow> x \<in> open_segment (curve_left t1) (curve_right t1)"          
      by auto        
  qed    
    
  have "closed_segment t1 t2 \<subseteq> open_domain"      
    using closed_segment_subset[OF \<open>t1 \<in> open_domain\<close> \<open>t2 \<in> open_domain\<close>  convex_open_domain] .          
  hence 2: "path_image path_mid \<subseteq> inside"
    unfolding path_mid_def path_image_def sym[OF image_comp] linepath_image_01 using midcurve_inside
    by auto
  
  have 3: "path_image path2 \<subseteq> inside"
  proof (rule subsetI, unfold insideP_eq, intro insidePI, rule \<open>t2 \<in> open_domain\<close>)
    fix x
    assume "x \<in> path_image path2"
    have *: "path_image path2 = closed_segment z2' z2" unfolding path2_def by auto
    have "z2' \<in> open_segment (curve_left t2) (curve_right t2)" unfolding \<open>z2' = midcurve_eq t2\<close>
      using midcurve_in_open_segment[OF \<open>t2 \<in> open_domain\<close>] . 
    with \<open>z2 \<in> open_segment (curve_left t2) (curve_right t2)\<close> have 
      "closed_segment z2' z2 \<subseteq> open_segment (curve_left t2) (curve_right t2)"
      by (auto simp add:closed_segment_subset)
    with * show "x \<in> path_image path2 \<Longrightarrow> x \<in> open_segment (curve_left t2) (curve_right t2)"
      by auto  
  qed
    
  from 1 2 3 have pi: "path_image path_g \<subseteq> inside"
    unfolding path_g_def by (simp add: subset_path_image_join path_image_join_subset)
    
  have ps: "pathstart path_g = z1" unfolding path_g_def using pathstart_join path1_def by auto
  have "pathfinish path_g = z2" unfolding path_g_def using pathfinish_join path2_def by auto
  with pg pi ps show 
    "\<exists>g. path g \<and> path_image g \<subseteq> local.inside \<and> pathstart g = z1 \<and> pathfinish g = z2" by auto
qed  
    
definition le_lb_x :: real where
  "le_lb_x \<equiv> le.curve_eq_x (Inf domain)"

theorem le_lb_x_lower_bound:
  "t \<in> domain \<Longrightarrow> le_lb_x \<le> le.curve_eq_x t"
  using mono_x_le domain_inf_sup unfolding le_lb_x_def strict_mono_in_def by (smt atLeastAtMost_iff)
  
definition ri_lb_x :: real where
  "ri_lb_x \<equiv> ri.curve_eq_x (Inf domain)"
  
theorem ri_lb_x_lower_bound:
  "t \<in> domain \<Longrightarrow> ri_lb_x \<le> ri.curve_eq_x t"
  using mono_x_ri domain_inf_sup unfolding ri_lb_x_def strict_mono_in_def by (smt atLeastAtMost_iff)

definition lb_x :: real where
  "lb_x \<equiv> min le_lb_x ri_lb_x"
    
theorem lb_x_lower_bound_le:
  "t \<in> domain \<Longrightarrow> lb_x \<le> le.curve_eq_x t"  
  unfolding lb_x_def min_def using le_lb_x_lower_bound by fastforce

theorem rb_x_lower_bound_ri:
  "t \<in> domain \<Longrightarrow> lb_x \<le> ri.curve_eq_x t"
  unfolding lb_x_def min_def using ri_lb_x_lower_bound by fastforce
  
definition le_ub_x :: real where
  "le_ub_x \<equiv> le.curve_eq_x (Sup domain)"

theorem le_ub_x_upper_bound:
  "t \<in> domain \<Longrightarrow> le.curve_eq_x t \<le> le_ub_x"
  using mono_x_le domain_inf_sup unfolding le_ub_x_def strict_mono_in_def by (smt atLeastAtMost_iff)

definition ri_ub_x :: real where
  "ri_ub_x \<equiv> ri.curve_eq_x (Sup domain)"
  
theorem ri_ub_x_upper_bound:
  "t \<in> domain \<Longrightarrow> ri.curve_eq_x t \<le> ri_ub_x"
  using mono_x_ri domain_inf_sup unfolding ri_ub_x_def strict_mono_in_def by (smt atLeastAtMost_iff)
  
definition ub_x :: real where
  "ub_x \<equiv> max le_ub_x ri_ub_x"
  
theorem ub_x_upper_bound_le:
  "t \<in> domain \<Longrightarrow> le.curve_eq_x t \<le> ub_x"  
  unfolding ub_x_def max_def using le_ub_x_upper_bound by fastforce
    
theorem ub_x_upper_bound_ri:
  "t \<in> domain \<Longrightarrow> ri.curve_eq_x t \<le> ub_x"
  unfolding ub_x_def max_def using ri_ub_x_upper_bound by fastforce
    
theorem 
  "lb_x \<le> ub_x" 
  using inf_in_dom lb_x_def lb_x_lower_bound_le ub_x_def ub_x_upper_bound_le by fastforce  
    
definition union_setX :: "real set" where
  "union_setX \<equiv> {lb_x .. ub_x}"
  
theorem 
  "common_setX \<subseteq> union_setX"
  unfolding union_setX_def 
  using lb_x_def lb_x_lower_bound_le le.setX_alt_def ub_x_def ub_x_upper_bound_le by auto

(*    
definition bounds :: "real \<Rightarrow> (real \<times> real) option" where
  "bounds x \<equiv> 
    (if x \<in> common_setX then Some (ri.f_of_x x, le.f_of_x x) 
     else if x \<in> union_setX \<and> x > (Sup ri.setX) then 
       Some (line_equation (curve_left (Sup domain)) (curve_right (Sup domain)) x, le.f_of_x x) 
     else if x \<in> union_setX \<and> x < (Inf ri.setX) then 
       Some (line_equation (curve_left (Inf domain)) (curve_right (Inf domain)) x, le.f_of_x x) 
     else if x \<in> union_setX \<and> x > (Sup le.setX) then 
       Some (line_equation (curve_left (Sup domain)) (curve_right (Sup domain)) x, ri.f_of_x x) 
     else if x \<in> union_setX \<and> x < (Inf le.setX) then 
       Some (line_equation (curve_left (Inf domain)) (curve_right (Inf domain)) x, ri.f_of_x x) 
     else  
       None)"    
  
theorem 
  assumes "direction_right"
  assumes "x \<in> common_setX"
  shows "ri.f_of_x x < le.f_of_x x"    
  
  
abbreviation fst_bound :: "real \<Rightarrow> real" where
  "fst_bound \<equiv> fst \<circ> (the \<circ> bounds)"  
                                    
abbreviation snd_bound :: "real \<Rightarrow> real" where
  "snd_bound \<equiv> snd \<circ> (the \<circ> bounds)"
    


  
definition inside2 :: "real2 set" where
  "inside2 \<equiv> {(x, y). x \<in> le.setX \<union> ri.setX \<and> 
                        y \<in> {min (fst_bound x) (snd_bound x) <..< max (fst_bound x) (snd_bound x)}}"  
             
 *)

end  
    
    
    
(*        
subsection "Multilane road"
  
locale multilane_road = simple_road curve_left curve_right domain 
  for curve_left and curve_right and domain +
  fixes lds :: "(real \<Rightarrow> real2) list" \<comment> \<open>lds is an abbreviation for lane dividers\<close>
  assumes lds_nonempty: "lds \<noteq> []"
  assumes sb: "ld \<in> set lds \<Longrightarrow> simple_boundary ld domain"
  assumes csx: "i < length lds \<Longrightarrow> common_setX = curve.setX (lds ! i) domain"    
  assumes bw: "i < j \<Longrightarrow> x \<in> curve.setX (lds ! i) domain \<inter> curve.setX (lds ! j) domain \<Longrightarrow> 
             simple_boundary.f_of_x (lds ! i) domain x <  simple_boundary.f_of_x (lds ! j) domain x"    
  assumes lb:"x \<in> curve.setX (last lds) domain \<inter> le.setX \<Longrightarrow> 
                                           simple_boundary.f_of_x (last lds) domain x < le.f_of_x x"  
  assumes rb:"x \<in> curve.setX (hd lds) domain \<inter> ri.setX \<Longrightarrow> 
                                             ri.f_of_x x < simple_boundary.f_of_x (hd lds) domain x"     
begin
    
definition nbr_of_lanes where
  "nbr_of_lanes \<equiv> length lds + 1"
  
\<comment> \<open>In multilane scenario the number of lanes is at least 2.\<close>  
lemma "2 \<le> nbr_of_lanes"
  unfolding nbr_of_lanes_def using lds_nonempty by (cases lds) (auto)

abbreviation ld_idx  where "ld_idx i \<equiv> lds ! i"
    
\<comment> \<open>Each adjacent lane dividers is a simple road.\<close>
theorem li:
  assumes "i < length lds - 1"
  shows "simple_road (ld_idx (i + 1)) (ld_idx i) domain"  
  unfolding simple_road_def
proof (rule conjI, rule_tac[2] conjI, unfold simple_road_axioms_def, rule_tac[3] conjI, rule_tac[4] allI, 
       rule_tac[4] impI)
  show "simple_boundary (ld_idx (i + 1)) domain" using sb[of "ld_idx (i+1)"] using assms by auto
next
  show "simple_boundary (ld_idx i) domain" using sb[of "ld_idx i"] using assms by auto
next
  fix x
  assume "x \<in> curve.setX (ld_idx (i+1)) domain \<inter> curve.setX (ld_idx i) domain"  
  with bw[of "i" "i+1" "x"] 
  show "simple_boundary.f_of_x (ld_idx i) domain x < simple_boundary.f_of_x (ld_idx (i + 1)) domain x"  
    by auto      
qed  
 
\<comment> \<open>Last lane dividers with left boundaries is a simple road too.\<close>
theorem lanel:
  "simple_road curve_left (last lds) domain"
  unfolding simple_road_def
proof (rule conjI, rule_tac[2] conjI, unfold simple_road_axioms_def, rule_tac[3] allI, 
       rule_tac[3] impI)
  show "simple_boundary curve_left domain" using le.simple_boundary_axioms by auto
next
  show "simple_boundary (last lds) domain" using sb[of "last lds"] last_in_set[OF lds_nonempty]
    by auto
next
  fix x
  assume "x \<in> le.setX \<inter> curve.setX (last lds) domain"
  with lb[of "x"] show " simple_boundary.f_of_x (last lds) domain x < le.f_of_x x" by auto   
qed
  
\<comment> \<open>First lane divider and right boundary is a simple road too.\<close>  
theorem  lane0: 
  "simple_road (hd lds) curve_right domain"
  unfolding simple_road_def
proof (rule conjI, rule_tac[2] conjI, unfold simple_road_axioms_def, rule_tac[3] allI, 
       rule_tac[3] impI)
  show "simple_boundary (hd lds) domain" using sb[of "hd lds"] hd_in_set[OF lds_nonempty]
    by auto
next
  show "simple_boundary curve_right domain" using ri.simple_boundary_axioms by auto
next
  fix x
  assume " x \<in> curve.setX (hd lds) domain \<inter> ri.setX"
  with rb[of "x"] show "ri.f_of_x x < simple_boundary.f_of_x (hd lds) domain x" by auto   
qed
  
definition drivable_lane :: "nat \<Rightarrow> real2 set" where
  "drivable_lane i \<equiv> (if i = 0 then 
                        simple_road.drivable_area (ld_idx i) curve_right domain
                      else if 0 < i \<and> i < nbr_of_lanes - 1 then 
                        simple_road.drivable_area (ld_idx i) (ld_idx (i - 1)) domain 
                      else if i = nbr_of_lanes - 1 then 
                        simple_road.drivable_area curve_left (ld_idx (i - 1)) domain 
                      else 
                        undefined)"

interpretation l0: simple_road "(hd lds)" curve_right domain using lane0 .
            
theorem l0_common_setX:
  "l0.common_setX = common_setX"   
proof -  
  from csx[of "0"] have 0: "common_setX = curve.setX (hd lds) domain" using lds_nonempty
    hd_conv_nth[OF lds_nonempty] by auto        
  hence "l0.le.setX \<inter> ri.setX = l0.le.setX" by auto
  thus ?thesis using 0 by auto      
qed    
  
theorem bw2:
  assumes "i \<le> j"
  assumes "x \<in> curve.setX (lds ! i) domain \<inter> curve.setX (lds ! j) domain"
  shows "simple_boundary.f_of_x (ld_idx i) domain x \<le> simple_boundary.f_of_x (ld_idx j) domain x"
proof (cases "i < j")
  case True
  then show ?thesis using bw[OF True assms(2)] by auto
next
  case False
  then show ?thesis using assms by auto
qed
      
theorem l0_between_setY:
  assumes "x \<in> l0.common_setX"
  shows "l0.between_setY x \<subseteq> between_setY x"
proof
  fix xa
  assume "xa \<in> l0.between_setY x"
  hence 0: "xa \<in> {(ri.f_of_x x) <..< (l0.le.f_of_x x)}" by auto
  from bw2[of "0" "length lds - 1"] 
  have "simple_boundary.f_of_x (hd lds) domain x \<le> simple_boundary.f_of_x (last lds) domain x"
    using hd_conv_nth[OF lds_nonempty] last_conv_nth[OF lds_nonempty] lds_nonempty assms csx
    by (metis (no_types, lifting) diff_less inf_left_idem l0_common_setX le0 length_greater_0_conv less_numeral_extra(1)) 
  also have "... < le.f_of_x x" using assms l0_common_setX csx lb
    last_conv_nth[OF lds_nonempty]
    by (metis (no_types, lifting) diff_less inf.right_idem inf_sup_aci(1) lds_nonempty length_greater_0_conv less_numeral_extra(1))
  finally have "l0.le.f_of_x x < le.f_of_x x"  by auto
  with 0 show "xa \<in> {(ri.f_of_x x) <..< le.f_of_x x}" by auto      
qed  
    
interpretation ll: simple_road curve_left "last lds" domain using lanel .

theorem ll_common_setX:  
  "ll.common_setX = common_setX"   
proof -  
  from csx[of "length lds - 1"] have 0: "common_setX = curve.setX (last lds) domain" using lds_nonempty
    last_conv_nth[OF lds_nonempty] by auto         
  hence "le.setX \<inter> ll.ri.setX = ll.ri.setX" by auto 
  thus ?thesis using 0 by auto
qed
  
theorem ll_between_setY:
  assumes "x \<in> ll.common_setX"
  shows "ll.between_setY x \<subseteq> between_setY x"
proof
  fix xa
  assume 0: "xa \<in> ll.between_setY x"
  from bw2[of "0" "length lds - 1"] 
  have "simple_boundary.f_of_x (hd lds) domain x \<le> simple_boundary.f_of_x (last lds) domain x"
    using hd_conv_nth[OF lds_nonempty] last_conv_nth[OF lds_nonempty] lds_nonempty assms csx
    by (metis (no_types, lifting) diff_less inf_left_idem l0_common_setX le0 length_greater_0_conv less_numeral_extra(1))
  moreover have "ri.f_of_x x < simple_boundary.f_of_x (hd lds) domain x" using rb[of "x"] assms 
    l0_common_setX ll_common_setX by auto
  ultimately have "ri.f_of_x x < ll.ri.f_of_x x" by auto
  with 0 show "xa \<in> between_setY x" by auto              
qed
    
lemma 
  assumes "i < nbr_of_lanes"  
  shows "path_connected (drivable_lane i)"
  unfolding drivable_lane_def if_splits(1)
proof (rule conjI, rule impI, rule_tac[2] impI, rule_tac[2] conjI, rule_tac[2] impI, 
       rule_tac[3] impI, rule_tac[3] conjI, rule_tac[3] impI, rule_tac[4] impI)    
  assume "i = 0"
  hence "ld_idx i = hd lds" using hd_conv_nth[OF lds_nonempty] by auto
  thus "path_connected (simple_road.drivable_area (ld_idx i) curve_right domain)"
    using l0.path_connected_drivable_area by auto    
next
  assume "0 < i \<and> i < nbr_of_lanes - 1"
  hence pos: "0 < i" and valid: "i < length lds" unfolding nbr_of_lanes_def by auto
  then interpret li: simple_road "ld_idx i" "ld_idx (i - 1)" domain using li[of "i-1"] by auto   
  show "path_connected li.drivable_area" using li.path_connected_drivable_area .
next
  assume "i = nbr_of_lanes - 1"
  hence "i = length lds" unfolding nbr_of_lanes_def by auto    
  hence "ld_idx (i - 1) = last lds" using last_conv_nth[OF lds_nonempty] by auto
  thus "path_connected (simple_road.drivable_area curve_left (ld_idx (i - 1)) domain)" 
    using ll.path_connected_drivable_area by auto
next
  assume "i \<noteq> 0"
  assume "\<not> (0 < i \<and> i < nbr_of_lanes - 1)"
  hence "0 \<ge> i \<or> i \<ge> nbr_of_lanes - 1" by auto
  with \<open>i \<noteq> 0\<close> have 0: "nbr_of_lanes - 1 \<le> i" by auto
  assume "i \<noteq> nbr_of_lanes - 1"
  with 0 have "nbr_of_lanes - 1 < i" by auto
  with assms have "False" by auto
  thus "path_connected undefined" by auto      
qed
    
lemma drivable_lane_subseteq_drivable_area:
  assumes "i < nbr_of_lanes"  
  shows "drivable_lane i \<subseteq> drivable_area"
  unfolding drivable_lane_def 
proof (split if_splits, rule conjI, rule_tac[!] impI)
  assume 0:"i = 0"  
  show "simple_road.drivable_area (ld_idx i) curve_right domain \<subseteq> drivable_area"
  proof 
    fix x
    assume "x \<in> simple_road.drivable_area (ld_idx i) curve_right domain"
    with 0 have "x \<in> l0.drivable_area" using hd_conv_nth[OF lds_nonempty] by auto
    hence 1: "fst x \<in> l0.common_setX" and 2: "snd x \<in> l0.between_setY (fst x)"
      using l0.drivable_areaD1 l0.drivable_areaD2 by auto        
    with l0_common_setX have 3: "fst x \<in> common_setX" by auto
    from 1 and 2 have "snd x \<in> between_setY (fst x)" using l0_between_setY[OF 1] by auto
    with 3 show "x \<in> drivable_area" unfolding drivable_area_def by auto            
  qed
next
  assume "i \<noteq> 0"
  show " (if 0 < i \<and> i < nbr_of_lanes - 1 then simple_road.drivable_area (ld_idx i) (ld_idx (i - 1)) domain
          else if i = nbr_of_lanes - 1 then simple_road.drivable_area curve_left (ld_idx (i - 1)) domain else undefined)
          \<subseteq> drivable_area"
  proof (split if_splits, rule conjI, rule_tac[!] impI)
    assume "0 < i \<and> i < nbr_of_lanes - 1"
    hence pos: "0 < i" and valid: "i < length lds" unfolding nbr_of_lanes_def by auto
    then interpret li: simple_road "ld_idx i" "ld_idx (i - 1)" domain using li[of "i-1"] by auto 
    show " simple_road.drivable_area (ld_idx i) (ld_idx (i - 1)) domain \<subseteq> drivable_area"      
    proof 
      fix x
      assume 4: "x \<in> li.drivable_area"
      hence 5: "fst x \<in> common_setX" using li.drivable_areaD1 csx valid by blast
      have 6: "snd x \<in> li.between_setY (fst x)" using li.drivable_areaD2[OF 4] by auto
      have "ri.f_of_x (fst x) < l0.le.f_of_x (fst x)" using rb 5 l0_common_setX by auto
      also have "... \<le> li.ri.f_of_x (fst x)" using bw2[of "0" "i-1" "fst x"] pos csx 5 valid 
        lds_nonempty hd_conv_nth[OF lds_nonempty]    
        by (metis "4" le0 length_greater_0_conv li.drivable_areaD1)          
      finally have 7:"ri.f_of_x (fst x) < li.ri.f_of_x (fst x)" by auto
      have "ll.ri.f_of_x (fst x) < le.f_of_x (fst x)" using lb 5 ll_common_setX by auto     
      moreover have "li.le.f_of_x (fst x) \<le> ll.ri.f_of_x (fst x)" using bw2[of "i" "length lds - 1" "fst x"]
        valid last_conv_nth[OF lds_nonempty] csx 5 lds_nonempty ll_common_setX
        proof -
          obtain rr :: real and rra :: real where
              f1: "ll.ri.setX = {rr..rra}"
            by (meson ll.ri.setX_closed_interval_or_empty)
          then obtain rrb :: real and rrc :: real where
            f2: "{rrb..rrc} \<inter> {rr..rra} = le.setX \<inter> ll.ri.setX"
            using le.setX_closed_interval_or_empty by blast
          then have "{rrb..rrc} \<inter> {rr..rra} = li.le.setX"
            using csx ll_common_setX valid by blast
          then have "li.le.setX \<inter> curve.setX (ld_idx (length lds - 1)) domain = {rrb..rrc} \<inter> {rr..rra}"
            using f1 by (metis (no_types) \<open>last lds = ld_idx (length lds - 1)\<close> inf.right_idem)
          then have "li.le.setX \<inter> curve.setX (ld_idx (length lds - 1)) domain = le.setX \<inter> ri.setX"
            using f2 ll_common_setX by blast
          then have f3: "fst x \<in> li.le.setX \<inter> curve.setX (ld_idx (length lds - 1)) domain"
            using "5" by blast (* > 1.0 s, timed out *)
          have f4: "\<not> length lds \<le> i"
            by (metis linorder_not_le valid)
          then have f5: "1 = length lds - i - 0 - (length lds - i - 0 - Suc 0)"
            by force
          { assume "\<not> i \<le> length lds - 1"
            then have "1 \<noteq> length lds - i"
              using f4 by (metis (no_types) diff_diff_cancel nat_le_linear)
            then have "\<not> length lds - 1 \<le> i"
              using f5 by (metis (no_types) One_nat_def cancel_ab_semigroup_add_class.diff_right_commute diff_is_0_eq' diff_zero)
            then have "i \<le> length lds - 1"
              by (metis nat_le_linear) }
          then have "li.le.f_of_x (fst x) + - 1 * simple_boundary.f_of_x (ld_idx (length lds - 1)) domain (fst x) \<le> 0"
            using f3 bw2 by force
          then show ?thesis
            by (simp add: \<open>last lds = ld_idx (length lds - 1)\<close>)
        qed
      ultimately have 8:"li.le.f_of_x (fst x) < le.f_of_x (fst x)" by auto
      with 6 and 7 have "snd x \<in> between_setY (fst x)" by auto
      with 5 show "x \<in> drivable_area" unfolding drivable_area_def by auto  
    qed
  next
    assume "\<not> (0 < i \<and> i < nbr_of_lanes - 1)"
    hence "0 \<ge> i \<or> i \<ge> nbr_of_lanes - 1" by auto
    with \<open>i \<noteq> 0\<close> have "i \<ge> nbr_of_lanes - 1" by auto                
    show "(if i = nbr_of_lanes - 1 then simple_road.drivable_area curve_left (ld_idx (i - 1)) domain else undefined) \<subseteq> drivable_area"
    proof (split if_splits, rule conjI, rule_tac[!] impI)
      assume "i = nbr_of_lanes - 1"
      hence 9: "i = length lds" unfolding nbr_of_lanes_def by auto    
      show "simple_road.drivable_area curve_left (ld_idx (i - 1)) domain \<subseteq> drivable_area"
      proof           
        fix x
        assume "x \<in> simple_road.drivable_area curve_left (ld_idx (i - 1)) domain"
        hence "x \<in> ll.drivable_area" using 9 last_conv_nth[OF lds_nonempty] by auto
        hence "fst x \<in> common_setX" using ll.drivable_areaD1 ll_common_setX by auto
        moreover have "snd x \<in> ll.between_setY (fst x)" using ll.drivable_areaD2 \<open>x \<in> ll.drivable_area\<close>
          by auto
        hence "snd x \<in> between_setY (fst x)" using ll_between_setY[of "fst x"] \<open>fst x \<in> common_setX\<close>
          ll_common_setX by auto
        with \<open>fst x \<in> common_setX\<close> show "x \<in> drivable_area" using drivable_areaI[of "fst x" "snd x"]
          by auto            
      qed
    next
      assume "i \<noteq> nbr_of_lanes - 1"
      with \<open>i \<ge> nbr_of_lanes - 1\<close> have "i > nbr_of_lanes - 1" by auto
      with assms have "False" by auto
      thus "undefined \<subseteq> drivable_area" by auto          
    qed  
  qed    
qed
  
definition boundary_points where
  "boundary_points i \<equiv> {(x,y). x \<in> curve.setX (lds ! i) domain \<and> 
                                                     y = simple_boundary.f_of_x (lds ! i) domain x}"  

lemma boundary_pointsD1:
  assumes "i < length lds"
  assumes "x \<in> boundary_points i"  
  shows "fst x \<in> common_setX"
  using assms csx unfolding boundary_points_def by auto

lemma boundary_pointsD2:
  assumes "i < length lds"
  assumes "x \<in> boundary_points i"
  shows "snd x = simple_boundary.f_of_x (lds ! i) domain (fst x)"
  using assms unfolding boundary_points_def by auto
      
theorem boundary_points_subseteq_drivable_area:
  assumes "i < length lds"
  shows "boundary_points i \<subseteq> drivable_area"
proof    
  fix x
  assume "x \<in> boundary_points i"
  with assms have fst: "fst x \<in> common_setX" and snd:"snd x = simple_boundary.f_of_x (lds ! i) domain (fst x)" 
    using boundary_pointsD1 boundary_pointsD2 by auto    
  with bw2[of "i" "length lds - 1" "fst x"] assms csx last_conv_nth[OF lds_nonempty]
  have "simple_boundary.f_of_x (ld_idx i) domain (fst x) \<le> ll.ri.f_of_x (fst x)" 
  proof -
    have f1: "0 < Suc 0"
      by (metis One_nat_def less_numeral_extra(1))
    obtain rr :: real and rra :: real where
      f2: "ll.ri.setX = {rr..rra}"
      using ll.ri.setX_closed_interval_or_empty by blast
    then obtain rrb :: real and rrc :: real where
          f3: "{rrb..rrc} \<inter> {rr..rra} = le.setX \<inter> ll.ri.setX"
      using le.setX_closed_interval_or_empty by blast
    then have "{rrb..rrc} \<inter> {rr..rra} = curve.setX (ld_idx i) domain"
      using assms csx ll_common_setX by blast
    then have "curve.setX (ld_idx i) domain \<inter> curve.setX (ld_idx (length lds - 1)) domain = {rrb..rrc} \<inter> {rr..rra}"
      using f2 by (metis (no_types) \<open>last lds = ld_idx (length lds - 1)\<close> inf.right_idem)
    then have f4: "fst x \<in> curve.setX (ld_idx i) domain \<inter> curve.setX (ld_idx (length lds - 1)) domain"
      using f3 fst ll_common_setX by blast
    have f5: "length lds - (length lds - inf i (length lds) - inf 0 (Suc 0)) = i"
      using f1 by (metis (no_types) assms diff_diff_cancel diff_zero inf.strict_order_iff less_imp_le_nat)
    have "Suc 0 \<le> length lds - inf i (length lds) - inf 0 (Suc 0)"
      by (metis One_nat_def assms diff_is_0_eq diff_zero inf.strict_order_iff less_one linorder_not_le)
    then show ?thesis
      using f5 f4 by (metis (full_types) One_nat_def \<open>\<lbrakk>i \<le> length lds - 1; fst x \<in> curve.setX (ld_idx i) domain \<inter> curve.setX (ld_idx (length lds - 1)) domain\<rbrakk> \<Longrightarrow> simple_boundary.f_of_x (ld_idx i) domain (fst x) \<le> simple_boundary.f_of_x (ld_idx (length lds - 1)) domain (fst x)\<close> \<open>last lds = ld_idx (length lds - 1)\<close> diff_le_mono2)
  qed
  also have "... < le.f_of_x (fst x)" using lb[of "fst x"] fst ll_common_setX by auto
  finally have 1: "simple_boundary.f_of_x (ld_idx i) domain (fst x) < le.f_of_x (fst x)" by auto
  with bw2[of "0" "i" "fst x"] assms csx lds_nonempty fst hd_conv_nth[OF lds_nonempty]
    have "l0.le.f_of_x (fst x) \<le> simple_boundary.f_of_x (ld_idx i) domain (fst x)" by auto
  moreover have "ri.f_of_x (fst x) < l0.le.f_of_x (fst x)" using rb[of "fst x"] fst l0_common_setX
      by auto
  ultimately have "ri.f_of_x (fst x) < simple_boundary.f_of_x (ld_idx i) domain (fst x)" by auto
  with 1 and snd have "snd x \<in> between_setY (fst x)" by auto
  with \<open>fst x \<in> common_setX\<close> show "x \<in> drivable_area" using drivable_areaI[of "fst x" "snd x"] 
    by auto
qed
  

definition partition_between where
  "partition_between x \<equiv> {l0.between_setY x, ll.between_setY x} \<union> 
    {ran . \<exists>i>0. i < length lds \<and> ran = simple_road.between_setY (ld_idx i) (ld_idx (i-1)) domain x}"  
 
lemma aux_intro:
  assumes "x \<in> A \<or> x \<in> B \<or> (\<exists>i. P i \<and> x \<in> C i)"
  shows "x \<in> \<Union>({A,B} \<union> {C'. \<exists>i. P i \<and> C' = C i})"  
  using assms by auto
      
lemma 
  assumes "x \<in> common_setX"
  shows "partition_on (between_setY x) (partition_between x)"    
proof (intro partition_onI)
  show "\<Union>partition_between x = between_setY x"
    unfolding partition_between_def
  proof (rule Set.equalityI, rule_tac[!] subsetI)
    fix xa
    assume "xa \<in> \<Union>({l0.between_setY x, ll.between_setY x} \<union>
                  {ran. \<exists>i>0. i < length lds \<and>
                   ran = {simple_boundary.f_of_x (ld_idx (i - 1)) domain x<..<simple_boundary.f_of_x (ld_idx i) domain x}})"  
    from this obtain X where "X \<in> partition_between x" and "xa \<in> X" unfolding partition_between_def 
      using Union_iff by blast
    hence "X = l0.between_setY x \<or> X = ll.between_setY x \<or> 
           X \<in> {ran. \<exists>i>0. i < length lds \<and>
                   ran = {simple_boundary.f_of_x (ld_idx (i - 1)) domain x<..<simple_boundary.f_of_x (ld_idx i) domain x}}"
      unfolding partition_between_def by auto
    from this consider \<open>X = l0.between_setY x\<close> | \<open>X = ll.between_setY x\<close> | 
              \<open>X \<in> {ran. \<exists>i>0. i < length lds \<and>
                   ran = {simple_boundary.f_of_x (ld_idx (i - 1)) domain x<..<simple_boundary.f_of_x (ld_idx i) domain x}}\<close>
      by auto
    then show "xa \<in> between_setY x"
    proof cases
      case 1
      then show ?thesis using l0_between_setY assms l0_common_setX \<open>xa \<in> X\<close> by blast
    next
      case 2
      then show ?thesis using ll_between_setY assms ll_common_setX \<open>xa \<in> X\<close> by blast
    next
      case 3
      then obtain i where X_def: "X = {simple_boundary.f_of_x (ld_idx (i-1)) domain x <..< 
                                simple_boundary.f_of_x (ld_idx i) domain x}" 
        and "i > 0" and "i < length lds" by blast
      from this interpret li: simple_road "ld_idx i" "ld_idx (i - 1)" domain using li[of "i-1"] 
        by auto
      have "li.between_setY x \<subseteq> between_setY x"
      proof   
        fix xa
        assume "xa \<in> li.between_setY x"
        have "li.le.f_of_x x \<le> ll.ri.f_of_x x" using bw2[of "i" "length lds - 1" "x"]
          using \<open>i < length lds\<close> csx[of "length lds - 1"] csx[of "i"] lds_nonempty assms
          last_conv_nth[OF lds_nonempty] by fastforce
        also have "... < le.f_of_x x" using lb[of "x"] using assms ll_common_setX by auto
        finally have temp: "li.le.f_of_x x < le.f_of_x x" by auto
        have "ri.f_of_x x < l0.le.f_of_x x" using rb[of "x"] assms l0_common_setX by auto
        also have "... \<le> li.ri.f_of_x x" using bw2[of "0" "i-1" "x"] \<open>i > 0\<close> 
          hd_conv_nth[OF lds_nonempty] csx[of "0"] lds_nonempty csx[of "i-1"] \<open>i < length lds\<close>    
          assms by auto
        finally have "ri.f_of_x x < li.ri.f_of_x x" by auto
        with temp and \<open>xa \<in> li.between_setY x\<close> show "xa \<in> between_setY x" by auto
      qed  
      with \<open>xa \<in> X\<close> and X_def show ?thesis by auto
    qed
  next          
    fix xa
    assume "xa \<in> between_setY x"
    have "xa \<in> \<Union>({l0.between_setY x, ll.between_setY x} \<union>
                  {ran. \<exists>i. (0 < i \<and> i < length lds) \<and>
                              ran = {simple_boundary.f_of_x (ld_idx (i - 1)) domain x<..<simple_boundary.f_of_x (ld_idx i) domain x}})"      
    proof (intro aux_intro)
      
    qed
  
  
    
lemma 
  assumes "x \<in> common_setX"
  assumes "y \<in> between_setY x"
  assumes "i < length_lds \<Longrightarrow> (x, y) \<notin> boundary_points i"
  assumes "y \<in> l0.between_setY x \<or> y \<in> ll.between_setY x"    
  shows "\<exists>i>0. i < length_lds \<and> y \<in> simple_road.between_setY (ld_idx i) (ld_idx (i-1)) domain x"           
proof (rule ccontr)  
  assume "\<not> (\<exists>i>0. i < length_lds \<and> y \<in> simple_road.between_setY (ld_idx i) (ld_idx (i-1)) domain x)"
  hence "\<forall>i>0. i < length_lds \<longrightarrow> y \<notin> simple_road.between_setY (ld_idx i) (ld_idx (i-1)) domain x"
    by auto
  have "y < simple_boundary.f_of_x (ld_idx 0) domain x \<or>
                      y > simple_boundary.f_of_x (ld_idx (length_lds - 1)) domain x"
  proof (rule ccontr)
    assume "\<not> (y < simple_boundary.f_of_x (ld_idx 0) domain x \<or> 
                   simple_boundary.f_of_x (ld_idx (length_lds - 1)) domain x < y)"   
    hence "y \<le> simple_boundary.f_of_x (ld_idx (length_lds - 1)) domain x \<and> 
               simple_boundary.f_of_x (ld_idx 0) domain x \<le> y" by auto
      
  qed    
qed  
    
    
\<comment> \<open>Drivable area for multilane road\<close>
definition multi_drivable_area :: "real2 set" where
  "multi_drivable_area \<equiv> 
                      (\<Union>i < nbr_of_lanes. drivable_lane i) \<union>  (\<Union>i < length lds. boundary_points i)"

theorem multi_drivable_area_alt_def:
  "multi_drivable_area = drivable_area"  
  unfolding multi_drivable_area_def
proof (rule Set.equalityI, unfold Un_subset_iff, rule conjI, unfold UN_subset_iff, rule_tac[1-2] ballI)
  fix i
  assume "i \<in> {..<nbr_of_lanes}"    
  hence "i < nbr_of_lanes" by auto
  with drivable_lane_subseteq_drivable_area[OF this] show "drivable_lane i \<subseteq> drivable_area" by simp        
next
  fix i
  assume "i \<in> {..<length lds}"
  hence "i < length lds" by auto
  with boundary_points_subseteq_drivable_area show "boundary_points i \<subseteq> drivable_area" by auto
next
  show "drivable_area \<subseteq> (\<Union>i < nbr_of_lanes. drivable_lane i) \<union>  (\<Union>i < length lds. boundary_points i)"
  proof 
    fix x
    assume "x \<in> drivable_area"
    hence fst:"fst x \<in> common_setX" and snd:"snd x \<in> between_setY (fst x)" using drivable_areaD1
      drivable_areaD2 by auto                    
  qed    
qed  
end  
*)

end  
  

  
  
  
  