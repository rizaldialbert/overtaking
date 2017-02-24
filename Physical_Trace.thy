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
  
definition mono_in :: "('a :: order \<Rightarrow> 'b :: order) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "mono_in f S \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x \<le> y \<longrightarrow> f x \<le> f y)"  

lemma strict_mono_in_mono_in: 
  "strict_mono_in f S \<Longrightarrow> mono_in f S"
  unfolding strict_mono_in_def mono_in_def by (simp add: le_less)
  
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
    
type_synonym real2 = "real \<times> real"
         
section "Trace"    
\<comment> \<open>Represent the state of a (dynamic) road user as a record.\<close>

record state = 
  position     :: "real2"        (* position vector     *)
  velocity     :: "real2"        (* velocity vector     *)
  acceleration :: "real2"        (* acceleration vector *)
  occupancy    :: "real2 set"    (* occupied space      *)

\<comment> \<open>predicate to check whether a number is the supremum in a dimension.\<close>  
definition is_sup :: "(real2 \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real2 set \<Rightarrow> bool" where
  "is_sup sel r occ \<equiv> (\<forall>p \<in> occ. sel p \<le> r)"  
  
definition is_sup_x :: "real \<Rightarrow> real2 set \<Rightarrow> bool" where
  "is_sup_x \<equiv> is_sup fst"

definition is_sup_y :: "real \<Rightarrow> real2 set \<Rightarrow> bool" where
  "is_sup_y \<equiv> is_sup snd"
        
section "Environment"

text "At the moment, we focus on highway (freeway) scenario first without fork and joints. There 
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
(*   assumes injective: "inj_on (\<lambda>(lane, s). lane s) ({curve_left, curve_right} \<times> domain)"
   assumes above: "y1 \<in> le.setY \<Longrightarrow> y2 \<in> ri.setY \<Longrightarrow> y1 > y2" \<comment> \<open>left lane is above right lane\<close>    
*) 
 assumes above': "x \<in> le.setX \<inter> ri.setX \<Longrightarrow> ri.f_of_x x < le.f_of_x x"
begin
  
abbreviation common_setX where
  "common_setX \<equiv> le.setX \<inter> ri.setX"  

lemma inverse_image_common_left: 
  "le.inv_curve_x ` common_setX \<subseteq> domain"
  using le.image_inverse  by (simp add: subset_eq)  

lemma inverse_image_common_right:
  "ri.inv_curve_x ` common_setX \<subseteq> domain"
  using ri.image_inverse by (simp add:subset_eq)
    
abbreviation between_setY where
  "between_setY x \<equiv> {(ri.f_of_x x) <..< (le.f_of_x x)}"

lemma convex_common_setX: "convex (common_setX)"
  using le.convex_setX  ri.convex_setX convex_Int by auto

lemma compact_common_setX: "compact (common_setX)"
  using le.compact_setX ri.compact_setX le.closed_setX compact_Int
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
  "common_setX \<noteq> {} \<Longrightarrow> lb_x \<in> common_setX"
  using compact_common_setX bdd_below_common  closed_contains_Inf
  unfolding lb_x_def compact_eq_bounded_closed
  by meson  
        
definition ub_x where
  "ub_x \<equiv> Sup common_setX"
  
lemma common_contains_ub: 
  "common_setX \<noteq> {} \<Longrightarrow> ub_x \<in> common_setX"  
  using compact_common_setX bdd_above_common closed_contains_Sup
  unfolding ub_x_def compact_eq_bounded_closed
  by meson  
        
lemma between_setY_nonempty: "x \<in> common_setX \<Longrightarrow> between_setY x \<noteq> {}"
proof -  
  assume "x \<in> common_setX"
  with above' have "ri.f_of_x x < le.f_of_x x" 
    using le.domain_and_range_f_of_x ri.domain_and_range_f_of_x by auto
  from Rats_dense_in_real[OF this] obtain r where "r \<in> between_setY x" 
    using greaterThanLessThan_iff by blast      
  thus "between_setY x \<noteq> {}" using ex_in_conv by auto    
qed     
    
definition drivable_area :: "real2 set" where
  "drivable_area \<equiv> {(x,y). x \<in> common_setX \<and> y \<in> between_setY x}"  
  
lemma drivable_areaI:
  assumes "x \<in> common_setX"
  assumes "y \<in> between_setY x"
  shows "(x,y) \<in> drivable_area"
using assms unfolding drivable_area_def by auto
      
lemma drivable_areaD1: "z \<in> drivable_area \<Longrightarrow> fst z \<in> common_setX"
  by (auto simp add:drivable_area_def)
    
lemma drivable_areaD2: "z \<in> drivable_area \<Longrightarrow> snd z \<in> between_setY (fst z)"
  by (auto simp add:drivable_area_def)
       
lemma drivable_area_alt_def: 
  "drivable_area = Sigma common_setX between_setY"
proof (unfold set_eq_subset, rule conjI, rule_tac [!] subsetI)  
  fix x
  assume "x \<in> drivable_area"
  hence 0: "fst x \<in> common_setX \<and> snd x \<in> between_setY (fst x)"
    unfolding drivable_area_def by auto
  have "(fst x, snd x) \<in> Sigma common_setX between_setY"    
    apply (rule SigmaI)  using 0 by auto
  thus "x \<in> Sigma common_setX between_setY"
    using surjective_pairing by auto
next
  fix x
  assume 1: "x \<in> Sigma common_setX between_setY"
  show "x \<in> drivable_area"
  proof (rule SigmaE2[of "fst x" "snd x" "common_setX" "between_setY"])    
    from 1 show "(fst x, snd x) \<in> Sigma common_setX between_setY"
      using surjective_pairing by auto
  next
    assume "fst x \<in> common_setX" and "snd x \<in> between_setY (fst x)"
    thus "x \<in> drivable_area" unfolding drivable_area_def by auto
  qed
qed  
    
theorem drivable_area_nonempty: "common_setX \<noteq> {} \<Longrightarrow> drivable_area \<noteq> {}"  
  unfolding drivable_area_alt_def
  using Sigma_empty_iff between_setY_nonempty
  by (smt disjoint_iff_not_equal inf_left_idem)

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
proof -
  from snd_path_image have "snd ` (path_image g) \<subseteq> {lb .. ub}"
    using assms by auto
  moreover from assms(2-3) have "ri.f_of_x (fst z1) < snd z1" and "snd z2 < le.f_of_x (fst z2)"
    unfolding drivable_area_def by auto
  moreover from assms(2-3) have "ri.f_of_x (fst z2) < snd z2" and "snd z1 < le.f_of_x (fst z1)"
    unfolding drivable_area_def by auto
  ultimately show ?thesis using assms(1) unfolding lb_def ub_def     
    by fastforce
qed  
    
definition midcurve_points :: "real2 set" where
  "midcurve_points \<equiv> {(x,y) . x \<in> common_setX \<and> y = (le.f_of_x x + ri.f_of_x x) / 2}"
  
lemma midcurve_pointsI:
  assumes "x \<in> common_setX"
  assumes "y =(le.f_of_x x + ri.f_of_x x) * inverse 2 "
  shows "(x, y) \<in> midcurve_points"
  unfolding midcurve_points_def using assms by auto    
  
lemma midcurve_points_inside_drivable_area: 
  "midcurve_points \<subseteq> drivable_area"
proof (rule subsetI, rename_tac "z")
  fix z :: real2
  assume 0: "z \<in> midcurve_points"
  from this obtain x y where 1: "z = (x,y)" by fastforce
  with 0 have 2: "x \<in> common_setX \<and> y = (le.f_of_x x + ri.f_of_x x) / 2" 
    unfolding midcurve_points_def by auto
  hence "y \<in> between_setY x"
    using simple_road.between_setY_nonempty simple_road_axioms by fastforce
  with 2 have "z \<in> Sigma common_setX between_setY" using 1 by auto
  thus "z \<in> drivable_area" using drivable_area_alt_def by auto      
qed

definition midcurve_fun :: "real \<Rightarrow> real" where
  "midcurve_fun x = (le.f_of_x x + ri.f_of_x x) * inverse 2"  
  
lemma midcurve_fun_midcurve_points:
  "x \<in> common_setX \<Longrightarrow> (x, midcurve_fun x) \<in> midcurve_points"
  using mem_Collect_eq midcurve_fun_def midcurve_points_def by auto

lemma midcurve_fun_inside_drivable_area:
  "x \<in> common_setX \<Longrightarrow> (x, midcurve_fun x) \<in> drivable_area"
  using midcurve_fun_midcurve_points midcurve_points_inside_drivable_area
  by auto
          
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
    using le.cont_f_of_x assms continuous_on_subset by auto
next
  from convex_common_setX have "{start .. end} \<subseteq> common_setX"
    by (metis assms atLeastAtMost_iff atLeastatMost_subset_iff common_setX_interval)
  thus "continuous_on {start .. end} ri.f_of_x"
    using ri.cont_f_of_x assms continuous_on_subset by auto
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
  assumes "start \<in> common_setX" and "end \<in> common_setX"      
  shows "rep_mid start end s \<in> common_setX"
proof (cases "start \<le> end")
  case True
  hence "rep_mid start end ` {0 .. 1} = {start .. end}"
    using image_rep_mid[OF True] by auto
  also have "... \<subseteq> common_setX" using convex_common_setX assms(2 - 3) 
    by (metis atLeastAtMost_iff atLeastatMost_subset_iff common_setX_interval)
  finally show "rep_mid start end s \<in> common_setX" using assms by auto    
next
  case False
  hence False2: "end \<le> start" by auto
  hence "rep_mid start end ` {0 .. 1} = {end .. start}" 
    using image_rep_mid2[OF False2] by auto
  also have "... \<subseteq> common_setX" using convex_common_setX assms(2 - 3)
    by (metis atLeastAtMost_iff atLeastatMost_subset_iff common_setX_interval)
  finally show "rep_mid start end s \<in> common_setX" using assms by auto      
qed
  
lemma mid_path_in_midcurve_points:
  assumes "s \<in> {0 .. 1}"
  assumes "start \<in> common_setX" and "end \<in> common_setX"  
  shows "mid_path start end s \<in> midcurve_points"
  unfolding mid_path_def midcurve_fun_def using rep_mid_in_common_setX[OF assms]
  by (rule midcurve_pointsI) (auto)
    
lemma mid_path_in_midcurve_points2:
  assumes "x1 \<in> common_setX" and "x2 \<in> common_setX"
  shows "mid_path x1 x2 ` {0 .. 1} \<subseteq> midcurve_points"
  using assms mid_path_in_midcurve_points
  unfolding mid_path_def by auto
    
lemma path_image_mid_path:
  assumes "x1 \<in> common_setX" and "x2 \<in> common_setX"  
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
  note z1z2 = z1 z1_d z2 z2_d drivable_areaD1     
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
      with z2 have 2: "x \<in> common_setX" using drivable_areaD1[OF z2_d] by auto           
      moreover from snd_path_image'[of "z1" "z2"] have "y \<in> between_setY x"
        using z1_d z2_d z1 z2 True 0 1 g_def \<open>x = x2\<close> image_subset_iff by auto          
      ultimately show "case z of (x,y) \<Rightarrow> x \<in> common_setX \<and> y \<in> between_setY x"           
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
      with z1 have 2: "x \<in> common_setX" using drivable_areaD1[OF z1_d] by auto           
      moreover from snd_path_image'[of "z1" "(x1, midcurve_fun x1)"] have "y \<in> between_setY x1"
        using z1_d z1 0 1 g1_def \<open>x = x1\<close> image_subset_iff midcurve_fun_inside_drivable_area
        calculation by auto
      ultimately show "case z of (x,y) \<Rightarrow> x \<in> common_setX \<and> y \<in> between_setY x"           
        using 1 \<open>x = x1\<close> by auto
    next
      fix z
      assume "z \<in> path_image g2"
      hence "z \<in> drivable_area" unfolding g2_def
        using path_image_mid_path[of "x1" "x2"] using z1z2 by auto
      thus "case z of (x,y) \<Rightarrow> x \<in> common_setX \<and> y \<in> between_setY x"  
        unfolding drivable_area_alt_def by auto
    next
      fix z
      assume 0: "z \<in> path_image g3"
      then obtain x y where 1:"z = (x, y)" unfolding g3_def by fastforce
      from fst_path_image[of "z2" "(x2, midcurve_fun x2)"] have "fst ` (path_image g3) = {x2}"
        unfolding g3_def using z2 by auto
      with 0 and 1 have "x = x2" by (metis Domain.DomainI Domain_fst singletonD)
      with z2 have 2: "x \<in> common_setX" using drivable_areaD1[OF z2_d] by auto
      moreover from snd_path_image'[of "z2" "(x2, midcurve_fun x2)"] have "y \<in> between_setY x2"
        using z2_d z2 0 1 g3_def \<open>x = x2\<close> image_subset_iff midcurve_fun_inside_drivable_area
        by (metis (no_types, lifting) calculation fst_conv snd_conv snd_path_image')
      ultimately show "case z of (x,y) \<Rightarrow> x \<in> common_setX \<and> y \<in> between_setY x" 
        using 1 \<open>x=x2\<close> by auto
    qed      
    thus ?thesis using \<open>path g\<close> \<open>pathstart g = z1\<close> \<open>pathfinish g = z2\<close> by auto
  qed      
qed        
end  
  
        
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
proof (rule conjI, rule_tac[2] conjI, unfold simple_road_axioms_def, rule_tac[3] allI, 
       rule_tac[3] impI)
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
  
(*
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
*)  
end  
end  
  

  
  
  
  