theory Safe_Distance_Auxiliarities
imports
  "HOL-Analysis.Analysis" (*set prover to HOL-Analysis*)
  "HOL-Library.Float"
begin

subsection \<open>TODO: Taken from \<open>ODE_Auxiliarities\<close>, move to distribution and remove from ODE!\<close>

lemma not_in_closure_trivial_limitI:
  "x \<notin> closure s \<Longrightarrow> trivial_limit (at x within s)"
  using not_trivial_limit_within[of x s]
  by auto (metis Diff_empty Diff_insert0 closure_subset contra_subsetD)

lemma tendsto_If:
  assumes tendsto:
    "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
      (f \<longlongrightarrow> l x) (at x within s \<union> (closure s \<inter> closure t))"
    "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
      (g \<longlongrightarrow> l x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) \<longlongrightarrow> l x) (at x within s \<union> t)"
proof (rule Lim_Un, safe intro!: topological_tendstoI)
  fix S::"'b set"
  assume S: "open S"
  assume l: "l x \<in> S"
  let ?thesis =
    "\<lambda>t. eventually (\<lambda>x. (if x \<in> s then f x else g x) \<in> S) (at x within t)"
  {
    assume x: "x \<in> s" hence "x \<in> s \<union> (closure s \<inter> closure t)" by auto
    from topological_tendstoD[OF tendsto(1)[OF this] S l]
    have "?thesis s" unfolding eventually_at_filter
      by eventually_elim auto
  } moreover {
    assume "x \<notin> closure s"
    then have "?thesis s"
      by (metis (no_types) not_in_closure_trivial_limitI trivial_limit_eventually)
  } moreover {
    assume s: "x \<in> closure s" "x \<notin> s"
    hence t: "x \<in> t" "x \<in> closure t"
      using assms closure_subset[of t] by auto
    from s t have c1: "x \<in> s \<union> (closure s \<inter> closure t)"
      and c2: "x \<in> t \<union> (closure s \<inter> closure t)"by auto
    from topological_tendstoD[OF tendsto(1)[OF c1] S l]
      topological_tendstoD[OF tendsto(2)[OF c2] S l]
    have "?thesis s"
      unfolding eventually_at_filter
      by eventually_elim auto
  } ultimately show "?thesis s" by blast
  {
    assume x: "x \<in> closure s" "x \<in> closure t"
    hence c1: "x \<in> s \<union> (closure s \<inter> closure t)"
      and c2: "x \<in> t \<union> (closure s \<inter> closure t)"
      by auto
    from topological_tendstoD[OF tendsto(1)[OF c1] S l]
      topological_tendstoD[OF tendsto(2)[OF c2] S l]
    have "?thesis t" unfolding eventually_at_filter
      by eventually_elim auto
  } moreover {
    assume "x \<notin> closure t"
    then have "?thesis t"
      by (metis (no_types) not_in_closure_trivial_limitI trivial_limit_eventually)
  } moreover {
    assume c: "x \<notin> closure s"
    hence c': "x \<in> t \<union> (closure s \<inter> closure t)"
      using assms closure_subset[of s]
      by auto
    from c have "eventually (\<lambda>x. x \<in> - closure s) (at x within t)"
      by (intro topological_tendstoD) auto
    hence "?thesis t"
      using topological_tendstoD[OF tendsto(2)[OF c'] S l] closure_subset[of s]
      unfolding eventually_at_filter
      by eventually_elim (auto; metis closure_subset contra_subsetD)
  } ultimately show "?thesis t" by blast
qed

lemma has_derivative_within_If_eq:
  "((\<lambda>x. if P x then f x else g x) has_derivative f') (at x within s) =
    (bounded_linear f' \<and>
     ((\<lambda>y.(if P y then (f y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)
           else (g y - ((if P x then f x else g x) + f' (y - x)))/\<^sub>R norm (y - x)))
      \<longlongrightarrow> 0) (at x within s))"
  (is "_ = (_ \<and> (?if \<longlongrightarrow> 0) _)")
proof -
  have "(\<lambda>y. (1 / norm (y - x)) *\<^sub>R
           ((if P y then f y else g y) -
            ((if P x then f x else g x) + f' (y - x)))) = ?if"
    by (auto simp: inverse_eq_divide)
  thus ?thesis by (auto simp: has_derivative_within)
qed

lemma has_derivative_If:
  assumes f': "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (f has_derivative f') (at x within s \<union> (closure s \<inter> closure t))"
  assumes g': "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (g has_derivative g') (at x within t \<union> (closure s \<inter> closure t))"
  assumes connect: "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f' = g'"
  assumes x_in: "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_derivative
      (if x \<in> s then f' else g')) (at x within (s \<union> t))"
proof -
  from f' x_in interpret f': bounded_linear "if x \<in> s then f' else (\<lambda>x. 0)"
    by (auto simp add: has_derivative_within)
  from g' interpret g': bounded_linear "if x \<in> t then g' else (\<lambda>x. 0)"
    by (auto simp add: has_derivative_within)
  have bl: "bounded_linear (if x \<in> s then f' else g')"
    using f'.scaleR f'.bounded f'.add g'.scaleR g'.bounded g'.add x_in
    by (unfold_locales; force)
  show ?thesis
    using f' g' closure_subset[of t] closure_subset[of s]
    unfolding has_derivative_within_If_eq
    by (intro conjI bl tendsto_If x_in)
      (auto simp: has_derivative_within inverse_eq_divide connect connect' set_mp)
qed

lemma has_vector_derivative_If:
  assumes x_in: "x \<in> s \<union> t"
  assumes "u = s \<union> t"
  assumes f': "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (f has_vector_derivative f') (at x within s \<union> (closure s \<inter> closure t))"
  assumes g': "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
    (g has_vector_derivative g') (at x within t \<union> (closure s \<inter> closure t))"
  assumes connect: "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> closure s \<Longrightarrow> x \<in> closure t \<Longrightarrow> f' = g'"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_vector_derivative
    (if x \<in> s then f' else g')) (at x within u)"
  unfolding has_vector_derivative_def assms
  using x_in
  apply (intro has_derivative_If[THEN has_derivative_eq_rhs])
       apply (rule f'[unfolded has_vector_derivative_def]; assumption)
      apply (rule g'[unfolded has_vector_derivative_def]; assumption)
  by (auto simp: assms)

lemma has_derivative_If_in_closed:
  assumes f':"x \<in> s \<Longrightarrow> (f has_derivative f') (at x within s)"
  assumes g':"x \<in> t \<Longrightarrow> (g has_derivative g') (at x within t)"
  assumes connect: "x \<in> s \<inter> t \<Longrightarrow> f x = g x" "x \<in> s \<inter> t \<Longrightarrow> f' = g'"
  assumes "closed t" "closed s" "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_derivative
    (if x \<in> s then f' else g')) (at x within (s \<union> t))"
  using assms
  by (intro has_derivative_If) (auto simp: Int_lower2 Un_absorb2)

lemma has_derivative_If_containing_closures:
  assumes f': "x \<in> s \<Longrightarrow> (f has_derivative f') (at x within s)"
  assumes g': "x \<in> t \<Longrightarrow> (g has_derivative g') (at x within t)"
  assumes connect: "x \<in> s \<Longrightarrow> x \<in> t \<Longrightarrow> f x = g x"
  assumes connect': "x \<in> s \<Longrightarrow> x \<in> t \<Longrightarrow> f' = g'"
  assumes x_in: "x \<in> s \<union> t"
  assumes contains: "closure s \<inter> closure t \<subseteq> s" "closure s \<inter> closure t \<subseteq> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) has_derivative
    (if x \<in> s then f' else g')) (at x within (s \<union> t))"
  using assms
  apply (intro has_derivative_If)
  by (auto elim: sup.orderE, (metis subset_eq sup.orderE Int_iff)+)

lemma has_derivative_transform:
  assumes "x \<in> s" "\<And>x. x \<in> s \<Longrightarrow> g x = f x"
  assumes "(f has_derivative f') (at x within s)"
  shows "(g has_derivative f') (at x within s)"
  using assms
  by (intro has_derivative_transform_within[OF _ zero_less_one, where g=g]) auto


subsection \<open>Float\<close>

text \<open>division with fixed precision (in contrast to @{term real_divr}, @{term real_divl})\<close>

definition real_div_down::"nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real"
  where "real_div_down p i j = truncate_down (Suc p) (i / j)"

definition real_div_up::"nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real"
  where "real_div_up p i j = truncate_up (Suc p) (i / j)"

context includes float.lifting begin

lift_definition float_div_down::"nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float" is real_div_down
  by (simp add: real_div_down_def)

lift_definition float_div_up::"nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> float" is real_div_up
  by (simp add: real_div_up_def)

end

lemma floor_log_divide_eq:
  assumes "i > 0" "j > 0" "p > 1"
  shows "\<lfloor>log p (i / j)\<rfloor> = floor (log p i) - floor (log p j) -
      (if i \<ge> j * p powr (floor (log p i) - floor (log p j)) then 0 else 1)"
proof -
  let ?l = "log p"
  let ?fl = "\<lambda>x. floor (?l x)"
  have "\<lfloor>?l (i / j)\<rfloor> = \<lfloor>?l i - ?l j\<rfloor>" using assms
    by (auto simp: log_divide)
  also have "\<dots> = floor (real_of_int (?fl i - ?fl j) + (?l i - ?fl i - (?l j - ?fl j)))"
    (is "_ = floor (_ + ?r)")
    by (simp add: algebra_simps)
  also note floor_add2
  also note \<open>p > 1\<close>
  note powr = powr_le_cancel_iff[symmetric, OF \<open>1 < p\<close>, THEN iffD2]
  note powr_strict = powr_less_cancel_iff[symmetric, OF \<open>1 < p\<close>, THEN iffD2]
  have "floor ?r = (if i \<ge> j * p powr (?fl i - ?fl j) then 0 else -1)" (is "_ = ?if")
    using assms
    by (linarith |
      auto
        intro!: floor_eq2
        intro: powr_strict powr
        simp: powr_diff powr_add divide_simps algebra_simps bitlen_def)+
  finally
  show ?thesis by simp
qed

lemma compute_float_div_up[code]: "float_div_up p i j = - float_div_down p (-i) j"
  including float.lifting
  by transfer (simp add: real_div_up_def real_div_down_def truncate_up_eq_truncate_down)

lemma compute_float_div_down[code]:
  "float_div_down prec m1 m2 = lapprox_rat (Suc prec) m1 m2"
  including float.lifting
  apply transfer
  unfolding real_div_down_def ..

end
