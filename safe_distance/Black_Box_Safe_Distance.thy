theory Black_Box_Safe_Distance
imports Complex_Main
        "./Safe_Distance_Isar"
        "./Hybrid_Trace"
begin

type_synonym 'a tuple6 = "'a*'a*'a*'a*'a*'a"
type_synonym ivl = "float * float"

definition real_ivl_of_real::"nat \<Rightarrow> real \<Rightarrow> (real * real)" where
  "real_ivl_of_real p x = (truncate_down (Suc p) x, truncate_up (Suc p) x)"

hide_const (open) Fraction_Field.Fract

context includes float.lifting begin

lift_definition float_ivl_of_real::"nat \<Rightarrow> real \<Rightarrow> ivl" is real_ivl_of_real
  by (auto simp: real_ivl_of_real_def)

end

lemma real_of_rat_Fract[simp]: "real_of_rat (Fract a b) = a / b"
by (simp add: Fract_of_int_quotient of_rat_divide)

lemma [code]: "float_ivl_of_real p (Ratreal r) =
  (let (a, b) = quotient_of r in
  (float_div_down p a b, float_div_up p a b))"
  including float.lifting
  apply transfer
  apply (auto split: prod.split simp: real_ivl_of_real_def real_div_down_def real_div_up_def)
  apply (metis of_rat_divide of_rat_of_int_eq quotient_of_div of_int_def)
  apply (metis of_rat_divide of_rat_of_int_eq quotient_of_div of_int_def)
  done

text \<open>
This theory is about formalising the safe distance rule. The safe distance rule is obtained
from Vienna Convention which basically states the following thing.

  ``The car at all times must maintain a safe distance towards the vehicle in front of it, 
    such that whenever the vehicle in front and the ego vehicle apply maximum deceleration, 
    there will not be a collision.''

To formalise this safe distance rule we have to define first what is a safe distance. 
To define this safe distance, we have to model the physics of the movement of the vehicle. 
The following model is sufficient. 

  \<open>s = s\<^sub>0 + v\<^sub>0 * t + 1 / 2 * a\<^sub>0 * t\<^sup>2\<close>

The exact mathematical derivation of safe distance can be seen in theory \<open>Safe_Distance_Isar\<close>.

Another assumptions in this model are :
  1) Both vehicles are assumed to be point mass. The exact location of the ego vehicle 
     is the frontmost occupancy of the ego vehicle. Similarly for the other vehicle, 
     its exact location is the rearmost occupancy of the other vehicle. 

  2) Both cars can never drive backward.
\<close>

text \<open>
  There are only two important variables in this scenario : position in x-axis and speed.    
\<close>
datatype variable = position | speed | max_dec

text \<open>
  There are two relevant traffic participants: ego vehicle and the closest vehicle in front
  of the ego vehicle. We make "Ego" and "Other" as constructor for discrete variables.
\<close>
datatype type  = ego | other

text \<open>Relevant variables for this scenario is the product of these two types\<close>
type_synonym var = "type \<times> variable"

text \<open>Define a weaker type of trace which consists of discrete jumps only\<close>
type_synonym ('dv, 'v) discrete_trace = "('dv, 'v)jumps list"

text \<open>function to evaluate discrete trace for specific variable\<close>
fun eval_var :: "(var, real) discrete_trace \<Rightarrow> var \<Rightarrow> real list" where
"eval_var js v = map (\<lambda>j . j v) js"

fun nonneg_res :: "real list \<Rightarrow> bool" where
"nonneg_res rs = fold conj (map (\<lambda>r . 0 \<le> r) rs) True"

fun pos_res :: "real list \<Rightarrow> bool" where
"pos_res rs = fold conj (map (\<lambda>r . 0 < r) rs) True"

fun neg_res :: "real list \<Rightarrow> bool" where
"neg_res rs = fold conj (map (\<lambda>r . r < 0) rs) True"

text \<open>Predicate to ensure that the variable in the trace is always nonnegative\<close>
fun nonneg_data :: "(var, real) discrete_trace \<Rightarrow> var \<Rightarrow> bool" where
"nonneg_data js v = nonneg_res (eval_var js v)"

fun neg_data :: "(var, real) discrete_trace \<Rightarrow> var \<Rightarrow> bool" where
"neg_data js v = neg_res (eval_var js v)"

text \<open>Predicate to check that the position of the other vehicle is always in front of 
   the position of ego vehicle.\<close>
fun always_in_front :: "(var, real) discrete_trace \<Rightarrow> bool" where
"always_in_front js = 
  (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
       rs = map (\<lambda>(x, y). x - y) zs in
       pos_res rs)"

definition no_collision_jumps :: "(var, real) jumps \<Rightarrow> bool" where
"no_collision_jumps j \<equiv> (let s\<^sub>e = j (ego, position); v\<^sub>e = j (ego, speed); a\<^sub>e = j (ego, max_dec);
                             s\<^sub>o = j (other, position); v\<^sub>o = j (other, speed); a\<^sub>o = j (other, max_dec) in
                                   \<not> (\<exists>t \<in> {t. 0 \<le> t} . movement.s a\<^sub>e v\<^sub>e s\<^sub>e t = 
                                                         movement.s a\<^sub>o v\<^sub>o s\<^sub>o t))"

fun no_collision_trace :: "(var, real) discrete_trace \<Rightarrow> bool" where
"no_collision_trace js =  fold conj (map no_collision_jumps js) True"

lemma false_fold_conj: "fold conj as False = False"
proof (induct as)
  show "fold conj [] False = False" by auto
next
  fix a as
  assume asm: "fold conj as False = False"
  have "fold conj (a # as) False = (fold conj as \<circ> conj a) False" by simp
  also have "... = fold conj as (a \<and> False)" by simp
  also have "... = fold conj as False" by simp
  finally show "fold conj (a # as) False = False" using asm by simp  
qed

lemma distrib_fold_conj:"(fold conj (a # as) init) = (a \<and> (fold conj as) init)"
proof -
  have "fold conj (a # as) init = (fold conj as \<circ> conj a) init" by (simp)
  also have "... = fold conj as (a \<and> init)" by simp
  also have "... = (a \<and> (fold conj as init))"
    proof (cases a)
      assume a
      hence 0: "fold conj as (a \<and> init) = fold conj as init" by simp
      from `a` have 1: "(a \<and> (fold conj as init)) = (fold conj as init)" by simp
      with 0 show ?thesis by simp
    next
      assume "\<not> a"
      hence 0: "fold conj as (a \<and> init) = fold conj as False" by simp
      also have "... = False" using false_fold_conj by simp
      also have "... = (a \<and> fold conj as init)" using `\<not> a` by simp
      finally show ?thesis by simp      
    qed
  finally show ?thesis by simp
qed

lemma distrib_no_collision_trace: 
"no_collision_trace (j # js) =  (no_collision_jumps j \<and> no_collision_trace js)"
proof -
  have "no_collision_trace  (j # js) = fold conj (map no_collision_jumps (j # js)) True"  
  by (simp add:no_collision_trace.induct)
  also have "... = fold conj (no_collision_jumps j # (map no_collision_jumps js)) True" by simp
  also have "... = (no_collision_jumps j \<and> (fold conj (map no_collision_jumps js) True))"
  using distrib_fold_conj by metis
  finally show ?thesis by simp
qed


lemma nonneg_data_closed: "nonneg_data (j # js) v = ((0 \<le> j v) \<and> nonneg_data js v)"
proof -
  have "nonneg_data (j # js) v = nonneg_res (eval_var (j # js) v)" using nonneg_data.simps by simp
  also have "... = nonneg_res (map (\<lambda>j . j v) (j # js))" using eval_var.simps by simp
  also have "... = nonneg_res (j v # map (\<lambda>j . j v) js)" by simp
  also have "... = fold conj (map (\<lambda>r. 0 \<le> r) (j v # map (\<lambda>j . j v) js)) True" using nonneg_res.simps by simp
  also have "... = fold conj ((0 \<le> j v) # map (\<lambda>r. 0 \<le> r) (map (\<lambda>j . j v) js)) True" by simp
  also have "... = ((0 \<le> j v) \<and> fold conj (map (\<lambda>r . 0 \<le> r) (map (\<lambda>j . j v) js)) True)" by (metis distrib_fold_conj)
  also have "... = ((0 \<le> j v) \<and> nonneg_res (map (\<lambda>j . j v) js))" using nonneg_res.simps by simp
  also have "... = ((0 \<le> j v) \<and> nonneg_res (eval_var js v))" using eval_var.simps by simp
  also have "... = ((0 \<le> j v) \<and> nonneg_data js v)" using nonneg_data.simps by simp
  finally show ?thesis by simp
qed

lemma neg_data_closed: "neg_data (j # js) v = ((j v < 0) \<and> neg_data js v)"
proof -
  have "neg_data (j # js) v = neg_res (eval_var (j # js) v)" using neg_data.simps by simp
  also have "... = neg_res (map (\<lambda>j . j v) (j # js))" using eval_var.simps by simp
  also have "... = fold conj (map (\<lambda>r. r < 0) (j v # map (\<lambda>j. j v) js)) True" using neg_res.simps by simp
  also have "... = fold conj ((j v < 0) # map (\<lambda>r. r < 0) (map (\<lambda>j. j v) js)) True" by simp
  also have "... = ((j v < 0) \<and> fold conj (map (\<lambda>r . r < 0) (map (\<lambda>j . j v) js)) True)" by (metis distrib_fold_conj)
  also have "... = ((j v < 0) \<and> neg_res (map (\<lambda>j . j v) js))" using nonneg_res.simps by simp
  also have "... = ((j v < 0) \<and> neg_res (eval_var js v))" using eval_var.simps by simp
  also have "... = ((j v < 0) \<and> neg_data js v)" using nonneg_data.simps by simp
  finally show ?thesis by simp
qed


lemma always_in_front_closed: "always_in_front (j # js) = 
                               ((0 < j (other, position) - j (ego, position)) \<and> always_in_front js)"
proof -
  have "always_in_front (j # js) = 
         (let zs = zip (eval_var (j # js) (other, position)) (eval_var (j # js) (ego, position)); 
              rs = map (\<lambda>(x, y). x - y) zs in
              pos_res rs)" using always_in_front.simps by simp
  also have "... = (let zs = zip (j (other, position) # eval_var js (other, position)) 
                       (j (ego, position)   # eval_var js (ego, position))  ;
                       rs = map (\<lambda>(x, y). x - y) zs in
                       pos_res rs)" using eval_var.simps by simp
  also have "... = (let zs = (j (other, position), j (ego, position)) # zip (eval_var js (other, position))
                                                                  (eval_var js (ego, position));
                        rs = map (\<lambda>(x, y). x - y) zs in
                        pos_res rs)" by simp
  also have "... = (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
                        z  = (j (other, position), j (ego, position)); 
                       rs  = map (\<lambda>(x, y). x - y) (z # zs) in 
                       pos_res rs)" by simp
  also have "... = (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
                        z  = (j (other, position), j (ego, position)); 
                       rs  = ((\<lambda>(x, y). x - y) z) # map (\<lambda>(x, y). x - y) zs  in 
                       pos_res rs)" by simp
  also have "... = (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
                        z  = (j (other, position), j (ego, position)); 
                        r  = ((\<lambda>(x, y). x - y) z); 
                        rs = map (\<lambda>(x, y). x - y) zs  in 
                        pos_res (r # rs))" by simp
  also have "... = (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
                        z  = (j (other, position), j (ego, position)); 
                        r  = ((\<lambda>(x, y). x - y) z); 
                        rs = map (\<lambda>(x, y). x - y) zs  in 
                        fold conj (map (\<lambda>r . 0 < r) (r # rs)) True)" by simp
  also have "... = (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
                        z  = (j (other, position), j (ego, position)); 
                        r  = ((\<lambda>(x, y). x - y) z); 
                        rs = map (\<lambda>(x, y). x - y) zs  in 
                        fold conj ((0 < r) # map (\<lambda>r . 0 < r) rs) True)" by simp
  also have "... = (let zs = zip (eval_var js (other, position)) (eval_var js (ego, position)); 
                        z  = (j (other, position), j (ego, position)); 
                        r  = ((\<lambda>(x, y). x - y) z); 
                        rs = map (\<lambda>(x, y). x - y) zs  in 
                        (0 < r) \<and> fold conj (map (\<lambda>r . 0 < r) rs) True)" using distrib_fold_conj by metis
  thus ?thesis by simp
qed
                                                     
definition s\<^sub>e :: "(var, real) jumps \<Rightarrow> real" where
"s\<^sub>e j \<equiv> j (ego, position)"

definition s\<^sub>o :: "(var, real) jumps \<Rightarrow> real" where
"s\<^sub>o j \<equiv> j (other, position)"

definition v\<^sub>e :: "(var, real) jumps \<Rightarrow> real" where
"v\<^sub>e j \<equiv> j (ego, speed)"

definition v\<^sub>o :: "(var, real) jumps \<Rightarrow> real" where
"v\<^sub>o j \<equiv> j (other, speed)"

definition a\<^sub>e :: "(var, real) jumps \<Rightarrow> real" where
"a\<^sub>e j \<equiv> j (ego, max_dec)"

definition a\<^sub>o :: "(var, real) jumps \<Rightarrow> real" where
"a\<^sub>o j \<equiv> j (other, max_dec)"

fun check_bb_safe_dist :: "(var, real) discrete_trace \<Rightarrow> bool" where
"check_bb_safe_dist [] = True" | 
"check_bb_safe_dist (j # js) = (let s\<^sub>e = j (ego, position); v\<^sub>e = j (ego, speed); a\<^sub>e = j (ego, max_dec); 
                             s\<^sub>o = j (other, position); v\<^sub>o = j (other, speed); a\<^sub>o = j (other, max_dec) in 
                             checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<and> check_bb_safe_dist js)"

lemma check_precond_imp_safe_distance:
  assumes "check_precond a b c d e f"
  shows "safe_distance c b a f e d"
  using assms unfolding check_precond_def
  by unfold_locales auto

lemma checker_imp_check_precond:
  assumes "checker a b c d e f"
  shows  "check_precond a b c d e f"
  using assms by (auto simp: checker_def Let_def)

lemma nonneg_data_Cons:
  assumes "nonneg_data xs a"
  assumes "0 \<le> x a"
  shows "nonneg_data (x#xs) a"
  using assms by auto

lemma neg_data_Cons:
  assumes "neg_data xs a"
  assumes "x a < 0" 
  shows "neg_data (x#xs) a"
  using assms by auto

lemma always_in_front_Cons:
  assumes "always_in_front xs"
  assumes "x (other, position) > x (ego, position)"
  shows "always_in_front (x#xs)"
  using assms by auto

theorem 
  check_bb_safe_dist_eq:
  "check_bb_safe_dist bb_trace \<longleftrightarrow>
    nonneg_data bb_trace (ego, speed) \<and>
    nonneg_data bb_trace (other, speed) \<and>
    neg_data bb_trace (ego, max_dec) \<and> 
    neg_data bb_trace (other, max_dec) \<and>
    always_in_front bb_trace \<and>
    no_collision_trace bb_trace"
proof
  assume if_asm: "check_bb_safe_dist bb_trace"
  then show
    "nonneg_data bb_trace (ego, speed) \<and>
    nonneg_data bb_trace (other, speed) \<and>
    neg_data bb_trace (ego, max_dec) \<and> 
    neg_data bb_trace (other, max_dec) \<and> 
    always_in_front bb_trace \<and>
    no_collision_trace bb_trace"
  proof (induction bb_trace)
    case Nil
    then show ?case by (auto)
  next
    case (Cons a bb_trace)
    from `check_bb_safe_dist (a # bb_trace)`
    have 0: "checker (s\<^sub>e a) (v\<^sub>e a) (a\<^sub>e a) (s\<^sub>o a) (v\<^sub>o a) (a\<^sub>o a) \<and> check_bb_safe_dist bb_trace"
      using s\<^sub>e_def v\<^sub>e_def s\<^sub>o_def v\<^sub>o_def a\<^sub>e_def a\<^sub>o_def
      by (simp add: check_bb_safe_dist.induct)

    hence ind_asm0: "check_bb_safe_dist bb_trace" by rule

    from ind_asm0[THEN Cons.IH] have
    ind_concl: "no_collision_trace bb_trace"
    and ind_pcs: "nonneg_data bb_trace (ego, speed)" "nonneg_data bb_trace (other, speed)"
      "neg_data bb_trace (ego, max_dec)" "neg_data bb_trace (other, max_dec)" "always_in_front bb_trace"
      by simp_all

    have eq: "no_collision_trace  (a # bb_trace) = 
         (no_collision_jumps  a \<and> 
          no_collision_trace  bb_trace)" 
    using distrib_no_collision_trace by simp
    
    from 0 have chk: "checker (s\<^sub>e a) (v\<^sub>e a) (a\<^sub>e a) (s\<^sub>o a) (v\<^sub>o a) (a\<^sub>o a)" by rule
    then interpret safe_distance "a\<^sub>e a" "(v\<^sub>e a)" "(s\<^sub>e a)" "a\<^sub>o a" "v\<^sub>o a" "s\<^sub>o a"
      by (intro check_precond_imp_safe_distance checker_imp_check_precond)

    from `checker (s\<^sub>e a) (v\<^sub>e a) (a\<^sub>e a) (s\<^sub>o a) (v\<^sub>o a) (a\<^sub>o a)` have 
         "(\<not> (\<exists>t\<in>{t. 0 \<le> t}. movement.s (a\<^sub>e a) (v\<^sub>e a) (s\<^sub>e a) t = 
                              movement.s (a\<^sub>o a) (v\<^sub>o a) (s\<^sub>o a) t))"
    using soundness_correctness by (simp add: collision_def)
    
    hence "no_collision_jumps a"
    using v\<^sub>e_def s\<^sub>e_def v\<^sub>o_def s\<^sub>o_def a\<^sub>e_def a\<^sub>o_def no_collision_jumps_def
    by simp
    
    from this eq chk ind_concl show ?case
      using nonneg_vel_ego nonneg_vel_other in_front decelerate_ego decelerate_other
      by (safe intro!: nonneg_data_Cons neg_data_Cons always_in_front_Cons ind_pcs checker_imp_check_precond)
        (simp_all add: v\<^sub>e_def v\<^sub>o_def s\<^sub>e_def s\<^sub>o_def a\<^sub>e_def a\<^sub>o_def)
  qed
next
  assume only_if_asm: "nonneg_data bb_trace (ego, speed) \<and>
    nonneg_data bb_trace (other, speed) \<and>
    neg_data bb_trace (ego, max_dec) \<and> 
    neg_data bb_trace (other, max_dec) \<and>
    always_in_front bb_trace \<and>
    no_collision_trace bb_trace"
  then show "check_bb_safe_dist bb_trace"
  proof (induction bb_trace)
    case Nil
    then show "check_bb_safe_dist []" by auto
  next
    case (Cons a bb_trace)
    then have "check_bb_safe_dist bb_trace"
      by (simp only: nonneg_data_closed neg_data_closed always_in_front_closed distrib_no_collision_trace)

    (* checking the safety of a *)
    from Cons have a0: "0 \<le> v\<^sub>e a" using nonneg_data_closed v\<^sub>e_def by simp
    from Cons have a1: "0 \<le> v\<^sub>o a" using nonneg_data_closed v\<^sub>o_def by simp
    from Cons have a2: "0 < s\<^sub>o a - s\<^sub>e a" using always_in_front_closed s\<^sub>o_def s\<^sub>e_def by simp
    from Cons have a3: "a\<^sub>e a < 0" using neg_data_closed a\<^sub>e_def by simp
    from Cons have a4: "a\<^sub>o a < 0" using neg_data_closed a\<^sub>o_def by simp
    from Cons have nc: "no_collision_jumps a"
    using distrib_no_collision_trace by simp

    from a0 a1 a2 a3 a4
    interpret safe_distance "a\<^sub>e a" "v\<^sub>e a" "s\<^sub>e a" "a\<^sub>o a" "v\<^sub>o a" "s\<^sub>o a"
      by unfold_locales auto
    (* use the soundness_correctness theorem here *)
    from nc a0 a1 a2 a3 a4 have left: "checker (s\<^sub>e a) (v\<^sub>e a) (a\<^sub>e a) (s\<^sub>o a) (v\<^sub>o a) (a\<^sub>o a)"
      unfolding soundness_correctness
      by (auto simp: no_collision_jumps_def check_precond_def collision_def)
        (simp add: s\<^sub>e_def v\<^sub>e_def s\<^sub>o_def v\<^sub>o_def a\<^sub>e_def a\<^sub>o_def)

    show ?case
      using left \<open>check_bb_safe_dist bb_trace\<close>
      by (simp add: s\<^sub>e_def v\<^sub>e_def s\<^sub>o_def v\<^sub>o_def a\<^sub>e_def a\<^sub>o_def)    
  qed
qed

fun var_of_tuple6::"real tuple6 \<Rightarrow> (var, real) jumps" 
  where
    "var_of_tuple6 (se, _, _, _, _, _) (ego, position) = se"
  | "var_of_tuple6 (_, ve, _, _, _, _) (ego, speed) = ve"
  | "var_of_tuple6 (_, _, ae, _, _, _) (ego, max_dec) = ae"
  | "var_of_tuple6 (_, _, _, so, _ ,_) (other, position) = so"
  | "var_of_tuple6 (_, _, _, _, vo ,_) (other, speed) = vo"
  | "var_of_tuple6 (_, _, _, _, _ ,ao) (other, max_dec) = ao"

definition interpret_tuple6::"real tuple6 list \<Rightarrow> (var, real) discrete_trace"
  where "interpret_tuple6 = map var_of_tuple6"

fun check_bb_safe_dist_wit' :: "nat \<Rightarrow> (ivl tuple6) list \<Rightarrow> bool list" where
"check_bb_safe_dist_wit' prec [] = []" | 
"check_bb_safe_dist_wit' prec ((se, ve, ae, so, vo, ao) # js) = 
  (checker' prec se ve ae so vo ao # check_bb_safe_dist_wit' prec js)"

fun numbering_result :: "bool list \<Rightarrow> (nat \<times> bool) list" where
"numbering_result res = zip [0..<(length res)] res"

fun filter_witness :: "bool list \<Rightarrow> nat list" where
"filter_witness res = map fst (filter (\<lambda>nres . snd nres = False) (numbering_result res))"

definition check_bb_safe_dist_wit'' :: "nat \<Rightarrow> (real tuple6) list \<Rightarrow> bool list" where
"check_bb_safe_dist_wit'' p trc = 
  check_bb_safe_dist_wit' p
      (map (\<lambda>(a, b, c, d, e, f).
        (float_ivl_of_real p a,
         float_ivl_of_real p b,
         float_ivl_of_real p c,
         float_ivl_of_real p d,
         float_ivl_of_real p e,
         float_ivl_of_real p f)) trc)"

fun check_bb_safe_dist' :: "_ \<Rightarrow> nat \<Rightarrow> (ivl tuple6) list \<Rightarrow> bool" where
"check_bb_safe_dist' chk' prec [] = True" | 
"check_bb_safe_dist' chk' prec ((se, ve, ae, so, vo, ao) # js) =
  (chk' prec se ve ae so vo ao \<and> check_bb_safe_dist' chk' prec js)"

definition trans6
  where "trans6 c chk'    se     ve     ae     so     vo     ao =
                  chk' (c se) (c ve) (c ae) (c so) (c vo) (c ao)"

primrec real_of_dec where
  "real_of_dec (m, e) =
    real_of_int (int_of_integer m) *
      (if e \<ge> 0 then 10 ^ (nat_of_integer e) else inverse (10 ^ (nat (-(int_of_integer e)))))"

lemma "real_of_dec (m, e) = int_of_integer m * 10 powr (int_of_integer e)"
proof -
  have 1: "e \<ge> 0 \<Longrightarrow> real (nat_of_integer e) = real_of_int (int_of_integer e)"
    using less_eq_integer.rep_eq nat_of_integer.rep_eq by auto
  have 2: "e \<le> 0 \<Longrightarrow> real_of_int (int_of_integer e) = - real (nat (- int_of_integer e))"
    using less_eq_integer.rep_eq by auto
  show ?thesis
    using 1
    apply (auto simp: real_of_dec_def powr_realpow[symmetric] divide_simps)
    apply (subst (asm) 2)
    apply (auto simp: powr_add[symmetric])
    done
qed

definition checker_dec
  where "checker_dec chk' p u =
    trans6 (float_ivl_of_real (nat_of_integer u) o real_of_dec) (chk' (nat_of_integer p))"

definition "checker_interval = checker_dec checker'"
definition "checker_symbolic = trans6 real_of_dec symbolic_checker"
definition "checker_rational = trans6 real_of_dec checker"
lemmas[code] = movement.p_def

lemma checker_kernel: "checker 0 54.93 (-5.6087) 62.58 54.90 (-5.6388)"
  by (simp add: checker_def Let_def check_precond_def first_safe_dist_def second_safe_dist_def
    suff_cond_safe_dist2_def rel_dist_to_stop_def power2_eq_square)


subsubsection\<open>Evaluation\<close>
text \<open>\label{sec:eval}\<close>
ML \<open>Char.isPunct\<close>
definition "testval = (40.99::real)"
export_code testval in SML
ML \<open>
  fun split_string s = String.fields (fn c => c = the (Char.fromString s))
  fun dec_of_string s =
    case split_string "." s
    of [r] => (the (IntInf.fromString r), 0)
    | [d1, d2] => (the (IntInf.fromString (d1 ^ d2)), ~ (String.size d2))
  fun check_string chk data =
    let
      val [id, so, _, ve, ae, _, vo, ao] = split_string "," data
(*      val _ = @{print} [(dec_of_string ve), (dec_of_string ae), (dec_of_string so), (dec_of_string vo), (dec_of_string ao)]*)
    in
      chk data (0, 0)
        (dec_of_string ve) (dec_of_string ae) (dec_of_string so) (dec_of_string vo) (dec_of_string ao)
    end
\<close>
ML \<open>
val prec = 12 (* 12 is roughly precision of input data, yields similar performance as Sturm *)
fun check_stream' chk i n y s =
  case TextIO.inputLine s of
    NONE => (TextIO.closeIn s; (y, i))
  | SOME l =>
    let
      val l = String.substring (l, 0, String.size l - 1)
(*       val _ = writeln l *)
      val c = check_string chk l
(*      val _ = if c then TextIO.print (IntInf.toString i ^ ": Yes\n") else TextIO.print (IntInf.toString i ^ ": No\n") *)
    in
      if i < n then check_stream' chk (i + 1) n (if c then y + 1 else y) s
      else (TextIO.closeIn s; (y, i))
    end
fun check_stream chk f n = check_stream' chk 0 n 0 (TextIO.openIn f)
val check_stream_symbolic = check_stream (fn _ => @{code checker_symbolic})
fun check_stream_interval prec uncer = check_stream (fn _ => @{code checker_interval} prec uncer)
val check_stream_rational = check_stream (fn _ => @{code checker_rational})
fun check_stream_delta prec uncer = check_stream (fn s => fn b => fn c => fn d => fn e => fn f => fn g =>
  let
    val c1 = @{code checker_rational} b c d e f g
    val c2 = @{code checker_interval} prec uncer b c d e f g
    val _ = if c1 andalso not c2 then writeln ("Incompletion at: " ^ s) else ()
  in c2 end
  )
\<close>

ML \<open>val filename = "/Users/immler/work/traffic/safe-distance/data/test_vector_first.csv"\<close>

ML \<open>
    val t_start = Timing.start ();
    check_stream_rational filename 1121215(*00*);
    val t_end = Timing.result t_start;
\<close>

ML \<open>check_stream_interval (* prec *) 12 (* uncertainty: 2^-7 *) 7 filename 2000\<close>
ML \<open>check_stream_rational filename 200000\<close>
ML \<open>check_stream_symbolic filename 2000\<close>
ML \<open>check_stream_delta 12 7 filename 200000\<close>


text \<open>438,62.58,6,54.90,-5.6088,4,54.90,-5.6088\<close>
text \<open> id,   so, ,   ve,     ae, ,   vo,     ao\<close>

context begin

private definition se::real where "se = 0"
private definition so::real where "so = 40.99"
private definition ve::real where "ve = 45.15"
private definition vo::real where "vo = 44.56"
private definition ae::real where "ae = -5.6088"
private definition ao::real where "ao = -5.6088"

ML \<open>map dec_of_string ["114.01", "50.00", "50.52", "-5.6088"]\<close>

lemmas test_defs = se_def so_def ve_def vo_def ae_def ao_def
thm checker_def[THEN meta_eq_to_obj_eq, unfolded Let_def, of se ve ae so vo ao]
value [code] "second_safe_dist ve ae vo ao < so - se"
lemma "second_safe_dist ve ae vo ao < so - se"
  unfolding second_safe_dist_def rel_dist_to_stop_def test_defs
  apply (approximation 10)
  done

value [code] "so - se \<le> first_safe_dist ve ae"
lemma "so - se \<le> first_safe_dist ve ae"
  unfolding rel_dist_to_stop_def test_defs first_safe_dist_def
  apply (approximation 10)
  done
value [code] "suff_cond_safe_dist2 se ve ae so vo ao"
lemma "suff_cond_safe_dist2 se ve ae so vo ao"
  unfolding checker_def check_precond_def first_safe_dist_def second_safe_dist_def
    suff_cond_safe_dist2_def Let_def t_stop_def s_stop_def
    rel_dist_to_stop_def
    discriminant_def
    not_le not_less
    de_Morgan_conj
    de_Morgan_disj
  unfolding test_defs
(*  apply (approximation 80) *)
  oops

value [code] "((4456 / 10\<^sup>2 - 4515 / 10\<^sup>2)\<^sup>2 -
    2 * (- (56088 / 10 ^ 4) - - (56088 / 10 ^ 4)) * (4099 / 10\<^sup>2 - 0)::real)"
value [code] "(4515 / 10\<^sup>2 - - (56088 / 10 ^ 4) / - (56088 / 10 ^ 4) * (4456 / 10\<^sup>2))\<^sup>2::real"

value[code] "trans6 (\<lambda>(i, j). (integer_of_int i, integer_of_int j)) (checker_interval (integer_of_nat 10) (integer_of_nat 10))
  (0, 0)
  (4515, -2)
  (-56088, -4)
  (4099, -2)
  (4456, -2)
  (-56088, -4)"
(* 0 ve ae so vo ao *)

end

end