theory Overtaking_rules
imports 
  Main Overtaking_Aux Environment_Executable
  "./safe_distance/Safe_Distance_Isar"
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
  
lemma semantics_ltlc_sugar [simp]:
  "\<xi> \<Turnstile>\<^sub>f \<phi> iff\<^sub>f \<psi> = (\<xi> \<Turnstile>\<^sub>f \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>f \<psi>)"
  "\<xi> \<Turnstile>\<^sub>f F\<^sub>f \<phi> = \<xi> \<Turnstile>\<^sub>f (true\<^sub>f U\<^sub>f \<phi>)"  
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
  
theorem exist_at_0:
  assumes "0 < length xs"
  shows "(\<exists>i < length xs. P i)  \<longleftrightarrow> (P 0 \<or> (\<exists>i. 0 < i \<and> i < length xs \<and> P i))"
  using assms by auto
    
theorem exist_at_0':
  assumes "(\<exists>i < length xs. P i)" 
  shows "((0 < length xs \<and> P 0) \<or> (\<exists>i. 0 < i \<and> i < length xs \<and> P i))"
  using assms by auto    
(* 
theorem 
  "suffix_list i (x # xs) \<Turnstile>\<^sub>f form = suffix_list (i - 1) xs \<Turnstile>\<^sub>f form"
  unfolding suffix_list_def by auto *)
    
theorem F_decompose:
  "((x # xs) \<Turnstile>\<^sub>f F\<^sub>f form) \<longleftrightarrow> (x # xs)  \<Turnstile>\<^sub>f form \<or> (xs \<Turnstile>\<^sub>f F\<^sub>f form)"
proof (cases "(x # xs)  \<Turnstile>\<^sub>f form")
  case True  
  have "(x # xs) \<Turnstile>\<^sub>f F\<^sub>f form = (\<exists>i < length (x # xs). suffix_list i (x # xs) \<Turnstile>\<^sub>f form)" 
    by auto
  also have "... = (suffix_list 0 (x # xs) \<Turnstile>\<^sub>f form \<or> (\<exists>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form))"
    (is "_ = (?disj1 \<or> ?disj2)")
    using exist_at_0 by auto
  also have "... = ((x # xs) \<Turnstile>\<^sub>f form \<or> ?disj2)" by (auto simp add:suffix_list_def) 
  also have "... = True" using True by auto
  finally have "(x # xs) \<Turnstile>\<^sub>f F\<^sub>f form" by auto            
  then show ?thesis using True by auto
next
  case False
  have "(x # xs) \<Turnstile>\<^sub>f F\<^sub>f form = (\<exists>i < length (x # xs). suffix_list i (x # xs) \<Turnstile>\<^sub>f form)" 
    by auto
  also have "... = (suffix_list 0 (x # xs) \<Turnstile>\<^sub>f form \<or> (\<exists>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form))"
    (is "_ = (?disj1 \<or> ?disj2)")
    using exist_at_0 by auto
  also have "... = ((x # xs) \<Turnstile>\<^sub>f form \<or> ?disj2)" by (auto simp add:suffix_list_def) 
  also have "... = ?disj2" using False by auto 
  also have "... = (\<exists>i < length xs. suffix_list i xs \<Turnstile>\<^sub>f form)" unfolding suffix_list_def 
  proof (rule)
    assume asm: "\<exists>i>0. i < length (x # xs) \<and> drop i (x # xs) \<Turnstile>\<^sub>f form"    
    { fix i  :: nat
      assume i: "0 < i \<and> i < length (x # xs) \<and> drop i (x # xs) \<Turnstile>\<^sub>f form" hence "0 < i" "drop i (x # xs) \<Turnstile>\<^sub>f form" 
        by auto
      define j where "j = i - 1"
      from i have j: "0 \<le> j \<and> j < length xs" unfolding j_def by auto
      from Environment_Executable.drop_cons[OF `0 < i`] have "drop (i-1) xs \<Turnstile>\<^sub>f form"
        using `drop i (x # xs) \<Turnstile>\<^sub>f form` by metis
      hence "drop j xs \<Turnstile>\<^sub>f form" unfolding j_def by auto         
      with j have "\<exists>j < length xs. drop j xs \<Turnstile>\<^sub>f form" by auto }  
    from exE[OF asm this] show "\<exists>i<length xs. drop i xs \<Turnstile>\<^sub>f form" by auto
  next
    assume asm: "\<exists>i<length xs. drop i xs \<Turnstile>\<^sub>f form"
    { fix i :: nat
      assume "i < length xs \<and> drop i xs \<Turnstile>\<^sub>f form" 
      hence "0 < i + 1" "i + 1 < length (x # xs)" and "drop i xs \<Turnstile>\<^sub>f form" by auto
      with Environment_Executable.drop_cons[OF `0 < i + 1`] have "drop (i + 1) (x # xs) \<Turnstile>\<^sub>f form"
        by auto
      hence "\<exists>j. 0 < j \<and> j < length (x # xs) \<and> drop j (x # xs) \<Turnstile>\<^sub>f form" using `0 < i + 1` `i + 1 < length (x # xs)`
        by (auto intro:) }  
    from exE[OF asm this] show " \<exists>i>0. i < length (x # xs) \<and> drop i (x # xs) \<Turnstile>\<^sub>f form"   by auto
  qed    
  finally show ?thesis using False by auto 
qed 
  
theorem G_decompose: 
  "(x # xs) \<Turnstile>\<^sub>f G\<^sub>f form = ((x # xs) \<Turnstile>\<^sub>f form \<and> xs \<Turnstile>\<^sub>f G\<^sub>f form)"  
proof -   
  have "(x # xs) \<Turnstile>\<^sub>f G\<^sub>f form = (\<forall>i < length (x # xs). suffix_list i (x # xs) \<Turnstile>\<^sub>f form)"
    by auto
  also have "... = (suffix_list 0 (x # xs) \<Turnstile>\<^sub>f form \<and> (\<forall>i. 0 < i \<and> i < length (x # xs) \<longrightarrow> suffix_list i (x # xs) \<Turnstile>\<^sub>f form))"
    (is "_ = (?conj1 \<and> ?conj2)")
    using univ_at_0 by auto
  also have "... = ((x # xs) \<Turnstile>\<^sub>f form \<and> ?conj2)" unfolding suffix_list_def by auto
  finally have *: "(x # xs) \<Turnstile>\<^sub>f G\<^sub>f form = ((x # xs) \<Turnstile>\<^sub>f form \<and> ?conj2)" by auto
  have "?conj2 = (\<forall>i < length xs. suffix_list i xs \<Turnstile>\<^sub>f form)" (is "_ = ?quant")
  proof 
    assume "?conj2"
    show "?quant"
    proof (rule allI, rule impI)
      fix i
      assume "i < length xs"
      hence "i + 1 < length (x # xs)" and "0 < i + 1" by auto  
      with `?conj2` have "suffix_list (i + 1) (x # xs) \<Turnstile>\<^sub>f form" by auto
      with Environment_Executable.drop_cons[OF `0 < i + 1`] show "suffix_list i xs \<Turnstile>\<^sub>f form"     
        unfolding suffix_list_def by auto                
    qed
  next
    assume "?quant"
    show "?conj2"
    proof (rule allI, rule impI)
      fix i
      assume "0 < i \<and> i < length (x # xs)" 
      hence *: "0 \<le> i - 1 \<and> i - 1 < length xs" and "0 < i" by auto
      with `?quant` have "suffix_list (i-1) xs \<Turnstile>\<^sub>f form" by auto
      with Environment_Executable.drop_cons[OF `0 < i`] show "suffix_list i (x # xs) \<Turnstile>\<^sub>f form"     
        unfolding suffix_list_def by metis  
    qed      
  qed
  with * show ?thesis by auto 
qed
  
theorem 
  "(\<exists>x. P x \<and> Q \<and> R x) \<Longrightarrow> Q \<and> (\<exists>x. P x \<and> R x)"  
  by auto  

  
theorem U_decompose:
  assumes "\<not> (x # xs) \<Turnstile>\<^sub>f form2"
  assumes "(x # xs) \<Turnstile>\<^sub>f form1 U\<^sub>f form2" (is "?eq1") 
  shows "((x # xs) \<Turnstile>\<^sub>f form1 \<and> xs \<Turnstile>\<^sub>f form1 U\<^sub>f form2)" (is "_ \<and> ?eq2")  
proof -
  have "0 < length (x # xs)" by auto 
  have "?eq1 = (\<exists>i. i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1))"
    by auto
  also have "... = ((suffix_list 0 (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j < 0. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)) \<or> 
                    (\<exists>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j < i. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)))"
    (is "_ = (_ \<or> ?quant)")
    using exist_at_0[OF `0 < length (x # xs)`] by auto
  also have "... = ((x # xs)\<Turnstile>\<^sub>fform2 \<or> ?quant)" by (auto simp add:suffix_list_def)      
  also have "... = ?quant" using assms by auto
  also have "... = (\<exists>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> suffix_list 0 (x # xs) \<Turnstile>\<^sub>f form1 \<and> (\<forall>j. 0 < j \<and> j < i \<longrightarrow> suffix_list j (x # xs) \<Turnstile>\<^sub>f form1))"
    using univ_at_0[where P="\<lambda>j. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1"] by auto
  also have "... = (\<exists>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> (x # xs) \<Turnstile>\<^sub>f form1 \<and> (\<forall>j. 0 < j \<and> j < i \<longrightarrow> suffix_list j (x # xs) \<Turnstile>\<^sub>f form1))"  
    (is "_ = ?bigquant")    
    by (auto simp add:suffix_list_def)
  finally have "?eq1 = ?bigquant" by auto    
  with assms have "?bigquant" by auto      
  hence "(x # xs) \<Turnstile>\<^sub>f form1 \<and> (\<exists>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j. 0 < j \<and> j < i \<longrightarrow> suffix_list j (x # xs) \<Turnstile>\<^sub>f form1))"
    (is "?conj1 \<and> ?conj2") by auto
  have "?conj2 \<Longrightarrow> ?eq2" unfolding semantics_ltlf.simps
  proof -
    assume "?conj2"
    { fix i :: nat
      assume "0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j. 0 < j \<and> j < i \<longrightarrow> suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)"
      hence "0 < i" and "i < length (x # xs)" and q2: "suffix_list i (x # xs) \<Turnstile>\<^sub>f form2" and q: "(\<forall>j. 0 < j \<and> j < i \<longrightarrow> suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)"
        by auto
      hence "0 \<le> i -1" and c2: "i - 1 < length xs" by auto
      from Environment_Executable.drop_cons[OF `0 < i`] have c1: "suffix_list (i - 1) xs \<Turnstile>\<^sub>f form2" 
        using `suffix_list i (x # xs) \<Turnstile>\<^sub>f form2` unfolding suffix_list_def by metis
      have "\<forall>j. j < (i - 1) \<longrightarrow> suffix_list j xs \<Turnstile>\<^sub>f form1" 
      proof (rule, rule)
        fix j
        assume "j < i - 1"
        hence 0: "0 < j + 1 \<and> j + 1 < i" by auto            
        hence "suffix_list (j + 1) (x # xs) \<Turnstile>\<^sub>f form1" using q by auto
        with Environment_Executable.drop_cons[of "j" "x" "xs"] show "suffix_list j xs \<Turnstile>\<^sub>f form1"
          unfolding suffix_list_def by auto
      qed
      with c1 and c2 have "i - 1 <length xs \<and>  suffix_list (i - 1) xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i-1. suffix_list j xs \<Turnstile>\<^sub>f form1)"
        by auto }      
    from this have "\<And>i. 0 < i \<and> i < length (x # xs) \<and> suffix_list i (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j. 0 < j \<and> j < i \<longrightarrow> suffix_list j (x # xs) \<Turnstile>\<^sub>f form1) \<Longrightarrow> 
        i - 1 <length xs \<and>  suffix_list (i - 1) xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i-1. suffix_list j xs \<Turnstile>\<^sub>f form1)" by auto  
    from exE[OF `?conj2` this] obtain k where " k - 1 < length xs \<and> suffix_list (k - 1) xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<k - 1. suffix_list j xs \<Turnstile>\<^sub>f form1)"
      by blast
    thus "\<exists>i<length xs. suffix_list i xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1)"
      by (auto intro:)  
  qed
  with `?conj1 \<and> ?conj2` show ?thesis by auto  
qed
  
theorem U_decompose':
  assumes "\<not> (x # xs) \<Turnstile>\<^sub>f form2"
  assumes "((x # xs) \<Turnstile>\<^sub>f form1 \<and> xs \<Turnstile>\<^sub>f form1 U\<^sub>f form2)" (is "_ \<and> ?eq2")  
  shows "(x # xs) \<Turnstile>\<^sub>f form1 U\<^sub>f form2" 
proof -
  have "?eq2 = (\<exists>i. i < length xs \<and> suffix_list i xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1))"
    by auto
  also have "... \<Longrightarrow> ((0 < length xs \<and> suffix_list 0 xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<0. suffix_list j xs \<Turnstile>\<^sub>f form1)) \<or> (\<exists>i. 0 < i \<and> i < length xs \<and> suffix_list i xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1)))"    
    (is "_ \<Longrightarrow> (?case1 \<or> ?case2)")
    using exist_at_0'[where P="\<lambda>i. suffix_list i xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1)" and xs="xs"]
    by auto
  with assms(2) have "?case1 \<or> ?case2" by auto
  moreover
  { assume "?case1"
    hence "xs \<Turnstile>\<^sub>f form2" unfolding suffix_list_def by auto  
    have ?thesis
    proof (unfold semantics_ltlf.simps, rule exI[where x="1"])
      have 1: "1 < length (x # xs)" using `?case1` by auto
      have 2: "suffix_list 1 (x # xs) \<Turnstile>\<^sub>f form2" unfolding suffix_list_def using `xs \<Turnstile>\<^sub>f form2`
        by auto
      have 3: " (\<forall>j<1. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)" unfolding suffix_list_def using 
          assms by auto   
      with 1 and 2 show "1 < length (x # xs) \<and> suffix_list 1 (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<1. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)"        
        by auto             
    qed }
  moreover  
  { assume "?case2"
    hence "(\<exists>k. 0 < k \<and> k < length (x # xs) \<and> suffix_list k (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<k. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1))"
    proof -
      assume " \<exists>i>0. i<length xs \<and> suffix_list i xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1)"   
      { fix i :: nat
        assume "0 < i \<and> i<length xs \<and> suffix_list i xs \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1)"        
        hence "i + 1 < length (x # xs)" and "suffix_list (i + 1) (x # xs) \<Turnstile>\<^sub>f form2"
          and q: "(\<forall>j<i. suffix_list j xs \<Turnstile>\<^sub>f form1)" and "0 < i"
          using Environment_Executable.drop_cons[of "i + 1" "x" "xs"] unfolding suffix_list_def  
          by auto
        have "(\<forall>j<i+1. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)"
        proof (rule, rule)
          fix j
          assume "j < i + 1"
          hence "j - 1 < i"  using \<open>0 < i\<close> by linarith
          with q have "suffix_list (j - 1) xs \<Turnstile>\<^sub>f form1" by auto
          have "j = 0 \<or> j \<noteq> 0" by auto    
          moreover
          { assume "j = 0"
            hence "suffix_list j (x # xs) \<Turnstile>\<^sub>f form1" unfolding suffix_list_def using assms
              by auto  }
          moreover
          { assume "j \<noteq> 0"
            hence "0 < j" by auto  
            hence "suffix_list j (x # xs) \<Turnstile>\<^sub>f form1"  
              using Environment_Executable.drop_cons[OF `0 < j`, of "x" "xs"] `suffix_list (j - 1) xs \<Turnstile>\<^sub>f form1`
              unfolding suffix_list_def by metis }  
          ultimately show "suffix_list j (x # xs) \<Turnstile>\<^sub>f form1" by auto
        qed      
        hence "0 < i + 1 \<and> i + 1 < length (x # xs) \<and> suffix_list (i + 1) (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<i+1. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)"
          using `i + 1 < length (x # xs)` `suffix_list (i + 1) (x # xs) \<Turnstile>\<^sub>f form2` by auto }
      from exE[OF `?case2` this] obtain k where " 0 < k+1 \<and> k+1 < length (x # xs) \<and> suffix_list (k+1) (x # xs) \<Turnstile>\<^sub>f form2 \<and> (\<forall>j<k+1. suffix_list j (x # xs) \<Turnstile>\<^sub>f form1)"
        by metis
      thus ?thesis by auto          
    qed }
  ultimately show ?thesis by auto
qed
  
section "Representing overtaking traffic rules in LTL with finite trace"
  
  
\<comment>\<open>traffic rules atoms\<close>
datatype tr_atom = overtaking_atom  | on_fastlane_atom  | sd_rear_atom  |  sd_front_atom  | 
                   surpassing_atom  | safe_side_atom  |  larger_safe_side_atom  | motorised_atom  | 
                   safe_to_return_atom  |  merging_atom  | original_lane_atom
                   
thm tr_atom.eq.simps
find_theorems "overtaking_atom"  
thm "tr_atom.eq.simps" 
term "equal_class.equal overtaking_atom"  
  
  
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
  "\<Phi>1 \<equiv> G\<^sub>f (overtaking and\<^sub>f on_fastlane implies\<^sub>f sd_rear)"

definition \<Phi>2 :: "tr_atom ltlf" where
  "\<Phi>2 \<equiv> G\<^sub>f (overtaking and\<^sub>f (surpassing and\<^sub>f motorised) implies\<^sub>f safe_side)"
  
definition \<Phi>2' :: "tr_atom ltlf" where
  "\<Phi>2' \<equiv> G\<^sub>f (overtaking and\<^sub>f (surpassing and\<^sub>f not\<^sub>f motorised) implies\<^sub>f larger_safe_side)"
  
definition \<Phi>3 :: "tr_atom ltlf" where
  "\<Phi>3 \<equiv> G\<^sub>f (overtaking and\<^sub>f (original_lane and\<^sub>f merging) implies\<^sub>f sd_rear)"
                            
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
    
definition (in lane) overtaking_checker :: "black_boxes \<Rightarrow> tr_atom set list" where
  "overtaking_checker bb \<equiv> 
                  rects_to_words (\<lambda>x. overtaking_trace  x) overtaking_atom (bb_to_rects bb)"  

definition (in lane) onfastlane_checker :: "black_boxes \<Rightarrow> tr_atom set list" where
  "onfastlane_checker bb \<equiv> 
                  rects_to_words (\<lambda>x. fast_lane_trace x) on_fastlane_atom (bb_to_rects bb)"

definition (in lane) merging_checker :: "black_boxes \<Rightarrow> tr_atom set list" where
  "merging_checker bb  \<equiv> 
                        rects_to_words (\<lambda>x. merging_trace x) merging_atom (bb_to_rects bb)"  
  
definition (in lane) original_lane_checker :: "black_boxes \<Rightarrow> tr_atom set list" where
  "original_lane_checker bb \<equiv> 
            rects_to_words (\<lambda>x. original_lane_trace x) original_lane_atom (bb_to_rects bb)"
  
\<comment>\<open>Detecting vehicles behind\<close>

fun relevant_lane_id :: "detection_opt \<Rightarrow> nat list" where
  "relevant_lane_id Outside = []" | 
  "relevant_lane_id (Lane x) = [x]" | 
  "relevant_lane_id (Boundaries ns) = ns"
  
fun list_intersect :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "list_intersect [] _ = False" | 
  "list_intersect (a # as) bs = (case find (\<lambda>x. x = a) bs of 
                                    Some _ \<Rightarrow> True 
                                 |  None \<Rightarrow> list_intersect as bs)"
  
theorem list_intersect_sound: 
  "list_intersect as bs \<longleftrightarrow> (\<exists>x. x \<in> set as \<and> x \<in> set bs)"
proof (induction as)
  case Nil
  then show ?case by auto
next
  case (Cons a as)  
  note case_cons = this  
  define res where "res \<equiv> find (\<lambda>x. x = a) bs"    
  then show ?case unfolding list_intersect.simps 
  proof (induction res)
    case None      
    have "list_intersect as bs = (\<exists>x. x \<in> set (a # as) \<and> x \<in> set bs)" (is "?lhs = ?rhs")
    proof -
      from sym[OF None] have " (\<nexists>x. x \<in> set bs \<and> x = a)" unfolding find_None_iff by auto
      hence "a \<notin> set bs" by auto
      hence "?rhs = (\<exists>x. x \<in> set as \<and> x \<in> set bs)" by auto
      also have "... = ?lhs" using case_cons by auto          
      finally show ?thesis by auto
    qed      
    with sym[OF None] show ?case by auto   
  next
    case (Some option)
    note case_option = this  
    from sym[OF this] have " \<exists>i<length bs. bs ! i = a \<and> option = bs ! i \<and> (\<forall>j<i. bs ! j \<noteq> a)" 
      unfolding find_Some_iff  by auto
    hence "a \<in> set bs" by auto        
    hence " (\<exists>x. x \<in> set (a # as) \<and> x \<in> set bs)" by auto     
    with sym[OF case_option] show ?case by auto
  qed          
qed  
    
fun is_relevant :: "nat list \<Rightarrow> detection_opt \<Rightarrow> bool" where
  "is_relevant _ Outside = False" | 
  "is_relevant ids (Lane x)  = (x \<in> set ids)" | 
  "is_relevant ids (Boundaries ns)  = list_intersect ns ids"  
  
definition (in lane) trim_vehicles_same_lane :: "raw_state list \<Rightarrow> detection_opt \<Rightarrow> raw_state list" where
  "trim_vehicles_same_lane states l = (let  ids = relevant_lane_id l in 
                                      filter (is_relevant ids \<circ> lane_detection \<circ> rectangle.truncate) states)"

definition (in lane) vehicles_behind :: "raw_state list \<Rightarrow> raw_state \<Rightarrow> raw_state list" where
  "vehicles_behind states r = (let re = rectangle.truncate r; 
                                   states2 = (trim_vehicles_same_lane states (lane_detection re)) in
                                   filter (\<lambda>x. Xcoord x \<le> Xcoord re) states2)"  
  
definition (in lane) sd_raw_state :: "raw_state \<Rightarrow> raw_state \<Rightarrow> real \<Rightarrow> bool" where
  "sd_raw_state ego other \<delta> \<equiv> (let se = Xcoord ego - Length ego / 2; 
                               ve = fst (velocity ego); ae = fst (acceleration ego);
                               so = Xcoord other + Length other / 2; 
                               vo = fst (velocity other); ao = fst (acceleration other)
                            in checker_r12 se ve ae so vo ao \<delta>)" 
  
fun (in lane) sd_rear' :: "raw_state list \<Rightarrow> raw_state \<Rightarrow> real \<Rightarrow> bool" where
  "sd_rear' [] _ _ = True" | 
  "sd_rear' (r # rs) ego \<delta> = (if sd_raw_state r ego \<delta> then sd_rear' rs ego \<delta> else False)"  

definition (in lane) sd_rear :: "raw_state list \<Rightarrow> raw_state \<Rightarrow> real \<Rightarrow> bool" where
  "sd_rear rs ego \<delta> = (let vehicles = vehicles_behind rs ego in sd_rear' vehicles ego \<delta>)" 
      
fun (in lane) sd_rears :: "raw_state list list \<Rightarrow> raw_state list \<Rightarrow> real \<Rightarrow> bool list" where
  "sd_rears _ [] _ = []" |
  "sd_rears [] (ego # egos) \<delta> = (sd_rear [] ego \<delta>) # sd_rears [] egos \<delta>" |
  "sd_rears (rs # rss) (ego # egos) \<delta> = (sd_rear rs ego \<delta>) # sd_rears rss egos \<delta>"  
        
theorem (in lane)
  "length (sd_rears rss egos \<delta>) = length egos"
  by (induction rule:sd_rears.induct) (auto)
    
definition (in lane) sd_rear_checker' :: "black_boxes  \<Rightarrow> real \<Rightarrow> bool list" where
  "sd_rear_checker' bb \<delta> \<equiv> (let ego_run = snd (fst bb); other_runs = map snd (snd bb) in 
                                 sd_rears (List.transpose other_runs) ego_run \<delta>)"  
  
definition (in lane) sd_rear_checker :: "black_boxes  \<Rightarrow> real \<Rightarrow> tr_atom set list" where
  "sd_rear_checker bb \<delta> \<equiv> (let result = sd_rear_checker' bb \<delta> 
                               in  map (\<lambda>x. if x then {sd_rear_atom} else {}) result)"

function monitor_tr :: "[tr_atom set list, tr_atom ltlf] \<Rightarrow> bool"  and 
         monitor_tr_F :: "tr_atom set list \<Rightarrow> tr_atom ltlf \<Rightarrow> bool" and 
         monitor_tr_G :: "tr_atom set list \<Rightarrow> tr_atom ltlf \<Rightarrow> bool" and 
         monitor_tr_U :: "tr_atom set list \<Rightarrow> tr_atom ltlf \<Rightarrow> tr_atom ltlf \<Rightarrow> bool"
where                           
  "monitor_tr \<xi> (true\<^sub>f) = True"    
| "monitor_tr \<xi> (false\<^sub>f) = False"                         
| "monitor_tr \<xi> prop\<^sub>f(q) = (q \<in> (\<xi> ! 0))"               
| "monitor_tr \<xi> (not\<^sub>f \<phi>) = (\<not> monitor_tr \<xi> \<phi>)"      
| "monitor_tr \<xi> (\<phi> and\<^sub>f \<psi>) = (monitor_tr \<xi> \<phi> \<and> monitor_tr \<xi> \<psi>)"
| "monitor_tr \<xi> (\<phi> or\<^sub>f \<psi>) = (monitor_tr \<xi> \<phi> \<or> monitor_tr \<xi> \<psi>)"
| "monitor_tr \<xi> (\<phi> implies\<^sub>f \<psi>) = (monitor_tr \<xi> \<phi> \<longrightarrow> monitor_tr \<xi> \<psi>)"
| "monitor_tr \<xi> (X\<^sub>f \<phi>) = (monitor_tr (suffix_list 1 \<xi>) \<phi>)"                    
| "monitor_tr \<xi> (F\<^sub>f \<phi>) = monitor_tr_F \<xi> \<phi>"
| "monitor_tr \<xi> (G\<^sub>f \<phi>) = monitor_tr_G \<xi> \<phi>"
| "monitor_tr \<xi> (\<phi> U\<^sub>f \<psi>) = monitor_tr_U \<xi> \<phi> \<psi>"
  
| "monitor_tr_F [] form = False"  
| "monitor_tr_F (x # xs) form = (if monitor_tr (x # xs) form then True else monitor_tr_F xs form)" 
   
| "monitor_tr_G [] form = True"   
| "monitor_tr_G (x # xs) form = (if monitor_tr (x # xs) form then monitor_tr_G xs form else False)"  
  
| "monitor_tr_U [] form1 form2  = False" 
| "monitor_tr_U (x # xs) form1 form2 = (if monitor_tr (x # xs) form2 then True else 
                                           monitor_tr (x # xs) form1 \<and> monitor_tr_U xs form1 form2)"  
  by pat_completeness auto
termination  by size_change    
    
theorem monitoring:
  "semantics_ltlf \<xi> form = monitor_tr \<xi> form" 
  "semantics_ltlf \<xi> (F\<^sub>f \<phi>) = monitor_tr_F \<xi> \<phi>"
  "semantics_ltlf \<xi> (G\<^sub>f \<phi>) = monitor_tr_G \<xi> \<phi>"
  "semantics_ltlf \<xi> (\<phi> U\<^sub>f \<psi>) = monitor_tr_U \<xi> \<phi> \<psi>"
proof (induct  rule:monitor_tr_monitor_tr_F_monitor_tr_G_monitor_tr_U.induct)
  case (1 \<xi>)
  then show ?case by auto
next
  case (2 \<xi>)
  then show ?case by auto
next
  case (3 \<xi> q)
  then show ?case by auto
next
  case (4 \<xi> \<phi>)
  then show ?case by auto
next
  case (5 \<xi> \<phi> \<psi>)
  then show ?case by auto
next
  case (6 \<xi> \<phi> \<psi>)
  then show ?case by auto
next
  case (7 \<xi> \<phi> \<psi>)
  then show ?case by auto
next
  case (8 \<xi> \<phi>)
  then show ?case by auto
next
  case (9 \<xi> \<phi>)
  then show ?case  by (induction \<xi>) auto
next
  case (10 \<xi> \<phi>)
  then show ?case  by (induction \<xi>) auto
next
  case (11 \<xi> \<phi> \<psi>)
  then show ?case  by (induction \<xi>) auto  
next
  case (12 form)
  then show ?case by auto
next
  case (13 x xs form)
  note case13 = this  
  have "monitor_tr (x # xs) form \<or> \<not> monitor_tr (x # xs) form" by auto
  moreover  
  { assume True: "monitor_tr (x # xs) form"
    with case13 have "(x # xs) \<Turnstile>\<^sub>f form"  by auto
    hence "(x # xs) \<Turnstile>\<^sub>f F\<^sub>f(form)"  
      by (auto intro:exI[where x="0"] simp add: suffix_list_def)     
    hence ?case unfolding monitor_tr_F.simps using True by auto }
  moreover
  { assume False: "\<not> monitor_tr (x # xs) form"
    with case13 have *: "xs \<Turnstile>\<^sub>f F\<^sub>f form = monitor_tr_F xs form" by auto
    have "((x # xs) \<Turnstile>\<^sub>f F\<^sub>f form) \<longleftrightarrow> (x # xs)  \<Turnstile>\<^sub>f form \<or> (xs \<Turnstile>\<^sub>f F\<^sub>f form)" using F_decompose[of "x" "xs" "form"] .
    hence ?case unfolding monitor_tr_F.simps using False and *  by (simp add: case13(1)) }    
  ultimately show ?case by auto      
next
  case (14 form)
  then show ?case by auto
next
  case (15 x xs form)
  note case15 = this  
  have "monitor_tr (x # xs) form \<or> \<not> monitor_tr (x # xs) form" by auto
  moreover
  { assume True: "monitor_tr (x # xs) form"
    with case15 have 0: "xs \<Turnstile>\<^sub>f G\<^sub>f form = monitor_tr_G xs form" by auto
    have *: "monitor_tr_G (x # xs) form = (monitor_tr (x # xs) form \<and> monitor_tr_G xs form)" 
      by (cases "monitor_tr (x # xs) form") auto
    have "(x # xs) \<Turnstile>\<^sub>f G\<^sub>f form = ((x # xs) \<Turnstile>\<^sub>f form \<and> xs \<Turnstile>\<^sub>f G\<^sub>f form)" using G_decompose[of "x" "xs" "form"] by auto
    with case15 have **: "(x # xs) \<Turnstile>\<^sub>f G\<^sub>f form = (monitor_tr (x # xs) form \<and> xs \<Turnstile>\<^sub>f G\<^sub>f form)"  by auto  
    have ?case unfolding ** * using 0 by auto }
  moreover  
  { assume False: "\<not> monitor_tr (x # xs) form"
    hence *: "\<not> monitor_tr_G (x # xs) form" by auto
    from case15 have "\<not> (x # xs) \<Turnstile>\<^sub>f form" using False by auto
    hence "\<not> (x # xs) \<Turnstile>\<^sub>f (G\<^sub>f form)" by (auto simp add:suffix_list_def)        
    then have ?case using * by auto  }    
  ultimately show ?case by auto
next
  case (16 form1 form2)
  then show ?case by auto
next
  case (17 x xs form1 form2)
  note case17 = this  
  have " monitor_tr (x # xs) form2 \<or> \<not>  monitor_tr (x # xs) form2 " by auto
  moreover
  { assume True: " monitor_tr (x # xs) form2 "
    hence *: "monitor_tr_U (x # xs) form1 form2" by auto
    from True case17 have "(x # xs) \<Turnstile>\<^sub>f form2" by auto
    hence "(x # xs) \<Turnstile>\<^sub>f form1 U\<^sub>f form2" by (auto simp add:suffix_list_def)     
    hence ?case using * by auto }  
  moreover  
  { assume False: " \<not> monitor_tr (x # xs) form2 "
    hence False': "\<not> (x # xs) \<Turnstile>\<^sub>f form2" using case17 by auto
    from False case17 have eq1: " (x # xs) \<Turnstile>\<^sub>f form1 = monitor_tr (x # xs) form1" and
                     eq2: " xs \<Turnstile>\<^sub>f form1 U\<^sub>f form2 = monitor_tr_U xs form1 form2" by auto
    have *: " monitor_tr_U (x # xs) form1 form2 = (monitor_tr (x # xs) form1 \<and> monitor_tr_U xs form1 form2)"
      using False by auto
    have  " (x # xs) \<Turnstile>\<^sub>f form1 U\<^sub>f form2 = ((x # xs) \<Turnstile>\<^sub>f form1 \<and> xs \<Turnstile>\<^sub>f form1 U\<^sub>f form2)" using U_decompose[OF False', of "form1"]
      U_decompose'[OF False', of "form1"] by (rule) auto         
    hence ?case unfolding * eq1 eq2 by auto }  
  ultimately show ?case by auto 
qed
  
theorem  "semantics_ltlf \<xi> form = monitor_tr \<xi> form"  using monitoring by auto
      
end