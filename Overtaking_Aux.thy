theory Overtaking_Aux
imports Analysis
begin

(* type of finite sequence *)  
typedef (overloaded) 'a fin_seq = "{x::nat \<Rightarrow> 'a::zero. 
                                  \<exists>l. 0 \<le> l \<and> (\<forall>i. i < l \<longrightarrow> x i \<noteq> 0) \<and> (\<forall>k. l \<le> k \<longrightarrow> x k = 0)}"
  morphisms fin_seq_apply Abs_seq
  by (auto intro!: exI[where x="\<lambda>x. 0"])

setup_lifting type_definition_fin_seq
  
(* degree of a sequence --- taken from Fabian Immler Affine Arithmetic library *)  
definition degree ::"('a :: zero) fin_seq \<Rightarrow> nat"
  where "degree x = (LEAST i. \<forall>j\<ge>i. fin_seq_apply x j = 0)"
    
type_synonym real2 = "real \<times> real"
        
definition min2D :: "real2 \<Rightarrow> real2 \<Rightarrow> real2" where
  "min2D z1 z2 = (let x1 = fst z1; x2 = fst z2; y1 = snd z1; y2 = snd z2 in
                    if x1 < x2 then z1 else
                    if x1 = x2 then (if y1 \<le> y2 then z1 else z2) else
                    (* x1 > x2 *)   z2)"
  
theorem min2D_D:
  assumes "min2D x y = z"
  shows "fst z \<le> fst x \<and> fst z \<le> fst y"
  using assms unfolding min2D_def by smt
    
theorem min2D_D2:
  assumes "min2D x y = z"
  shows "z = x \<or> z = y"
  using assms unfolding min2D_def by presburger

theorem min2D_D3:
  assumes "min2D x y = x"
  shows "fst x < fst y \<or> (fst x = fst y \<and> snd x \<le> snd y)"
  using assms unfolding min2D_def by smt  
    
theorem min2D_D4:
  assumes "min2D x y = y"
  shows "fst y < fst x \<or> (fst x = fst y \<and> snd y \<le> snd x)"
  using assms unfolding min2D_def by smt 

    
    
end