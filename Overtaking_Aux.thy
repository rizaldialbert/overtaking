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
    

end