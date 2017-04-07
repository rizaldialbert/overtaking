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

section "Rectangle"    
  
record rectangle = 
  Xcoord :: real
  Ycoord :: real
  Orient :: real
  Length :: real
  Width  :: real  
    
print_record rectangle  

type_synonym rect_vertices = "real2 \<times> real2 \<times> real2 \<times> real2"  
  
fun get_first :: "rect_vertices \<Rightarrow> real2" where
  "get_first rv = fst rv"

fun get_snd :: "rect_vertices \<Rightarrow> real2" where
  "get_snd rv = fst (snd rv)" 
  
fun get_thrd :: "rect_vertices \<Rightarrow> real2" where
  "get_thrd rv = fst (snd (snd rv))"

fun get_frth :: "rect_vertices \<Rightarrow> real2" where
  "get_frth rv = snd (snd (snd rv))"  
    
definition rotation_matrix :: "rectangle \<Rightarrow> real2 \<Rightarrow> real2" where
  "rotation_matrix rect \<equiv> (let theta = Orient rect in
                           (\<lambda>p :: real2. (cos theta * fst p - sin theta * snd p, 
                                          sin theta * fst p + cos theta * snd p)))"
    
definition get_vertices :: "rectangle \<Rightarrow> real2 list" where
  "get_vertices rect \<equiv> (let x = Xcoord rect; y = Xcoord rect; l = Length rect; w = Width rect in 
                          [(x - l / 2, y + w / 2), (x + l / 2, y + w / 2), 
                           (x - l / 2, y - w / 2), (x + l / 2, y - w / 2)])"
  
theorem nbr_of_vertex:
  "length (get_vertices rect) = 4"
  unfolding get_vertices_def Let_def by auto    

definition get_vertices_rotated :: "rectangle \<Rightarrow> real2 list" where
  "get_vertices_rotated rect \<equiv> map (rotation_matrix rect) (get_vertices rect)"  
  
theorem nbr_of_vertex_rotated:
  "length (get_vertices_rotated rect) = 4"
  unfolding get_vertices_rotated_def using length_map nbr_of_vertex by auto
   
definition get_lines :: "rectangle \<Rightarrow> (real2 \<times> real2) list" where
  "get_lines rect \<equiv> (let vertices = get_vertices_rotated rect; 
                         zero = vertices ! 0; one = vertices ! 1; 
                         two = vertices ! 2; three = vertices ! 3                  
                      in 
                        [(zero, one), (one, two), (two, three), (three, zero)])"
      
end