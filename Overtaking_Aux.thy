theory Overtaking_Aux
  imports Analysis "Affine_Arithmetic/Polygon"
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
              
definition rotation_matrix' :: "real \<Rightarrow> real2 \<Rightarrow> real2" where
  "rotation_matrix' theta \<equiv>  (\<lambda>p :: real2. (cos theta * fst p - sin theta * snd p, 
                                             sin theta * fst p + cos theta * snd p))"

definition rotate_rect :: "rectangle \<Rightarrow> real2 \<Rightarrow> real2" where
  "rotate_rect rect \<equiv> (let centre = (Xcoord rect, Ycoord rect); ori = Orient rect in 
                              (\<lambda>p. p + centre) \<circ> (rotation_matrix' ori) \<circ> (\<lambda>p. p - centre))"  
  
(* the vertices are sorted in counter-clockwise manner *)    
definition get_vertices :: "rectangle \<Rightarrow> real2 list" where
  "get_vertices rect \<equiv> (let x = Xcoord rect; y = Ycoord rect; l = Length rect; w = Width rect in 
                          [(x - l / 2, y + w / 2),
                           (x - l / 2, y - w / 2),
                           (x + l / 2, y - w / 2),
                           (x + l / 2, y + w / 2)])"

definition get_vertices_zero :: "rectangle \<Rightarrow> real2 list" where
  "get_vertices_zero rect \<equiv> (let l = Length rect; w = Width rect in 
                          [(- l / 2,   w / 2),
                           (- l / 2, - w / 2),
                           (  l / 2, - w / 2),
                           (  l / 2,   w / 2)])"
    
theorem 
  assumes "vertices = get_vertices rect"
  assumes "0 < Length rect" and "0 < Width rect"  
  shows "ccw' (vertices ! 0) (vertices ! 1) (vertices ! 2)"
proof -
  define x where "x \<equiv> Xcoord rect"
  define y where "y \<equiv> Ycoord rect"
  define l where "l \<equiv> Length rect"
  define w where "w \<equiv> Width rect"      
  note params = x_def y_def l_def w_def
  from assms(2-3) have "0 < l" and "0 < w" unfolding params by auto  
  from assms have 0: "vertices ! 0 = (x - l / 2, y + w / 2)" and 1: "vertices ! 1 = (x - l/2, y - w/2)"
      and 2: "vertices ! 2 = (x + l /2, y - w / 2)"
    unfolding get_vertices_def Let_def params by auto
  have "ccw' (vertices ! 0) (vertices ! 1) (vertices ! 2) = 
        ccw' 0 (vertices ! 1 - vertices ! 0) (vertices ! 2 - vertices ! 0)" 
    unfolding ccw'_def using det3_translate_origin by auto    
  also have "... = ccw' 0 (0, -w) (l, -w)" unfolding 0 1 2 by auto
  finally have *: "ccw' (vertices ! 0) (vertices ! 1) (vertices ! 2) = ccw' 0 (0,-w) (l,-w)" by auto
  have "det3 0 (0,-w) (l,-w) =  w * l" unfolding det3_def'  by (auto simp add:algebra_simps)   
  with `0 < w` `0 < l` have "0 < det3 0 (0,-w) (l,-w)" by auto
  hence "ccw' 0 (0,-w) (l,-w)" unfolding ccw'_def by auto
  with * show ?thesis by auto  
qed  
  
theorem nbr_of_vertex:
  "length (get_vertices rect) = 4"
  unfolding get_vertices_def Let_def by auto 
    
theorem nbr_of_vertex_zero:
  "length (get_vertices_zero rect) = 4"
  unfolding get_vertices_zero_def Let_def by auto 
        
definition get_vertices_rotated :: "rectangle \<Rightarrow> real2 list" where
  "get_vertices_rotated rect \<equiv> map (rotation_matrix' (Orient rect)) (get_vertices_zero rect)"  
  
theorem nbr_of_vertex_rotated:
  "length (get_vertices_rotated rect) = 4"
  unfolding get_vertices_rotated_def using length_map nbr_of_vertex_zero by auto

definition get_vertices_rotated_translated :: "rectangle \<Rightarrow> real2 list" where
  "get_vertices_rotated_translated rect \<equiv> 
                               map (\<lambda>p. p + (Xcoord rect, Ycoord rect)) (get_vertices_rotated rect)"

theorem nbr_of_vertex_rotated_translated:
  "length (get_vertices_rotated_translated rect) = 4"
  unfolding get_vertices_rotated_translated_def using length_map nbr_of_vertex_rotated by auto  
        
definition get_lines :: "rectangle \<Rightarrow> (real2 \<times> real2) list" where
  "get_lines rect \<equiv> (let vertices = get_vertices_rotated_translated rect; 
                         zero = vertices ! 0; one = vertices ! 1; 
                         two = vertices ! 2; three = vertices ! 3                  
                      in 
                        [(zero, one), (one, two), (two, three), (three, zero)])"
  
theorem nbr_of_lines:
  "length (get_lines rect) = 4"
  unfolding get_lines_def unfolding Let_def by auto  
  
(* Definition of point inside a rectangle *)
definition inside_rectangle :: "real2 \<Rightarrow> rectangle \<Rightarrow> bool" where
  "inside_rectangle p rect \<equiv> (let lines = get_lines rect;
                                line0 = lines ! 0; line1 = lines ! 1; line2 = lines ! 2; line3 = lines ! 3
                              in 
                                ccw' p (fst line0) (snd line0) \<and> ccw' p (fst line1) (snd line1) \<and> 
                                ccw' p (fst line2) (snd line2) \<and> ccw' p (fst line3) (snd line3))"
                                        
theorem centre_point_inside: 
  assumes "0 < Length rect" and "0 < Width rect" 
  shows "inside_rectangle (Xcoord rect, Ycoord rect) rect"
proof -
  define x where "x \<equiv> Xcoord rect"
  define y where "y \<equiv> Ycoord rect"
  define l where "l \<equiv> Length rect"
  define w where "w \<equiv> Width rect"      
  note params = x_def y_def l_def w_def 
  from assms have "0 < l" and "0 < w" unfolding params by auto
      
  define zero where "zero \<equiv> get_vertices_rotated_translated rect ! 0"    
  define one where "one \<equiv> get_vertices_rotated_translated rect ! 1"
  define two where "two \<equiv> get_vertices_rotated_translated rect ! 2"
  define three where "three \<equiv> get_vertices_rotated_translated rect ! 3"
  note vertices_def = zero_def one_def two_def three_def  
  have "zero = rotation_matrix' (Orient rect) (- l / 2, w / 2) + (x,y)" and 
       "one = rotation_matrix' (Orient rect) (- l / 2, - w / 2) + (x,y)" and
       "two = rotation_matrix' (Orient rect) (l / 2, - w / 2) + (x,y)" and 
       "three = rotation_matrix' (Orient rect) (l / 2, w / 2) + (x,y)"
    unfolding vertices_def get_vertices_rotated_translated_def get_vertices_rotated_def
      get_vertices_zero_def Let_def params by auto      
  define line0 where "line0 \<equiv> get_lines rect ! 0"    
  define line1 where "line1 \<equiv> get_lines rect ! 1"
  define line2 where "line2 \<equiv> get_lines rect ! 2"
  define line3 where "line3 \<equiv> get_lines rect ! 3"
  note lines_def = line0_def line1_def line2_def line3_def    
  have "line0 = (zero,one)" "line1 = (one,two)" "line2 = (two, three)" "line3 = (three, zero)"
    unfolding lines_def get_lines_def Let_def vertices_def by auto
 
  have "ccw' (x,y) (fst line0) (snd line0)" sorry
  moreover      
  have "ccw' (x,y) (fst line1) (snd line1)" sorry
  moreover    
  have "ccw' (x,y) (fst line2) (snd line2)" sorry
  moreover
  have "ccw' (x,y) (fst line3) (snd line3)" sorry
  ultimately show ?thesis unfolding inside_rectangle_def Let_def params lines_def by auto      
qed
  
    
    
    
      
end