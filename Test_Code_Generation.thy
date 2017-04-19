theory Test_Code_Generation
imports
  Environment_Executable
  "~~/src/HOL/Library/Code_Real_Approx_By_Float"
begin                                                          

text \<open>TODO: missing in \<open>Code_Real_Approx_By_Float\<close> or is there some deeper reason?
  Perhaps Florians recent (March/April 2017) changes to codegen?\<close>

lemmas
  real_less_eq_code[code del]
  real_less_code[code del]

text \<open>TODO: adapt \<open>Code_Real_Approx_By_Float\<close> and its @{const \<open>Realfract\<close>}
    to the "new" \<open>Code_Target_Int\<close> setup using @{typ integer}\<close>

definition Realfract :: "integer \<Rightarrow> integer \<Rightarrow> real"
  where "Realfract p q = real_of_integer p / real_of_integer q"

lemma [code]: "Ratreal r = (case (quotient_of r) of (x, y) \<Rightarrow>
  Test_Code_Generation.Realfract (integer_of_int x) (integer_of_int y))"
  by (cases r)
     (simp add: Realfract_def quotient_of_Fract of_rat_rat
       real_of_integer_def)

export_code segment_intersection in SML module_name Test file "code/segment_intersection.sml"

ML \<open>
val segment1 = ((0.0,0.0), (5.0,0.0));
val segment2 = ((0.0,0.0), (5.0,1.0));
\<close>
ML_file "code/segment_intersection.sml"
ML \<open>Test.segment_intersection segment1 segment2\<close>

end