theory Test_Code_Generation
imports
  Environment_Executable
begin                                                          

type_synonym segment = "(real*real)*real*real"
definition segment1::segment where
  "segment1 = ((0.0,0.0), (5.0,0.0))"
definition segment2::segment where
  "segment2 = ((0.0,0.0), (5.0,1.0))"
definition "reoi x = (real_of_int (int_of_integer x))"
definition "raoi i j = reoi i / reoi j"

ML \<open>
val segment_intersection = @{code segment_intersection}
val segment1 = @{code segment1}
val segment2 = @{code segment2}
val reoi = @{code reoi}
val raoi = @{code raoi}
fun mk_segment a b c d = ((reoi a, reoi b), (reoi c, reoi d))
val segment3 = mk_segment 0 1 2 3
\<close>
ML \<open>segment_intersection segment1 segment2\<close>
ML \<open>segment_intersection segment1 segment3\<close>

end