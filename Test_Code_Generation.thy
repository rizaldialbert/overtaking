theory Test_Code_Generation
imports "~~/src/HOL/Library/Code_Real_Approx_By_Float" Environment_Executable
begin                                                          
  
export_code segment_intersection in SML file "code/segment_intersection.sml"
 
SML_file "code/segment_intersection.sml"
    
ML \<open>

val segment1 = ((0.0,0.0), (5.0,0.0));
val segment2 = ((0.0,1.0), (5.0,1.0));
\<close>  
  
  
  

end