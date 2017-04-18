section {* Test of the header *}

theory Hybrid_Trace
imports Complex_Main
begin

subsection {* declaration of continuous and discrete variables *}
 

type_synonym 'cv val = "'cv \<Rightarrow> real"
type_synonym 'cv act = "real \<Rightarrow> 'cv val" 

(* declaring jumps for discrete variable of natural numbers type *)
type_synonym ('disc_var, 'v) jumps = "'disc_var \<Rightarrow> 'v" 

(* event datatype: an event is either a continuous evolution or a discrete jump *)
datatype ('cv, 'dv, 'v) event = Cont real "'cv act" | Disc "('dv, 'v) jumps"

type_synonym ('cv, 'dv, 'v)trace = "('cv, 'dv, 'v)event list"

primrec currt :: "('cv, 'dv, 'v) trace \<Rightarrow> real" where
"currt [] = 0" | 
"currt (e # es) = (case e of 
  Disc _   \<Rightarrow> currt es 
| Cont d _ \<Rightarrow> (if 0 < d then (d + currt es) else currt es)
)"

fun no_zenon :: "('cv, 'dv, 'v) trace \<Rightarrow> bool" where
"no_zenon [] = True" | 
"no_zenon (e # es) = (case e of 
  Disc _ \<Rightarrow> True \<and> no_zenon es
| Cont d _ \<Rightarrow> (0 < d) \<and> no_zenon es 
)"

lemma always_non_zero : "0 \<le> currt es"
apply(induction es)
apply(simp_all)
apply(case_tac a)
apply(simp_all)
done

(* convert a list of events into a set which contains all the time points from that list *)
primrec event_list_to_time :: "('cv, 'dv, 'v) trace \<Rightarrow> real set" where
"event_list_to_time [] = {0}" | 
"event_list_to_time (e # es) = (let tt = (case e of Disc _ \<Rightarrow> {currt es} | 
                                               Cont d _ \<Rightarrow> {t::real . currt es < t \<and> t < currt es + d})
                           in tt \<union> event_list_to_time es)"

(* get the time interval for the head of the event list. If it is a discrete jump then it is 
   a set with single element only i.e. one specific time point. If it is a continuous 
   evolution then it is a time interval. *)
fun time_interval :: "('cv, 'dv, 'v) trace \<Rightarrow> real set" where
"time_interval [] = {0}" | 
"time_interval (e # es) = (case e of 
  Disc _ \<Rightarrow> {currt es}
| Cont d _ \<Rightarrow> (if 0 < d then {t::real . currt es < t \<and> t < currt es + d} else {})
)"

fun complete_interval :: "('cv, 'dv, 'v) trace \<Rightarrow> real set" where
"complete_interval [] = {0}" |
"complete_interval (e # es) = time_interval (e # es) \<union> complete_interval es"

lemma one_element: "{t::real . x \<le> t \<and> t \<le> x} = {x}"
apply(auto)
done

lemma mono_no_zenon: "no_zenon (a # e) \<Longrightarrow> no_zenon e" 
apply(auto)
apply(case_tac a)
apply(simp_all)
done

fun alternate:: "('cv, 'dv, 'v)trace \<Rightarrow> bool" where
"alternate [] = True" | 
"alternate [Disc _]   = False" | 
"alternate (Disc _   #  (e # es)) = (\<exists> d a . (e = Cont d a) \<and> alternate (e # es))" | 
"alternate (Cont _ _ #  (e # es)) = (\<exists> j   . (e = Disc j)   \<and> alternate (e # es))"

lemma mono_alternate: "alternate (a # e) \<Longrightarrow> alternate e"
apply(induction e)
apply(simp)
apply(case_tac a)
apply(simp)
apply(simp)
done

lemma cc_and_oo : "\<lbrakk>low\<^sub>1 \<le> up\<^sub>1; up\<^sub>1 < up\<^sub>2\<rbrakk> \<Longrightarrow> {t::real . low\<^sub>1 \<le> t \<and> t \<le> up\<^sub>1} \<union> {t::real . up\<^sub>1 < t \<and> t < up\<^sub>2} = {t :: real . low\<^sub>1 \<le> t \<and> t < up\<^sub>2}"
apply(auto)
done

lemma insert_co : "0 \<le> up \<Longrightarrow> insert up {t::real . 0 \<le> t \<and> t < up} = {t::real . 0 \<le> t \<and> t \<le> up}"
apply(auto)
done

lemma cover_r : "\<lbrakk>e \<noteq> []; no_zenon (e); alternate (e)\<rbrakk> \<Longrightarrow> ((\<exists> d a es. e = Cont d a # es) \<and> complete_interval (e) = {t::real. 0 \<le> t \<and> t < currt (e)}) 
                                                       \<or>   ((\<exists> j es . e = Disc j # es) \<and> complete_interval (e) = {t::real. 0 \<le> t \<and> t \<le> currt (e)})"
(*
apply(induction e)
apply(simp)
apply(case_tac a)
apply(subgoal_tac "no_zenon e")
apply(subgoal_tac "alternate e")
apply(subgoal_tac "complete_interval e = {t . 0 \<le> t \<and> t \<le> currt e}")
apply(simp)
apply(subgoal_tac "{t. 0 \<le> t \<and> t \<le> currt e} \<union> {t . currt e < t \<and> t < currt e + real} = {t . 0 \<le> t \<and> t < real + currt e}")
apply(blast)
apply(subgoal_tac "{t. 0 \<le> t \<and> t \<le> currt e} \<union> {t . currt e < t \<and> t < currt e + real} = {t . 0 \<le> t \<and> t < currt e + real}")
apply(simp)
apply(force)
apply(rule cc_and_oo)
apply(rule always_non_zero)
apply(arith)
defer
apply(drule_tac a="a" and e="e" in mono_alternate)
apply(assumption)
apply(rule_tac a="a" and e="e" in mono_no_zenon)
apply(assumption)
apply(rule disjI2)
apply(subgoal_tac "no_zenon e")
apply(subgoal_tac "alternate e")
apply(subgoal_tac "complete_interval e = {t . 0 \<le> t \<and> t < currt e}")
apply(simp)
apply(rule insert_co)
apply(rule always_non_zero)
defer
apply(drule_tac a="a" and e="e" in mono_alternate)
apply(assumption)
apply(rule_tac a="a" and e="e" in mono_no_zenon)
apply(assumption)
apply(simp_all)
defer
apply(force)
defer
apply(force)
*)
oops


lemma case_head : "\<lbrakk>e \<noteq> []; no_zenon (e); alternate (e)\<rbrakk> \<Longrightarrow> (\<exists> d a es. e = Cont d a # es)  \<or> (\<exists> j es . e = Disc j # es)"
apply(induction rule:alternate.induct)
apply(simp_all)
done

lemma case_head2: "\<lbrakk>e \<noteq> []; no_zenon e ; alternate e; (\<exists> d a es . e = Cont d a # es)\<rbrakk> \<Longrightarrow> \<not>(\<exists> j es . e = Disc j # es)"
apply(induction rule:alternate.induct)
apply(simp_all)
done

lemma case_head3: "\<lbrakk>e \<noteq> []; no_zenon e ; alternate e; (\<exists> j es . e = Disc j # es)\<rbrakk> \<Longrightarrow> \<not>(\<exists> d a es . e = Cont d a # es)"
apply(induction rule:alternate.induct)
apply(simp_all)
done

lemma cover_r2 : "\<lbrakk>e \<noteq> []; no_zenon (e); alternate (e); \<exists> j es . e = Disc j # es \<rbrakk> \<Longrightarrow> 
                                                      complete_interval (e) = {t::real. 0 \<le> t \<and> t \<le> currt (e)}"
(* apply(subgoal_tac " (\<exists> j es . e = Disc j # es) \<and> (complete_interval (e) = {t::real. 0 \<le> t \<and> t \<le> currt (e)})")
apply(rule_tac P=" \<exists> j es . e = Disc j # es" in conjunct2)
apply(assumption)
apply(subgoal_tac "((\<exists> d a es. e = Cont d a # es) \<and> complete_interval (e) = {t::real. 0 \<le> t \<and> t < currt (e)}) 
                                                       \<or>   ((\<exists> j es . e = Disc j # es) \<and> complete_interval (e) = {t::real. 0 \<le> t \<and> t \<le> currt (e)})")
apply(subgoal_tac "\<not>(\<exists> d a es. e = Cont d a # es)")
apply(blast)
apply(rule case_head3)
apply(assumption)
apply(assumption)
apply(assumption)
apply(assumption)
apply(rule cover_r)
apply(assumption)
apply(assumption)
apply(assumption)
done
 *)
oops

lemma cover_r3 : "\<lbrakk>e \<noteq> []; no_zenon (e); alternate (e); \<exists> d a es . e = Cont d a # es \<rbrakk> \<Longrightarrow> 
                                                      complete_interval (e) = {t::real. 0 \<le> t \<and> t < currt (e)}"
apply(subgoal_tac " (\<exists> d a es . e = Cont d a # es) \<and> (complete_interval (e) = {t::real. 0 \<le> t \<and> t < currt (e)})")
apply(rule_tac P=" \<exists> d a es . e = Cont d a  # es" in conjunct2)
apply(assumption)
apply(subgoal_tac "((\<exists> d a es. e = Cont d a # es) \<and> complete_interval (e) = {t::real. 0 \<le> t \<and> t < currt (e)}) 
                                                       \<or>   ((\<exists> j es . e = Disc j # es) \<and> complete_interval (e) = {t::real. 0 \<le> t \<and> t \<le> currt (e)})")
apply(subgoal_tac "\<not>(\<exists> j es. e = Disc j # es)")
apply(blast)
apply(rule case_head2)
apply(assumption)
apply(assumption)
apply(assumption)
apply(assumption)
oops
(* apply(rule cover_r)
apply(assumption)
apply(assumption)
apply(assumption)
done
 *)

lemma interval: "no_zenon e \<Longrightarrow> (\<exists> t\<^sub>1 t\<^sub>2 . 0 \<le> t\<^sub>1 \<and> 0 \<le> t\<^sub>2 \<and> t\<^sub>1 < t\<^sub>2 \<and> time_interval e = {t :: real . t\<^sub>1 < t \<and> t < t\<^sub>2}) \<or>
                 (\<exists> t\<^sub>3 . 0 \<le> t\<^sub>3 \<and> time_interval e = {t:: real . t\<^sub>3 \<le> t \<and> t \<le> t\<^sub>3})"
(*
apply(induction e)
apply(simp)
apply(rule disjI2)
apply(rule_tac x="0" in exI)
apply(simp)
apply(rule sym)
apply(rule one_element)
apply(case_tac a)
defer
apply(rule disjI2)
apply(simp)
apply(rule_tac x="currt e" in exI)
apply(rule conjI)
apply(rule always_non_zero)
apply(rule sym)
apply(rule one_element)
apply(rule disjI1)
apply(simp)
apply(rule_tac x="currt e" in exI)
apply(rule conjI)
apply(rule always_non_zero)
apply(rule_tac x="currt e + real" in exI)
apply(simp)
apply(subgoal_tac "0 \<le> currt e")
apply(simp)
apply(rule always_non_zero)
done
*)
oops

lemma interval1: "\<lbrakk>e = Disc j # es;  no_zenon e \<rbrakk> \<Longrightarrow> (\<exists> t\<^sub>3 . 0 \<le> t\<^sub>3 \<and> time_interval e = {t:: real . t\<^sub>3 \<le> t \<and> t \<le> t\<^sub>3})"
apply(simp)
apply(rule_tac x="currt es" in exI)
apply(rule conjI)
apply(rule always_non_zero)
apply(rule sym)
apply(rule one_element)
done

lemma interval2: "\<lbrakk>e = Cont d a # es; no_zenon e\<rbrakk>  \<Longrightarrow> (\<exists> t\<^sub>1 t\<^sub>2 . 0 \<le> t\<^sub>1 \<and> 0 \<le> t\<^sub>2 \<and> t\<^sub>1 < t\<^sub>2 \<and> time_interval e = {t :: real . t\<^sub>1 < t \<and> t < t\<^sub>2})"
apply(simp)
apply(rule_tac x="currt es" in exI)
apply(rule conjI)
apply(rule always_non_zero)
apply(rule_tac x="currt es + d" in exI)
apply(rule conjI)
apply(subgoal_tac "0 \<le> currt es")
apply(arith)
apply(rule always_non_zero)
apply(rule conjI)
apply(simp_all)
done

lemma myinf: "0 < d \<Longrightarrow> Inf {t::real . low < t \<and> t < low + d} = low"
oops

lemma mysup: "currt e = Sup (time_interval e)"
oops

lemma adjacency: "\<lbrakk>time_interval e\<^sub>1 = I\<^sub>1; no_zenon (a # e\<^sub>1); time_interval (a # e\<^sub>1) = I\<^sub>2\<rbrakk> \<Longrightarrow> 
                  Inf I\<^sub>2 = Sup I\<^sub>1"
(*
apply(case_tac a)
apply(auto)
apply(subgoal_tac "Inf {t. currt e\<^sub>1 < t \<and> t < currt e\<^sub>1 + real} = currt e\<^sub>1")
apply(simp)
apply(rule mysup)
apply(rule myinf)
apply(assumption)
apply(rule mysup)
done
*)
oops

locale state =
  fixes init_cv :: "'cv \<Rightarrow> real"
  fixes init_dv :: "'dv \<Rightarrow> 'v"
begin

fun disc_values :: "('cv, 'dv, 'v) trace \<Rightarrow> 'dv \<Rightarrow> 'v" where
"disc_values [] var = init_dv var" | 
"disc_values (e # es) var = (case e of 
  Disc j \<Rightarrow> j var
| Cont _ _ \<Rightarrow> disc_values es var
)"

fun disc_values_t :: "('cv, 'dv, 'v) trace \<Rightarrow> 'dv \<Rightarrow> real \<Rightarrow> 'v option" where
"disc_values_t [] v t = (if (t = 0) then Some (init_dv v) else None)" | 
"disc_values_t (e # es) v t = (if t \<in> time_interval (e # es) then
                                  (case e of 
                                    Disc j \<Rightarrow> Some (j v)
                                  | Cont _ _ \<Rightarrow> Some (disc_values es v))
                             else disc_values_t es v t)"

fun cont_values_currt :: "('cv, 'dv, 'v) trace \<Rightarrow> 'cv \<Rightarrow> real" where
"cont_values_currt [] v = (init_cv v)" | 
"cont_values_currt (e # es) v = (case e of
  Disc _   \<Rightarrow> cont_values_currt es v
| Cont d a \<Rightarrow> a d v
)"

fun cont_values :: "('cv, 'dv, 'v) trace \<Rightarrow> 'cv \<Rightarrow> real \<Rightarrow> real option" where
"cont_values [] v t = (if (t = 0) then Some (init_cv v) else None)" | 
"cont_values (e # es) v t = (if t \<in> time_interval (e # es) then 
                                  (case e of 
                                    Disc _ \<Rightarrow> Some (cont_values_currt es v)
                                  | Cont _ a \<Rightarrow> Some (a (t - currt es) v))
                                else cont_values es v t)"



lemma always_in_interval:"cont_values es var t = None \<Longrightarrow> t \<notin> complete_interval es"
(*
apply(induction es)
apply(simp)
apply(case_tac "t = 0")
apply(simp)
apply(simp)
apply(case_tac a)
apply(simp only:cont_values.simps)
apply(case_tac "t \<in> time_interval (Cont real fun # es)")
prefer 2
apply(simp)
apply(simp)
apply(simp only:cont_values.simps)
apply(case_tac "t \<in> time_interval (Disc fun # es)")
apply(simp)
defer
apply(simp)
done
*)
oops


lemma always_in_interval2 : "t \<in> complete_interval es \<Longrightarrow> cont_values es var t \<noteq> None"
(* apply(rule_tac Q="t \<in> complete_interval es" in contrapos_pn)
apply(assumption)
apply(rule_tac var="var" in always_in_interval)
apply(assumption)
done

 *)(*
apply(simp only:cont_values.simps)
apply(case_tac "t \<in> time_interval (a # es)")
defer
apply(simp)
apply(auto)
apply(case_tac a)
apply(simp)
*)
oops



fun disc_values_currt :: "('cv, 'dv, 'v) trace \<Rightarrow> 'dv \<Rightarrow> 'v" where
"disc_values_currt [] v = (init_dv v)" | 
"disc_values_currt (e # es) v = (case e of 
  Disc j   \<Rightarrow> j v
| Cont _ _ \<Rightarrow> disc_values_currt es v
)"

primrec cont_values_jumps :: "('cv, 'dv, 'v) trace \<Rightarrow> 'cv \<Rightarrow> real" where
"cont_values_jumps [] v = init_cv v" |
"cont_values_jumps (e # es) v = (case e of 
  Disc _   \<Rightarrow> cont_values_jumps es v
| Cont d a \<Rightarrow> a d v)"

fun is_discrete :: "('cv, 'dv, nat set + bool) trace \<Rightarrow> real \<Rightarrow> bool" where
"is_discrete [] t = (t = 0)" |
"is_discrete (e # es) t = (if t \<in> time_interval (e # es) then 
                              (case e of Disc _ \<Rightarrow> True | Cont _ _ \<Rightarrow> False) else
                              is_discrete es t)"

lemma inclusion: "t \<notin> complete_interval \<rho> \<Longrightarrow> \<not> is_discrete \<rho> t" 
apply(induction \<rho>)
apply(simp_all)
done

lemma "is_discrete \<rho> t \<Longrightarrow> t \<in> complete_interval \<rho>"
apply(subgoal_tac "\<not> t \<notin> complete_interval \<rho>")
apply(simp)
apply(rule notI)
apply(subgoal_tac "\<not> is_discrete \<rho> t")
apply(simp)
apply(rule inclusion)
apply(auto)
done


end

(*
datatype cont_vars =  x | y | z

fun init_cont_vars::"cont_vars \<Rightarrow> real" where
  "init_cont_vars x = 12.3"
| "init_cont_vars _ = 0"
hide_const (open) x y z

datatype disc_vars =  lane_id | brakelight| blinker

fun init_disc_vars::"disc_vars \<Rightarrow> nat set + bool" where
  "init_disc_vars lane_id = Inl {0::nat}"
| "init_disc_vars brakelight = Inr ( False)"
| "init_disc_vars blinker = Inr ( False)"

interpretation state init_cont_vars init_disc_vars .
print_theorems      
*)                 

end
