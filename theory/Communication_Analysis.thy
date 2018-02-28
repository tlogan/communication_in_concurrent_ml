theory Communication_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin

definition send_paths :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_paths \<E> c \<equiv> {\<pi>\<^sub>y ;; `x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e e\<^sub>n \<kappa> \<rho> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e. 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<and>
    \<rho> x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>n; \<rho>(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>)
  }"

definition recv_paths :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_paths \<E> c \<equiv> {\<pi>\<^sub>y ;; `x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e e\<^sub>n \<kappa> \<rho> x\<^sub>r\<^sub>c \<rho>\<^sub>e \<omega>. 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>n; \<rho>(x\<^sub>y \<mapsto> \<omega>); \<kappa>\<rangle>)
  }"

definition two_paths_ordered :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where 
  "two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2  = (prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1)"

fun proc_legacy :: "control_path \<Rightarrow> control_path" where
  "proc_legacy [] = []" |
  "proc_legacy (.l # \<pi>) = `l # []" |
  "proc_legacy (`l # \<pi>) = `l # (proc_legacy \<pi>)" |
  "proc_legacy (\<upharpoonleft>l # \<pi>) = \<upharpoonleft>l # (proc_legacy \<pi>)" |
  "proc_legacy (\<downharpoonleft>l # \<pi>) = \<downharpoonleft>l # (proc_legacy \<pi>)"

fun proc_spawn :: "control_path \<Rightarrow> control_path" where
  "proc_spawn [] = []" |
  "proc_spawn (.l # \<pi>) = \<pi>" |
  "proc_spawn (`l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<upharpoonleft>l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<downharpoonleft>l # \<pi>) = (proc_spawn \<pi>)"

inductive two_paths_exclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  Base: "
    \<lbrakk>
      (proc_legacy \<pi>\<^sub>1) \<noteq> (proc_legacy \<pi>\<^sub>2);
      \<not> (two_paths_ordered (proc_legacy \<pi>\<^sub>1) (proc_legacy \<pi>\<^sub>2))
    \<rbrakk> \<Longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Induc: "
    \<lbrakk>
      (proc_legacy \<pi>\<^sub>1) = (proc_legacy \<pi>\<^sub>2);
      two_paths_exclusive (proc_spawn \<pi>\<^sub>1) (proc_spawn \<pi>\<^sub>1)
    \<rbrakk> \<Longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


lemma two_paths_exclusive_preserved_under_seq_cons: "
  two_paths_exclusive \<pi> \<pi>' \<Longrightarrow> two_paths_exclusive (`x # \<pi>) (`x # \<pi>')
"
by (smt Cons_prefix_Cons list.inject proc_legacy.simps(3) proc_spawn.simps(3) two_paths_exclusive.simps two_paths_ordered_def)

lemma two_paths_exclusive_preserved_under_up_cons: "
  two_paths_exclusive \<pi> \<pi>' \<Longrightarrow> two_paths_exclusive (\<upharpoonleft>x # \<pi>) (\<upharpoonleft>x # \<pi>')
"
by (smt Cons_prefix_Cons list.inject proc_legacy.simps(4) proc_spawn.simps(4) two_paths_exclusive.simps two_paths_ordered_def)

lemma two_paths_exclusive_preserved_under_down_cons: "
  two_paths_exclusive \<pi> \<pi>' \<Longrightarrow> two_paths_exclusive (\<downharpoonleft>x # \<pi>) (\<downharpoonleft>x # \<pi>')
"
by (smt Cons_prefix_Cons list.inject proc_legacy.simps(5) proc_spawn.simps(5) two_paths_exclusive.simps two_paths_ordered_def)

(*
theorem two_paths_exclusive_preserved_under_concat: "
  two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' \<Longrightarrow> two_paths_exclusive (\<pi> @ \<pi>\<^sub>1') (\<pi> @ \<pi>\<^sub>2')
"
sorry

theorem two_paths_ordered_commutative: "
  two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> two_paths_ordered \<pi>\<^sub>2 \<pi>\<^sub>1
"
using two_paths_ordered_def by blast

theorem two_paths_exclusive_commutative: "
  two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> two_paths_exclusive \<pi>\<^sub>2 \<pi>\<^sub>1
"
sorry
*)

definition two_paths_noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  "two_paths_noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 = (two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2)"

lemma "
  \<forall> \<pi>\<^sub>b \<pi>\<^sub>b' . two_paths_noncompetitive \<pi>\<^sub>b \<pi>\<^sub>b' \<longrightarrow>
  \<not> prefix \<pi>\<^sub>b (\<pi> @ \<pi>\<^sub>b') \<longrightarrow> \<not> prefix (\<pi> @ \<pi>\<^sub>b') \<pi>\<^sub>b \<longrightarrow>
  two_paths_exclusive \<pi>\<^sub>b (\<pi> @ \<pi>\<^sub>b')
"
 apply (induct \<pi>; auto)
  apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def)
  apply (drule_tac x = \<pi>\<^sub>b in spec; auto?)
  apply (drule_tac x = \<pi>\<^sub>b' in spec; auto?)
  apply (case_tac \<pi>\<^sub>b; auto)
sorry

theorem double_append_exclusive: "
  (\<forall> \<pi>\<^sub>a' \<pi>\<^sub>b \<pi>\<^sub>b'.
    two_paths_noncompetitive  \<pi>\<^sub>a \<pi>\<^sub>a' \<longrightarrow> two_paths_noncompetitive \<pi>\<^sub>b \<pi>\<^sub>b' \<longrightarrow>
    \<not> prefix (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b') \<longrightarrow> \<not> prefix (\<pi>\<^sub>a' @ \<pi>\<^sub>b') (\<pi>\<^sub>a @ \<pi>\<^sub>b) \<longrightarrow>
    two_paths_exclusive (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b')
  )
"
 apply (induct \<pi>\<^sub>a; auto; simp?)
  apply (case_tac \<pi>\<^sub>a'; auto)
   apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def; auto)
  apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def; auto)
    
sorry

theorem noncompetitive_preserved_under_double_append: "
 two_paths_noncompetitive  \<pi>\<^sub>a \<pi>\<^sub>a' \<Longrightarrow> two_paths_noncompetitive \<pi>\<^sub>b \<pi>\<^sub>b' \<Longrightarrow> two_paths_noncompetitive (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b')
"
 apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def; blast?)
 apply (case_tac "prefix (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b')"; blast?) 
 apply (case_tac" prefix (\<pi>\<^sub>a' @ \<pi>\<^sub>b') (\<pi>\<^sub>a @ \<pi>\<^sub>b)"; blast?)
 apply (rule disjI2, rule disjI2) 
 apply (simp add: double_append_exclusive two_paths_noncompetitive_def two_paths_ordered_def)
done

definition set_noncompetitive  :: "control_path set \<Rightarrow> bool" where
  "set_noncompetitive \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    two_paths_noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  )"

definition set_exclusive :: "control_path set \<Rightarrow> bool"  where
  "set_exclusive \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 . 
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow> 
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  )"


definition one_shot :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_shot \<E> c \<equiv> set_exclusive (send_paths \<E> c) \<and> set_exclusive (recv_paths \<E> c)"


definition one_to_one :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_to_one \<E> c \<equiv> set_noncompetitive (send_paths \<E> c) \<and> set_noncompetitive (recv_paths \<E> c)"
  
definition fan_out :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_out \<E> c \<equiv> set_noncompetitive (send_paths \<E> c)"
  
definition fan_in :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_in \<E> c \<equiv> set_noncompetitive (recv_paths \<E> c)"


end