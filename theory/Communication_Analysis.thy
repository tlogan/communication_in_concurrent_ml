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
  "proc_legacy (.l # \<pi>) = []" |
  "proc_legacy (`l # \<pi>) = `l # (proc_legacy \<pi>)" |
  "proc_legacy (\<upharpoonleft>l # \<pi>) = \<upharpoonleft>l # (proc_legacy \<pi>)" |
  "proc_legacy (\<downharpoonleft>l # \<pi>) = \<downharpoonleft>l # (proc_legacy \<pi>)"

fun proc_spawn :: "control_path \<Rightarrow> control_path" where
  "proc_spawn [] = []" |
  "proc_spawn (.l # \<pi>) = (.l # \<pi>)" |
  "proc_spawn (`l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<upharpoonleft>l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<downharpoonleft>l # \<pi>) = (proc_spawn \<pi>)"

inductive two_paths_exclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  Base: "
    \<lbrakk>
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