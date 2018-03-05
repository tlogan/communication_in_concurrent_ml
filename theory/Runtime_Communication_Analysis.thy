theory Runtime_Communication_Analysis
  imports Main Syntax Runtime_Semantics Static_Semantics
begin

definition is_send_path :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_send_path \<E> c \<pi>' \<equiv> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e e\<^sub>n \<kappa> \<rho> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e. 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<and>
    \<rho> x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>n; \<rho>(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>)
  )"

definition is_recv_path :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_recv_path \<E> c \<pi>' \<equiv> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e e\<^sub>n \<kappa> \<rho> x\<^sub>r\<^sub>c \<rho>\<^sub>e \<omega>. 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and> 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>n; \<rho>(x\<^sub>y \<mapsto> \<omega>); \<kappa>\<rangle>)
  )"


definition two_paths_ordered :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where 
  "two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2  = (prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1)"


lemma two_paths_ordered_commut: "
  two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> two_paths_ordered \<pi>\<^sub>2 \<pi>\<^sub>1
"
using two_paths_ordered_def by auto

definition all_ordered :: "(control_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "all_ordered P \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    P \<pi>\<^sub>1 \<longrightarrow>
    P \<pi>\<^sub>2 \<longrightarrow>
    two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2
  )"


definition all_paths_equal :: "(control_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "all_paths_equal P \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    P \<pi>\<^sub>1 \<longrightarrow>
    P \<pi>\<^sub>2 \<longrightarrow>
    \<pi>\<^sub>1 = \<pi>\<^sub>2
  )"


definition one_shot :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_shot \<E> c \<equiv> all_paths_equal (is_send_path \<E> c) \<and> all_paths_equal (is_recv_path \<E> c)"


definition one_to_one :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_to_one \<E> c \<equiv> all_ordered (is_send_path \<E> c) \<and> all_ordered (is_recv_path \<E> c)"
  

definition fan_out :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_out \<E> c \<equiv> all_ordered (is_send_path \<E> c)"
  

definition fan_in :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_in \<E> c \<equiv> all_ordered (is_recv_path \<E> c)"


end