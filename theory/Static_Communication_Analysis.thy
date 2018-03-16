theory Static_Communication_Analysis
  imports Main Syntax Runtime_Semantics Static_Semantics Runtime_Communication_Analysis
begin

definition is_static_send_path :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_send_path \<A> x\<^sub>c \<pi>' \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>s\<^sub>c x\<^sub>m e\<^sub>n . 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
    {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
  )"

definition is_static_recv_path :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_recv_path \<A> x\<^sub>c \<pi>' \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>r\<^sub>c e\<^sub>n \<omega>. 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e \<and>
    {|\<omega>|} \<subseteq> \<V> x\<^sub>y
  )"

(*  

Reppy/Xiao analyze the subprogram within which a channel is live, 
thus avoiding conflating different instances of a channel with one name, 
such as one created in a loop.

Reppy/Xiao do not distinguish between paths that 
occur in the same run from those that occur in the same subprogram.

Reppy/Xiao consider paths with the same process path to be noncompetitive statically.

*)

inductive inclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Ordered: "
    \<lbrakk>
      prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
    \<rbrakk> \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
 Spawn_Left: "
    \<pi> @ .x # \<pi>\<^sub>1 \<asymp> \<pi> @ `x # \<pi>\<^sub>2
 " |
 Spawn_Right: "
    \<pi> @ `x # \<pi>\<^sub>1 \<asymp> \<pi> @ .x # \<pi>\<^sub>2
 "

lemma inclusive_commut: "
  \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>2 \<asymp> \<pi>\<^sub>1
"
 apply (erule inclusive.cases; auto)
  apply (simp add: Ordered)
  apply (simp add: Ordered)
  apply (simp add: Spawn_Right)
  apply (simp add: Spawn_Left)
done



lemma inclusive_preserved_under_unordered_extension: "
  \<not> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> \<not> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow> \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 ;; l \<asymp> \<pi>\<^sub>2
"
 apply (erule inclusive.cases; auto)
  apply (simp add: Spawn_Left)
  apply (simp add: Spawn_Right)
done



definition singular :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "singular \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"

definition noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"

definition static_one_shot :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_shot \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) singular \<and> all (is_static_recv_path \<A> x\<^sub>c) singular"

definition static_one_to_one :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_to_one \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) noncompetitive \<and> all (is_static_recv_path \<A> x\<^sub>c) noncompetitive"

definition static_fan_out :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_out \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) noncompetitive"

definition static_fan_in :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_in \<A> x\<^sub>c \<equiv> all (is_static_recv_path \<A> x\<^sub>c) noncompetitive"


end
