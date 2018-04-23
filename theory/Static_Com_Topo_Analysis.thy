theory Static_Com_Topo_Analysis
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics 
    Static_Traceability 
    Dynamic_Com_Topo_Analysis
    Static_Live_Channel_Analysis
begin

definition is_static_send_path :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_send_path \<V> e x\<^sub>c \<pi>\<^sub>y \<equiv> (\<exists> x\<^sub>y x\<^sub>e x\<^sub>s\<^sub>c x\<^sub>m e\<^sub>n . 
    \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
  )"

definition is_static_recv_path :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_recv_path \<V> e x\<^sub>c \<pi>\<^sub>y \<equiv> (\<exists> x\<^sub>y x\<^sub>e x\<^sub>r\<^sub>c e\<^sub>n. 
    \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e
  )"

inductive inclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Ordered: "
    \<lbrakk>
      prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
    \<rbrakk> \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
 Spawn_Left: "
    \<pi> @ (LSpawn x) # \<pi>\<^sub>1 \<asymp> \<pi> @ (LNext x) # \<pi>\<^sub>2
 " |
 Spawn_Right: "
    \<pi> @ (LNext x) # \<pi>\<^sub>1 \<asymp> \<pi> @ (LSpawn x) # \<pi>\<^sub>2
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


(* need new definitions that consider all subprograms where x\<^sub>c is live*)
definition static_one_shot :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  "static_one_shot \<V> Ln x\<^sub>c e \<equiv> all (is_static_send_path \<V> (simplifyExp Ln e) x\<^sub>c) singular"

definition static_one_to_one :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow>  bool" where
  "static_one_to_one \<V> Ln x\<^sub>c e \<equiv> all (is_static_send_path \<V> (simplifyExp Ln e) x\<^sub>c) noncompetitive \<and> all (is_static_recv_path \<V> e x\<^sub>c) noncompetitive"

definition static_fan_out :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  "static_fan_out \<V> Ln x\<^sub>c e \<equiv> all (is_static_send_path \<V> (simplifyExp Ln e) x\<^sub>c) noncompetitive"

definition static_fan_in :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  "static_fan_in \<V> Ln x\<^sub>c e \<equiv> all (is_static_recv_path \<V> (simplifyExp Ln e) x\<^sub>c) noncompetitive"


end
