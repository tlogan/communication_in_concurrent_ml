theory Static_Communication_Analysis
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication_Analysis
begin

datatype node_label = NLet var | NResult var

fun nodeLabel :: "exp \<Rightarrow> node_label" where
  "nodeLabel (LET x = b in e) = NLet x" |
  "nodeLabel (RESULT y) = NResult y"

type_synonym node_set = "node_label set"

type_synonym node_map = "node_label \<Rightarrow> var set"

inductive may_be_static_send_node_label :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  Sync: "
    {^Chan xC} \<subseteq> V xSC \<Longrightarrow>
    {^Send_Evt xSC xM} \<subseteq> V xE \<Longrightarrow>
    is_super_exp e (LET x = SYNC xE in e') \<Longrightarrow>
    may_be_static_send_node_label V e xC (NLet x)
  "

inductive may_be_static_recv_node_label :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  Sync: "
    {^Chan xC} \<subseteq> V xRC \<Longrightarrow>
    {^Recv_Evt xRC} \<subseteq> V xE \<Longrightarrow>
    is_super_exp e (LET x = SYNC xE in e') \<Longrightarrow>
    may_be_static_recv_node_label V e xC (NLet x)
  "



lemma path_state_preserved_for_non_leaf: "
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' (\<pi> @ [l]) = Some \<sigma> \<Longrightarrow>
\<not> leaf E \<pi> \<Longrightarrow>
E (\<pi> @ [l]) = Some \<sigma>
"
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply presburger+
  apply (metis append1_eq_conv fun_upd_other)
  apply (metis butlast_snoc fun_upd_apply)
done


lemma spawn_point: "
  (E, H) \<rightarrow> (E', H') \<Longrightarrow>
  leaf E \<pi> \<Longrightarrow>
  E' (\<pi> @ [l1]) = Some \<sigma>1 \<Longrightarrow>
  E' (\<pi> @ [l2]) = Some \<sigma>2 \<Longrightarrow>
  l1 = l2 \<or> 
  (\<exists> x . l1 = (LNext x) \<and> l2 = (LSpawn x)) \<or>
  (\<exists> x . l1 = (LSpawn x) \<and> l2 = (LNext x))
"
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis (mono_tags, lifting) append1_eq_conv fun_upd_apply leaf.cases option.distinct(1) strict_prefixI')
  apply (smt butlast_snoc exp.inject(1) fun_upd_apply last_snoc leaf.cases option.distinct(1) option.inject state.inject strict_prefixI')
done

lemma isnt_send_evt_sound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> V x\<^sub>e
"
  apply (drule values_not_bound_sound; assumption?; auto)
done

lemma isnt_recv_evt_sound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> V x\<^sub>e
"
  apply (drule values_not_bound_sound; assumption?; auto)
done

lemma isnt_send_chan_sound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi> xC));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan xC \<in> V x\<^sub>s\<^sub>c
"
 apply (frule may_be_static_eval_to_pool)
 apply (drule may_be_static_eval_preserved_under_concur_step_star[of _ _ _ ]; assumption?)
 apply (erule may_be_static_eval_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule may_be_static_eval_state.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule may_be_static_eval_value.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ "(VChan (Ch \<pi> xC))"]; simp)
done

lemma isnt_recv_chan_sound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi> xC));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan xC \<in> V x\<^sub>r\<^sub>c
"
 apply (frule may_be_static_eval_to_pool)
 apply (drule may_be_static_eval_preserved_under_concur_step_star[of _ _ _ ]; assumption?)
 apply (erule may_be_static_eval_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule may_be_static_eval_state.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule may_be_static_eval_value.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>r\<^sub>c], drule spec[of _ "(VChan (Ch \<pi> xC))"]; simp)
done

lemma isnt_send_site_sound: "
  \<E>' \<pi>Sync = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>C xC)) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  may_be_static_send_node_label V e xC (NLet x\<^sub>y)
"
 apply (unfold may_be_static_send_node_label.simps; auto)
 apply (rule exI[of _ x\<^sub>s\<^sub>c]; auto)
 apply (auto simp: isnt_send_chan_sound)
 apply (rule exI[of _ x\<^sub>m]; auto?)
 apply (rule exI[of _ x\<^sub>e]; auto?)
 apply (blast dest: isnt_send_evt_sound)
 apply (rule exI; auto?)
 apply (erule isnt_exp_sound; auto)
done

lemma isnt_recv_site_sound: "
  \<E>' \<pi>Sync = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi>C xC)) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  may_be_static_recv_node_label V e xC (NLet x\<^sub>y)
"
 apply (unfold may_be_static_recv_node_label.simps; auto)
 apply (rule exI[of _ x\<^sub>r\<^sub>c]; auto)
 apply (auto simp: isnt_recv_chan_sound)
 apply (rule exI[of _ x\<^sub>e]; auto?)
 apply (blast dest: isnt_recv_evt_sound)
 apply (rule exI; auto?)
 apply (erule isnt_exp_sound; auto)
done

end
