theory Communication_Topology_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Topology_Analysis
begin


lemma xyz: "
  \<lbrakk> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<longrightarrow> \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (rule impI)
 apply (erule flow_sound[of \<V> \<C> e \<E>'], auto)
done

theorem topology_one_shot_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_one_shot (\<V>, \<C>, e) x \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x)
"
sorry

theorem topology_one_to_one_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_one_to_one (\<V>, \<C>, e) x \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x) \<or> one_to_one \<E>' (Ch \<pi> x)
"
sorry

theorem topology_fan_out_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_fan_out (\<V>, \<C>, e) x \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x) \<or> one_to_one \<E>' (Ch \<pi> x) \<or> fan_out \<E>' (Ch \<pi> x)
"
sorry

theorem topology_fan_in_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_fan_in (\<V>, \<C>, e) x \<Longrightarrow>
  
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x) \<or> one_to_one \<E>' (Ch \<pi> x) \<or> fan_in \<E>' (Ch \<pi> x)
"
sorry


lemma non_precise: "
  Non \<preceq> t
"  
 apply (cases t, auto)
      apply (rule precision_order.Refl)
     apply (rule precision_order.Edge0)
    apply (
      rule precision_order.Trans[of "Non" "OneShot" "OneToOne"],
      rule precision_order.Edge0, rule precision_order.Edge1
    )
   apply (
     rule precision_order.Trans[of "Non" "OneShot" "FanOut"], rule precision_order.Edge0,
     rule precision_order.Trans[of "OneShot" "OneToOne" "FanOut"], rule precision_order.Edge1,
     rule precision_order.Edge2
   )
  apply (
    rule precision_order.Trans[of "Non" "OneShot" "FanIn"], rule precision_order.Edge0,
    rule precision_order.Trans[of "OneShot" "OneToOne" "FanIn"], rule precision_order.Edge1,
    rule precision_order.Edge3
  )
 apply (
   rule precision_order.Trans[of "Non" "OneShot" "Many"], rule precision_order.Edge0,
   rule precision_order.Trans[of "OneShot" "OneToOne" "Many"], rule precision_order.Edge1,
   rule precision_order.Trans[of "OneToOne" "FanOut" "Many"], rule precision_order.Edge2,
   rule precision_order.Edge4
 )
done

lemma one_shot_precise: "
  (x, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x) \<Longrightarrow> 
  OneShot \<preceq> t
"  
sorry

lemma one_to_one_precise: "
  (x, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> 
  \<not> one_shot \<E>' (Ch \<pi> x) \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> x) \<Longrightarrow> 
  OneToOne \<preceq> t
"
sorry

theorem topology_pair_sound : "
  \<lbrakk>
    (x, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'; x\<rangle>\<rangle> \<preceq> t
"
 apply (unfold var_to_topo_def, unfold var_topo_def)
 apply (cases "\<nexists>\<pi> e' \<rho>' \<kappa>'. \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>)")
  apply (simp, rule non_precise)
 apply (cases "var_topo one_shot \<E>' x"; unfold var_topo_def)
  apply (simp, erule exE, erule allE, erule impE, simp, (erule exE)+) 
  apply (rule one_shot_precise; auto)
 apply (cases "var_topo one_to_one \<E>' x"; unfold var_topo_def)
  apply (simp, rule conjI)
   apply (
    rule impI,
    thin_tac "\<exists>\<pi>. (\<exists>e' \<rho>' \<kappa>'. \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>)) \<and> \<not> one_shot \<E>' (Ch \<pi> x)",
    thin_tac "\<forall>\<pi>. (\<exists>e' \<rho>' \<kappa>'. \<E>' \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>)) \<longrightarrow> one_to_one \<E>' (Ch \<pi> x)",
    erule exE, erule allE, erule impE, simp, (erule exE)+
   ) 
   apply (rule one_shot_precise; auto)
  

(*
, erule exE, erule allE, erule impE, simp, (erule exE)+, rule conjI)
   apply (rule impI, rule one_shot_precise; auto)
  apply (erule conjE, (erule exE)+)
  apply (erule one_to_one_precise; auto)
*)
  

       
sorry


lemma topology_sound': "
  (x, \<A> x) \<TTurnstile> e \<Longrightarrow> [[] \<mapsto> \<langle>e; Map.empty; []\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> (\<langle>\<langle>\<E>'\<rangle>\<rangle>) x \<preceq> \<A> x
"
 apply (drule topology_pair_sound, simp)
 apply (unfold state_pool_to_topo_env_def, auto)
done


theorem topology_sound : "
  \<lbrakk>
    \<A> \<bind> e;
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'\<rangle>\<rangle> \<sqsubseteq>\<^sub>t \<A>
"
 apply (unfold topo_accept_def)
 apply (unfold topo_env_precision_def)
 apply (intro allI, drule spec)
 apply (erule topology_sound', auto)
done

end