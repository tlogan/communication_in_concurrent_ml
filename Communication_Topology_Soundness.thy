theory Communication_Topology_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Topology_Analysis
begin

lemma "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e  e; 
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
by (erule Abstract_Value_Flow_Soundness.flow_sound)

lemma xyz: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>l = b in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  e \<noteq> RESULT x
"
 apply (erule star.cases; auto)
  apply (case_tac "\<pi> = []"; auto)
 apply (erule concur_step.cases)
  apply (metis exp.distinct(1) fun_upd_apply option.distinct(1) option.inject state.inject)
  apply (metis fun_upd_apply option.distinct(1) option.inject state.inject)
  apply (metis exp.simps(4) fun_upd_apply option.distinct(1) option.inject state.inject)+
done

lemma "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = b in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>) \<Longrightarrow>
  \<V> \<tturnstile> (\<pi>\<^sub>y;;x\<^sub>y) \<triangleleft> e
"
sorry

lemma topology_send_sound': "

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>

  \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>) \<Longrightarrow> 
  \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace> \<Longrightarrow> 
  \<E>' (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>) \<Longrightarrow> 

  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>

  \<V> \<tturnstile> (\<pi>\<^sub>y;;x\<^sub>y) \<triangleleft> e \<and>
  (LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y) \<unlhd> e \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c

"
 apply (auto)
(*
 apply (frule Abstract_Value_Flow_Soundness.flow_sound[of _ _ _ _ \<pi>]; drule Abstract_Value_Flow_Soundness.flow_sound[of _ _ _ _ \<pi>\<^sub>y]; blast?; assumption?)
 apply (unfold abstract_value_env_precision_def)
 apply (unfold env_to_abstract_value_env_def)
 apply (drule spec)
 apply (drule spec[of _ x\<^sub>e])
 apply (case_tac "\<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>"; simp)

 apply (rule conjI)+
  apply ((cases \<pi>\<^sub>y); auto)
*)


sorry

lemma topology_send_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<pi>\<^sub>y \<in> send_paths \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  \<pi>\<^sub>y \<in> abstract_send_paths (\<V>, \<C>, e) x\<^sub>c
"
 apply (unfold send_paths_def abstract_send_paths_def abstract_send_sites_def abstract_paths_def; auto)
  apply (rule exI, rule exI, rule conjI, rule exI)
   apply (frule topology_send_sound'; blast?; assumption?; blast)
  apply (frule topology_send_sound'; blast?; assumption?; blast)
 apply (frule topology_send_sound'; blast?; assumption?; blast)
done


theorem topology_single_path_send_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  single_path (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c) \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  single_path (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_path_def; auto; erule allE; erule impE)
  apply (drule topology_send_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule topology_send_sound; auto)
 apply (drule topology_send_sound; auto)
done


(****)

lemma topology_recv_sound': "

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>

  \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>) \<Longrightarrow> 
  \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>s\<^sub>c, \<rho>\<^sub>e\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace> \<Longrightarrow> 
  \<E>' (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<omega>);\<kappa>\<^sub>y\<rangle>) \<Longrightarrow> 

  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>

  \<V> \<tturnstile> (\<pi>\<^sub>y;;x\<^sub>y) \<triangleleft> e \<and>
  (LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y) \<unlhd> e \<and>
  ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>e \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
  \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>y
"
sorry

lemma topology_recv_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<pi>\<^sub>y \<in> recv_paths \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  \<pi>\<^sub>y \<in> abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c
"
 apply (unfold recv_paths_def abstract_recv_paths_def abstract_recv_sites_def abstract_paths_def; auto)
  apply (rule exI, rule exI, rule conjI, rule exI)
   apply (frule topology_recv_sound'; blast?; assumption?; blast)
  apply (frule topology_recv_sound'; blast?; assumption?; blast)
 apply (frule topology_recv_sound'; blast?; assumption?; blast)
done

theorem topology_single_path_recv_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  single_path (abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c) \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  single_path (recv_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_path_def; auto; erule allE; erule impE)
  apply (drule topology_recv_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule topology_recv_sound; auto)
 apply (drule topology_recv_sound; auto)
done


theorem topology_one_shot_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_one_shot (\<V>, \<C>, e) x\<^sub>c \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_one_shot_def, auto)
 apply (unfold one_shot_def, auto)
  apply (erule topology_single_path_send_sound; auto)
  apply (erule topology_single_path_recv_sound; auto)
done


theorem topology_single_proc_send_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  single_proc (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c) \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  single_proc (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_proc_def; auto; erule allE; erule impE)
  apply (drule topology_send_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule topology_send_sound; auto)
 apply (drule topology_send_sound; auto)
done

theorem topology_single_proc_recv_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  single_proc (abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c) \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  single_proc (recv_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_proc_def; auto; erule allE; erule impE)
  apply (drule topology_recv_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule topology_recv_sound; auto)
 apply (drule topology_recv_sound; auto)
done

theorem topology_one_to_one_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_one_to_one (\<V>, \<C>, e) x\<^sub>c \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_one_to_one_def, auto)
 apply (unfold one_to_one_def, auto)
  apply (erule topology_single_proc_send_sound; auto)
  apply (erule topology_single_proc_recv_sound; auto)
done

theorem topology_fan_out_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_fan_out (\<V>, \<C>, e) x\<^sub>c \<Longrightarrow>

  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_fan_out_def)
 apply (unfold fan_out_def)
  apply (erule topology_single_proc_send_sound; auto)
done

theorem topology_fan_in_sound: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  abstract_fan_in (\<V>, \<C>, e) x\<^sub>c \<Longrightarrow>
  
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_fan_in_def)
 apply (unfold fan_in_def)
  apply (erule topology_single_proc_recv_sound; auto)
done

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
   rule precision_order.Trans[of "Non" "OneShot" "ManyToMany"], rule precision_order.Edge0,
   rule precision_order.Trans[of "OneShot" "OneToOne" "ManyToMany"], rule precision_order.Edge1,
   rule precision_order.Trans[of "OneToOne" "FanOut" "ManyToMany"], rule precision_order.Edge2,
   rule precision_order.Edge4
 )
done

lemma one_shot_precise: "
  (x\<^sub>c, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  OneShot \<preceq> t
"  
 apply (erule topo_pair_accept.cases; auto)
     apply (rule precision_order.Refl)
    apply (rule precision_order.Edge1)
   apply (
    rule precision_order.Trans[of "OneShot" "OneToOne" "FanOut"], rule precision_order.Edge1,
    rule precision_order.Edge2
   )
  apply (
   rule precision_order.Trans[of "OneShot" "OneToOne" "FanIn"], rule precision_order.Edge1,
   rule precision_order.Edge3
  )
 apply (
   rule precision_order.Trans[of "OneShot" "OneToOne" "ManyToMany"], rule precision_order.Edge1,
   rule precision_order.Trans[of "OneToOne" "FanOut" "ManyToMany"], rule precision_order.Edge2,
   rule precision_order.Edge4
 )
done

lemma one_to_one_precise: "
  (x\<^sub>c, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> 
  \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  OneToOne \<preceq> t
"
 apply (erule topo_pair_accept.cases; auto)
     apply (drule topology_one_shot_sound; auto)
    apply (rule precision_order.Refl)
   apply (rule precision_order.Edge2)
  apply (rule precision_order.Edge3)
 apply (
   rule precision_order.Trans[of "OneToOne" "FanOut" "ManyToMany"], rule precision_order.Edge2,
   rule precision_order.Edge4
 )
done


lemma fan_out_precise: "
  (x\<^sub>c, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> 
  \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow>
  \<not> one_to_one \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  fan_out \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  FanOut \<preceq> t
"
 apply (erule topo_pair_accept.cases; auto)
     apply (drule topology_one_shot_sound; auto)
    apply (drule topology_one_to_one_sound; auto)
   apply (rule precision_order.Refl)
   apply (drule topology_fan_in_sound; blast?; (simp add: one_shot_def one_to_one_def fan_out_def fan_in_def)?; auto)
 apply (rule precision_order.Edge4)
done

lemma fan_in_precise: "
  (x\<^sub>c, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> 
  \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow>
  \<not> one_to_one \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  fan_in \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  FanIn \<preceq> t
"
 apply (erule topo_pair_accept.cases; auto)
     apply (drule topology_one_shot_sound; auto)
    apply (drule topology_one_to_one_sound; auto)
   apply (drule topology_fan_out_sound; blast?; (simp add: one_shot_def one_to_one_def fan_out_def fan_in_def)?; auto)
  apply (rule precision_order.Refl)
 apply (rule precision_order.Edge5)
done

lemma many_to_many_precise: "
  (x\<^sub>c, t) \<TTurnstile> e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> 
  \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> \<not> one_to_one \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  \<not> fan_out \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> \<not> fan_in \<E>' (Ch \<pi> x\<^sub>c) \<Longrightarrow> 
  ManyToMany \<preceq> t
"
 apply (erule topo_pair_accept.cases; auto)
     apply (drule topology_one_shot_sound; auto)
    apply (drule topology_one_to_one_sound; auto)
   apply (drule topology_fan_out_sound; auto; (simp add: one_to_one_def fan_in_def fan_out_def))
  apply (drule topology_fan_in_sound; auto; (simp add: one_to_one_def fan_in_def fan_out_def))
 apply (rule precision_order.Refl)
done

theorem topology_pair_sound : "
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'; \<pi>; x\<^sub>c\<rangle>\<rangle> \<preceq> t
"
 apply (unfold var_to_topo_def)
 apply (cases "\<nexists> e' \<rho>' \<kappa>'. \<E>' \<pi> = Some (\<langle>LET x\<^sub>c = CHAN \<lparr>\<rparr> in e';\<rho>';\<kappa>'\<rangle>)")
  apply (simp, rule non_precise)
 apply (cases "one_shot \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp, (erule exE)+) 
  apply (rule one_shot_precise; auto)
 apply (cases "one_to_one \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp, (erule exE)+) 
  apply (rule one_to_one_precise; auto)
 apply (cases "fan_out \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp, (erule exE)+) 
  apply (rule fan_out_precise; auto)
 apply (cases "fan_in \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp, (erule exE)+) 
  apply (rule fan_in_precise; auto)
 apply (simp, (erule exE)+) 
 apply (rule many_to_many_precise; auto)    
done


theorem topology_sound : "
  \<lbrakk>
    \<A> \<bind> e;
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'; \<pi>\<rangle>\<rangle> \<sqsubseteq>\<^sub>t \<A>
"
 apply (unfold topo_accept_def)
 apply (unfold topo_env_precision_def)
 apply (intro allI, drule spec)
 apply (drule topology_pair_sound, simp)
 apply (unfold state_pool_to_topo_env_def, auto)
done

end