theory Communication_Topology_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Topology_Analysis
begin

lemma path_not_reachable_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>LET x = b in e';\<rho>';\<kappa>'\<rangle>) 
  \<rbrakk> \<Longrightarrow>
  (\<V>, e) :\<downharpoonright> (\<pi>;;x)
"
sorry

lemma exp_not_reachable_sound'': "
  \<lbrakk>
    \<E>\<^sub>m \<rightarrow> \<E>';
    (\<V>, \<E>) \<downharpoonright>\<downharpoonright> \<E>\<^sub>m;
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<^sub>m 
  \<rbrakk> \<Longrightarrow> 
  (\<V>, \<E>) \<downharpoonright>\<downharpoonright> \<E>'
"
sorry

lemma exp_not_reachable_sound': "
  \<lbrakk>
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<E>) \<downharpoonright>\<downharpoonright> \<E>'
"
 apply (drule star_implies_star_left)
 apply (erule star_left.induct[of concur_step], auto)
  apply (rule pool_reachable.Any, auto)
  using exp_reachable.Refl apply blast
  apply (rename_tac \<E>' \<E>\<^sub>m \<E>)
  apply (drule star_left_implies_star)
  apply (drule flow_preservation_star; assumption?)
  apply (drule exp_not_reachable_sound''; auto)
done

lemma exp_to_pool_reachable: "
  \<lbrakk>
    (\<V>, \<E>) \<downharpoonright>\<downharpoonright> \<E>';
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  (\<exists> \<pi> e \<rho> \<kappa> . 
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<and>
    prefix \<pi> \<pi>' \<and>
    (\<V>, e) \<downharpoonright> e'
  )
"
 apply (erule pool_reachable.cases; auto)
done

lemma exp_not_reachable_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) 
  \<rbrakk> \<Longrightarrow>
  (\<V>, e) \<downharpoonright> e'
"
 apply (insert exp_to_pool_reachable[of \<V> "[[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" \<E>' \<pi>' e' \<rho>' \<kappa>'], auto)
 apply (erule meta_impE, auto)
 apply (drule lift_flow_exp_to_pool)
 apply (drule exp_not_reachable_sound', auto)
 apply (metis option.inject option.simps(3) state.inject)
done

lemma abstract_chan_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>
  \<rbrakk> \<Longrightarrow> 
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c
"
 apply (frule lift_flow_exp_to_pool)
 apply (drule flow_preservation_star[of _ _ _ \<E>']; assumption?)
 apply (erule accept_state_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule accept_state.cases; auto)
 apply (erule accept_val_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>"]; simp)
 apply (erule conjE)
 apply (erule accept_value.cases; auto)
 apply (erule accept_val_env.cases; auto)
 apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ "\<lbrace>Ch \<pi> x\<^sub>c\<rbrace>"]; simp)
done

lemma abstract_send_evt_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> 
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto)
done

lemma abstract_unit_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' (\<pi>\<^sub>y ;; x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>)
  \<rbrakk> \<Longrightarrow> 
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y
"
 apply (drule isnt_abstract_value_sound_coro; assumption?; auto; simp)
done

lemma abstract_message_isnt_sent_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>;
    \<E>' (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e\<^sub>y; \<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>y\<rangle>)
  \<rbrakk> \<Longrightarrow> 
  \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
"
  apply (frule lift_flow_exp_to_pool)
  apply (drule flow_preservation_star[of _ _ _ \<E>']; assumption?)
  apply (erule accept_state_pool.cases; auto)
  apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
  apply (erule accept_state.cases; auto)
  apply (erule accept_exp.cases[of _ "LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y"]; auto)
  apply (thin_tac "\<forall>x\<^sub>r\<^sub>c. ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>y)")
  apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ x\<^sub>m])
  apply (frule abstract_send_evt_doesnt_exist_sound; assumption?)
  apply (erule impE; simp)
  apply (drule spec[of _ x\<^sub>c])
  apply (drule abstract_chan_doesnt_exist_sound; assumption?; auto)
done

lemma isnt_send_path_sound': "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>;
    \<E>' (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>) 
  \<rbrakk> \<Longrightarrow> 

  (\<V>, e) :\<downharpoonright> (\<pi>\<^sub>y;;x\<^sub>y) \<and>
  (\<V>, e) \<downharpoonright> (LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y) \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c

"
 apply (rule conjI, (erule path_not_reachable_sound; assumption))
 apply (rule conjI, (erule exp_not_reachable_sound; assumption))
 apply (rule conjI, (erule abstract_chan_doesnt_exist_sound; assumption))
 apply (rule conjI, (erule abstract_send_evt_doesnt_exist_sound; assumption))
 apply (rule conjI, (erule abstract_unit_doesnt_exist_sound; assumption))
 apply (drule abstract_message_isnt_sent_sound; assumption)
done

lemma isnt_send_path_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<pi>\<^sub>y \<in> send_paths \<E>' (Ch \<pi> x\<^sub>c)
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>y \<in> abstract_send_paths (\<V>, \<C>, e) x\<^sub>c
"
 apply (unfold send_paths_def abstract_send_paths_def abstract_send_sites_def abstract_paths_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_send_path_sound'; assumption?; auto; blast)
  apply (frule isnt_send_path_sound'; assumption?; blast)
 apply (frule isnt_send_path_sound'; assumption?; blast)
done


theorem topology_single_path_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    single_path (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  single_path (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_path_def; auto; erule allE; erule impE)
  apply (drule isnt_send_path_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule isnt_send_path_sound; auto)
 apply (drule isnt_send_path_sound; auto)
done

(****)

lemma topology_recv_sound': "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>); 
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>s\<^sub>c, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>;
    \<E>' (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<omega>);\<kappa>\<^sub>y\<rangle>) 
  \<rbrakk> \<Longrightarrow> 

  (\<V>, e) :\<downharpoonright> (\<pi>\<^sub>y;;x\<^sub>y) \<and>
  (\<V>, e) \<downharpoonright> (LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y) \<and>
  ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>e \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
  \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>y
"
sorry

lemma topology_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    \<pi>\<^sub>y \<in> recv_paths \<E>' (Ch \<pi> x\<^sub>c) 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>y \<in> abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c
"
 apply (unfold recv_paths_def abstract_recv_paths_def abstract_recv_sites_def abstract_paths_def; auto)
  apply (rule exI, rule conjI)
   apply (frule topology_recv_sound'; blast?; assumption?; blast)
  apply (frule topology_recv_sound'; blast?; assumption?; blast)
 apply (frule topology_recv_sound'; blast?; assumption?; blast)
done

theorem topology_single_path_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    single_path (abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  single_path (recv_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_path_def; auto; erule allE; erule impE)
  apply (drule topology_recv_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule topology_recv_sound; auto)
 apply (drule topology_recv_sound; auto)
done


theorem topology_one_shot_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    abstract_one_shot (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_one_shot_def, auto)
 apply (unfold one_shot_def, auto)
  apply (erule topology_single_path_send_sound; auto)
  apply (erule topology_single_path_recv_sound; auto)
sorry


theorem topology_single_proc_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    single_proc (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  single_proc (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_proc_def; auto; erule allE; erule impE)
  apply (drule isnt_send_path_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule isnt_send_path_sound; auto)
 apply (drule isnt_send_path_sound; auto)
done

theorem topology_single_proc_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    single_proc (abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c);
  
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  single_proc (recv_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (simp add: single_proc_def; auto; erule allE; erule impE)
  apply (drule topology_recv_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule topology_recv_sound; auto)
 apply (drule topology_recv_sound; auto)
done

theorem topology_one_to_one_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    abstract_one_to_one (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_one_to_one_def, auto)
 apply (unfold one_to_one_def, auto)
  apply (erule topology_single_proc_send_sound; auto)
  apply (erule topology_single_proc_recv_sound; auto)
done

theorem topology_fan_out_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    abstract_fan_out (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_fan_out_def)
 apply (unfold fan_out_def)
  apply (erule topology_single_proc_send_sound; auto)
done

theorem topology_fan_in_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    abstract_fan_in (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold abstract_fan_in_def)
 apply (unfold fan_in_def)
  apply (erule topology_single_proc_recv_sound; auto)
done

lemma one_shot_precise: "
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    one_shot \<E>' (Ch \<pi> x\<^sub>c) 
  \<rbrakk> \<Longrightarrow> 
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
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c);
    one_to_one \<E>' (Ch \<pi> x\<^sub>c) 
  \<rbrakk> \<Longrightarrow> 
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
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c);
    \<not> one_to_one \<E>' (Ch \<pi> x\<^sub>c);
    fan_out \<E>' (Ch \<pi> x\<^sub>c)
  \<rbrakk> \<Longrightarrow> 
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
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c);
    \<not> one_to_one \<E>' (Ch \<pi> x\<^sub>c); 
    fan_in \<E>' (Ch \<pi> x\<^sub>c) 
  \<rbrakk> \<Longrightarrow> 
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
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<not> one_shot \<E>' (Ch \<pi> x\<^sub>c);  \<not> one_to_one \<E>' (Ch \<pi> x\<^sub>c);
    \<not> fan_out \<E>' (Ch \<pi> x\<^sub>c); \<not> fan_in \<E>' (Ch \<pi> x\<^sub>c) 
  \<rbrakk> \<Longrightarrow> 
  ManyToMany \<preceq> t
"
 apply (erule topo_pair_accept.cases; auto)
     apply (drule topology_one_shot_sound; auto)
    apply (drule topology_one_to_one_sound; auto)
   apply (drule topology_fan_out_sound; auto; (simp add: one_to_one_def fan_in_def fan_out_def))
  apply (drule topology_fan_in_sound; auto; (simp add: one_to_one_def fan_in_def fan_out_def))
 apply (rule precision_order.Refl)
done

theorem is_abstract_topo_sound' : "
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'; \<pi>; x\<^sub>c\<rangle>\<rangle> \<preceq> t
"
 apply (unfold var_to_topo_def)
 apply (cases "one_shot \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp) 
  apply (rule one_shot_precise; auto?)
 apply (cases "one_to_one \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp) 
  apply (rule one_to_one_precise; auto)
 apply (cases "fan_out \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp) 
  apply (rule fan_out_precise; auto?)
 apply (cases "fan_in \<E>' (Ch \<pi> x\<^sub>c)")
  apply (simp) 
  apply (rule fan_in_precise; auto)
 apply (simp) 
 apply (rule many_to_many_precise; auto)    
done


theorem is_abstract_topo_sound: "
  \<lbrakk>
    \<A> \<bind> e;
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'; \<pi>\<rangle>\<rangle> \<sqsubseteq>\<^sub>t \<A>
"
 apply (unfold topo_accept_def)
 apply (unfold topo_env_precision_def)
 apply (intro allI, drule spec)
 apply (drule is_abstract_topo_sound', simp)
 apply (unfold state_pool_to_topo_env_def, auto)
done

end