theory Communication_Topology_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Topology_Analysis
begin

theorem topology_pair_pool_sound : "
  \<lbrakk>
    (x, t) \<TTurnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>' ; x\<rangle>\<rangle> \<preceq> t
"
sorry


lemma "
  (\<V>, \<C>) \<Turnstile> e \<Longrightarrow> one_max (abstract_send_paths \<V> x e) \<Longrightarrow> t = OneShot \<Longrightarrow> (x, OneShot) \<TTurnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]
"
 apply (rule topo_pair_accept.OneShot[of \<V> \<C>], simp)
  apply (rule accept_state_pool.Any, auto)
  apply (rule accept_state.Any)
   apply (unfold flow_accept_exp_def, auto)
   apply (rule accept_value_accept_val_env.Any, auto)
   apply (rule accept_stack.Empty)
 apply (simp add: abstract_send_paths_def control_paths_def one_max_def)
sorry

theorem topo_pair_exp_to_pool: "
  (x, t) \<TTurnstile>\<^sub>e e \<Longrightarrow> (x, t) \<TTurnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]
"
 apply (erule topo_pair_accept.cases, auto)
     apply (rule topo_pair_accept.OneShot; auto?)
     apply (simp add: abstract_send_paths_def control_paths_def)
sorry


theorem topology_pair_sound : "
  \<lbrakk>
    (x, t) \<TTurnstile>\<^sub>e e; 
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>' ; x\<rangle>\<rangle> \<preceq> t
"
 apply (drule topo_pair_exp_to_pool)
 apply (erule topology_pair_pool_sound, auto)
done

lemma topology_sound': "
  (x, \<A> x) \<TTurnstile>\<^sub>e e \<Longrightarrow> [[] \<mapsto> \<langle>e; Map.empty; []\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> (\<langle>\<langle>\<E>'\<rangle>\<rangle>) x \<preceq> \<A> x
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