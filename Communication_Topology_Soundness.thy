theory Communication_Topology_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Topology_Analysis
begin

theorem topology_pair_sound : "
  \<lbrakk>
    (x, t) \<Turnstile>\<^sub>t e; 
    [[] \<mapsto> <<e, empty, []>>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>' ; x\<rangle>\<rangle> \<preceq> t
"
sorry

lemma topology_sound': "
  (x, \<A> x) \<Turnstile>\<^sub>t e \<Longrightarrow> [[] \<mapsto> <<e,Map.empty,[]>>] \<rightarrow>* \<E>' \<Longrightarrow> (\<langle>\<langle>\<E>'\<rangle>\<rangle>) x \<preceq> \<A> x
"
 apply (drule topology_pair_sound, simp)
 apply (unfold state_pool_to_topo_env_def, auto)
done

theorem topology_sound : "
  \<lbrakk>
    \<A> \<bind> e; 
    [[] \<mapsto> <<e, empty, []>>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'\<rangle>\<rangle> \<sqsubseteq>\<^sub>t \<A>
"
 apply (unfold topo_accept_def)
 apply (unfold topo_env_precision_def)
 apply (intro allI, drule spec)
 apply (erule topology_sound', auto)
done

end