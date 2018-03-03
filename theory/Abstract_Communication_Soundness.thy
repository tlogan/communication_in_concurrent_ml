theory Abstract_Communication_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Analysis Abstract_Communication_Analysis
begin

lemma abstract_send_chan_doesnt_exist_sound: "
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
    \<E>' (\<pi>\<^sub>y ;;`x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>)
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
    \<E>' (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>y; \<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>y\<rangle>)
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
  apply (drule abstract_send_chan_doesnt_exist_sound; assumption?; auto)
done

lemma isnt_send_path_sound': "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>;
    \<E>' (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>) 
  \<rbrakk> \<Longrightarrow> 
  \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y) \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c

"
 apply (rule conjI)
 apply (insert isnt_traceable_sound, blast)
 apply (rule conjI, (erule abstract_send_chan_doesnt_exist_sound; assumption))
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
 apply (unfold send_paths_def abstract_send_paths_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_send_path_sound'; assumption?; auto; blast)
  apply (frule isnt_send_path_sound'; assumption?; blast)
done


lemma send_path_preserved: "
  \<pi> \<in> send_paths \<E> c \<Longrightarrow> 
  \<E> \<rightarrow> \<E>' \<Longrightarrow> 
  \<pi> \<in> send_paths \<E>' c         
"
 apply (simp add: send_paths_def; auto)
 apply (erule concur_step.cases; clarsimp)
  apply (metis leaf_def option.simps(3) strict_prefixI')+
done

lemma send_paths_set_exclusive_preceded: "
  \<E> \<rightarrow> \<E>' \<Longrightarrow> set_exclusive (send_paths \<E>' c) \<Longrightarrow> set_exclusive (send_paths \<E> c)
"
 apply (simp add: set_exclusive_def; auto)
 apply (drule send_path_preserved; auto?)+
done

lemma send_paths_set_exclusive_preceded_star': "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow> set_exclusive (send_paths \<E>' c) \<longrightarrow> set_exclusive (send_paths \<E> c)
"
 apply (erule star.induct; auto)
 apply (simp add: send_paths_set_exclusive_preceded)
done

lemma send_paths_set_exclusive_preceded_star: "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow> set_exclusive (send_paths \<E>' c) \<Longrightarrow> set_exclusive (send_paths \<E> c)
"
 apply (simp add: send_paths_set_exclusive_preceded_star')
done

lemma send_path_preceded: "
  \<pi> \<in> (send_paths (\<E>(\<pi>\<^sub>p \<mapsto> \<sigma>)) c) \<Longrightarrow>
  \<E> \<rightarrow> \<E>(\<pi>\<^sub>p \<mapsto> \<sigma>) \<Longrightarrow>
  \<pi> \<noteq> \<pi>\<^sub>p \<Longrightarrow>
  \<pi> \<in> (send_paths \<E> c)
"
 apply (unfold send_paths_def; auto)
 apply (case_tac "\<pi>\<^sub>y = \<pi>\<^sub>p"; auto)
 apply (rule_tac x = x\<^sub>e in exI)
 apply (rule_tac x = e\<^sub>n in exI)
 apply (rule_tac x = \<kappa> in exI)
 apply (rule_tac x = \<rho> in exI)
 apply auto
 apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply (metis (mono_tags, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (metis (no_types, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (smt append1_eq_conv control_label.inject(1) fun_upd_other fun_upd_same fun_upd_twist leaf_elim option.distinct(1) strict_prefixI')
  apply (metis (mono_tags, lifting) leaf_def map_upd_Some_unfold option.distinct(1) prefixI prefix_snocD)
  apply (smt append1_eq_conv control_label.distinct(1) fun_upd_other fun_upd_same fun_upd_twist leaf_elim option.distinct(1) strict_prefixI')
done

lemma send_path_preceded_by_two: "
  \<pi> \<in> (send_paths (\<E>(\<pi>' \<mapsto> \<sigma>', \<pi>'' \<mapsto> \<sigma>'')) c) \<Longrightarrow>
  \<E> \<rightarrow> \<E>(\<pi>' \<mapsto> \<sigma>'', \<pi>'' \<mapsto> \<sigma>'') \<Longrightarrow>
  \<pi> \<noteq> \<pi>' \<Longrightarrow>  \<pi> \<noteq> \<pi>'' \<Longrightarrow>
  \<pi> \<in> (send_paths \<E> c)
"
sorry

lemma send_path_set_equal_preserved: "
  set_paths_equal (send_paths \<E> c) \<Longrightarrow> 
  \<E> \<rightarrow> \<E>' \<Longrightarrow>
  set_exclusive (send_paths \<E>' c) \<Longrightarrow>  
  set_paths_equal (send_paths \<E>' c)
"

 apply (simp add: set_paths_equal_def; auto)
 apply (rename_tac \<pi>\<^sub>1' \<pi>\<^sub>2')
 apply (simp add: set_exclusive_def; auto?)
 apply (rotate_tac 2, drule_tac x = \<pi>\<^sub>1' in spec; auto)
 apply (rotate_tac -1, drule_tac x = \<pi>\<^sub>2' in spec; auto)
 apply (subgoal_tac "\<E> \<rightarrow> \<E>'"; blast?)
 apply (erule concur_step.cases; clarify; (erule seq_step.cases; clarify)?, auto)
   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'"; simp?))
   apply ((unfold send_paths_def)[1]; blast)
   apply ((unfold send_paths_def)[1]; blast)
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>\<bar>x"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>\<bar>x"; simp?))
   apply ((unfold send_paths_def)[1]; blast)
   apply ((unfold send_paths_def)[1]; blast)
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>:x"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>:x"; simp?))
   apply ((unfold send_paths_def)[1]; blast)
   apply ((unfold send_paths_def)[1]; blast)
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>xa"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>xa"; simp?))
   apply ((unfold send_paths_def)[1]; blast)
   apply ((unfold send_paths_def)[1]; blast)
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; simp?))
   apply ((unfold send_paths_def)[1], (smt append_self_conv bind.distinct(5) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 state.inject))
   apply ((unfold send_paths_def)[1], (smt append_self_conv bind.distinct(5) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 state.inject))
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; simp?))
   apply ((unfold send_paths_def)[1], (smt append1_eq_conv control_label.inject(1) fun_upd_triv map_upd_eqD1 mem_Collect_eq state.inject val.distinct(5)))
   apply ((unfold send_paths_def)[1], (smt append1_eq_conv control_label.inject(1) fun_upd_triv map_upd_eqD1 mem_Collect_eq state.inject val.distinct(5)))
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; simp?))
   apply ((unfold send_paths_def)[1], (smt append_self_conv bind.distinct(43) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 option.inject state.inject))
   apply ((unfold send_paths_def)[1], (smt append_self_conv bind.distinct(43) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 option.inject state.inject))
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; simp?))
   apply ((unfold send_paths_def)[1], (smt append_self_conv bind.distinct(45) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 state.inject))
   apply ((unfold send_paths_def)[1], (smt append_self_conv bind.distinct(45) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 option.inject state.inject))
   apply (blast dest: send_path_preceded)

   apply (case_tac "\<pi>\<^sub>1' = \<pi>\<^sub>s ;; `x\<^sub>s"; simp?; 
     (case_tac "\<pi>\<^sub>1' = \<pi>\<^sub>r ;; `x\<^sub>r"; simp?); (case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>s ;; `x\<^sub>s"; simp?; (case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>r ;; `x\<^sub>r"; simp?))
   )
   apply ((unfold send_paths_def)[1]; clarify, fold send_paths_def)
   apply (smt bind.inject(2) exp.inject(1) leaf_def map_upd_Some_unfold option.inject prim.distinct(29) state.inject strict_prefixI' val.inject(2))

   apply (case_tac "c = ca"; simp?)

sorry



lemma send_paths_set_exclusive_implies_equal': "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow> 
  set_paths_equal (send_paths \<E> c) \<longrightarrow>
  set_exclusive (send_paths \<E>' c) \<longrightarrow> 
  set_paths_equal (send_paths \<E>' c)
"
 apply ((erule star.induct; auto), erule notE)
 apply (blast dest: send_path_set_equal_preserved send_paths_set_exclusive_preceded_star)
done

lemma empty_send_paths_set_equal: "
  set_paths_equal (send_paths [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] c)
"
 apply (unfold set_paths_equal_def send_paths_def; auto)
done

lemma send_paths_set_exclusive_implies_equal: "
  set_exclusive (send_paths \<E>' c) \<Longrightarrow> 
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  set_paths_equal (send_paths \<E>' c)
"
by (simp add: empty_send_paths_set_equal send_paths_set_exclusive_implies_equal')

theorem topology_set_exclusive_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    set_exclusive (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  set_paths_equal (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (rule send_paths_set_exclusive_implies_equal; auto?)
 apply (simp add: set_exclusive_def two_paths_ordered_def; auto; erule allE; erule impE)
  apply (drule isnt_send_path_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule isnt_send_path_sound; auto)
 apply (drule isnt_send_path_sound; auto)
done


lemma abstract_recv_chan_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>
  \<rbrakk> \<Longrightarrow> 
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c
"
 apply (frule lift_flow_exp_to_pool)
 apply (drule flow_preservation_star[of _ _ _ \<E>']; assumption?)
 apply (erule accept_state_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule accept_state.cases; auto)
 apply (erule accept_val_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace>"]; simp)
 apply (erule conjE)
 apply (erule accept_value.cases; auto)
 apply (erule accept_val_env.cases; auto)
 apply (drule spec[of _ x\<^sub>r\<^sub>c], drule spec[of _ "\<lbrace>Ch \<pi> x\<^sub>c\<rbrace>"]; simp)
done

lemma abstract_recv_evt_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace>
  \<rbrakk> \<Longrightarrow> 
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e 
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto)
done

lemma abstract_value_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' (\<pi>\<^sub>y ;; `x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<omega>);\<kappa>\<^sub>y\<rangle>)
  \<rbrakk> \<Longrightarrow> 
  { | \<omega> | } \<subseteq> \<V> x\<^sub>y
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto?)
done

lemma isnt_recv_path_sound': "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>); 
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>;
    \<E>' (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<omega>);\<kappa>\<^sub>y\<rangle>) 
  \<rbrakk> \<Longrightarrow>
  \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y) \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e \<and>
  {|\<omega>|} \<subseteq> \<V> x\<^sub>y
"
 apply (rule conjI, erule isnt_traceable_sound; assumption?)
 apply (rule conjI, (erule abstract_recv_chan_doesnt_exist_sound; assumption))
 apply (rule conjI, (erule abstract_recv_evt_doesnt_exist_sound; assumption))
 apply (drule abstract_value_doesnt_exist_sound; assumption)
done

lemma isnt_recv_path_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    \<pi>\<^sub>y \<in> recv_paths \<E>' (Ch \<pi> x\<^sub>c) 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>y \<in> abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c
"
 apply (unfold recv_paths_def abstract_recv_paths_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_recv_path_sound'; blast?; assumption?; blast)
  apply (frule isnt_recv_path_sound'; blast?; assumption?; blast)
done

lemma set_recv_paths_exclusive_implies_equal: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  set_exclusive (recv_paths \<E>' c) \<Longrightarrow> 
  set_paths_equal (recv_paths \<E>' c)
"
 apply (unfold set_exclusive_def recv_paths_def; auto)
sorry


theorem topology_set_exclusive_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    set_exclusive (abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  set_paths_equal (recv_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (rule set_recv_paths_exclusive_implies_equal; auto?)
 apply (simp add: set_exclusive_def two_paths_ordered_def; auto; erule allE; erule impE)
  apply (drule isnt_recv_path_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule isnt_recv_path_sound; auto)+
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
 apply (unfold one_shot_def; auto)
 apply (auto dest: topology_set_exclusive_send_sound)
 apply (auto dest: topology_set_exclusive_recv_sound)
done

lemma set_send_paths_noncompetitive_implies_ordered: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  set_noncompetitive (send_paths \<E>' c) \<Longrightarrow>
  set_ordered (send_paths \<E>' c)
"
sorry

theorem topology_set_noncompetitive_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    set_noncompetitive (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  set_ordered (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (rule set_send_paths_noncompetitive_implies_ordered; auto?)
 apply (simp add: set_noncompetitive_def; auto; erule allE; erule impE)
  apply (drule isnt_send_path_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule isnt_send_path_sound; auto)
 apply (drule isnt_send_path_sound; auto)
done

lemma set_recv_paths_noncompetitive_implies_ordered: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  set_noncompetitive (recv_paths \<E>' c) \<Longrightarrow>
  set_ordered (recv_paths \<E>' c)
"
sorry

theorem topology_set_noncompetitive_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    set_noncompetitive (abstract_recv_paths (\<V>, \<C>, e) x\<^sub>c);
  
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  set_ordered (recv_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (rule set_recv_paths_noncompetitive_implies_ordered; auto?)
 apply (simp add: set_noncompetitive_def; auto; erule allE; erule impE)
  apply (drule isnt_recv_path_sound; auto)
 apply (erule allE; frule impE; auto)
  apply (drule isnt_recv_path_sound; auto)
 apply (drule isnt_recv_path_sound; auto)
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
  apply (erule topology_set_noncompetitive_send_sound; auto)
  apply (erule topology_set_noncompetitive_recv_sound; auto)
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
  apply (erule topology_set_noncompetitive_send_sound; auto)
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
  apply (erule topology_set_noncompetitive_recv_sound; auto)
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