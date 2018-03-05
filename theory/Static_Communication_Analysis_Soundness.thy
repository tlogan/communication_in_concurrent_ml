theory Static_Communication_Analysis_Soundness
  imports 
    Main
    Syntax 
    Runtime_Semantics Runtime_Semantics Static_Semantics Static_Semantics_Soundness
    Runtime_Communication_Analysis Static_Communication_Analysis
begin

lemma static_send_chan_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
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

lemma static_send_evt_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> 
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto)
done

lemma static_unit_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' (\<pi>\<^sub>y ;;`x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>)
  \<rbrakk> \<Longrightarrow> 
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y
"
 apply (drule isnt_abstract_value_sound_coro; assumption?; auto; simp)
done

lemma static_message_isnt_sent_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
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
  apply (frule static_send_evt_doesnt_exist_sound; assumption?)
  apply (erule impE; simp)
  apply (drule spec[of _ x\<^sub>c])
  apply (drule static_send_chan_doesnt_exist_sound; assumption?; auto)
done

lemma isnt_send_path_sound': "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
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
 apply (rule conjI, (erule static_send_chan_doesnt_exist_sound; assumption))
 apply (rule conjI, (erule static_send_evt_doesnt_exist_sound; assumption))
 apply (rule conjI, (erule static_unit_doesnt_exist_sound; assumption))
 apply (drule static_message_isnt_sent_sound; assumption)
done

lemma isnt_send_path_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>y
  \<rbrakk> \<Longrightarrow> 
  is_static_send_path (\<V>, \<C>, e) x\<^sub>c \<pi>\<^sub>y
"
 apply (unfold is_send_path_def is_static_send_path_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_send_path_sound'; assumption?; auto; blast)
  apply (frule isnt_send_path_sound'; assumption?; blast)
done

method solve_case_of_paths_ordered_or_nonexclusive_preserved = (
  (metis (mono_tags, hide_lams) 
    leaf_def option.distinct(1)
    prefix_order.dual_order.order_iff_strict 
    two_paths_exclusive.Refl
    two_paths_exclusive_commut
    two_paths_exclusive_and_ordered_implies_equal 
    two_paths_exclusive_and_unordered_implies_exclusive_or_prefix_under_backtrack 
    prefix_order.dual_order.order_iff_strict prefix_snoc 
    two_paths_exclusive.simps 
  )
)



lemma paths_ordered_or_nonexclusive_preserved: "
  \<lbrakk>
    \<E> \<rightarrow> \<E>';
    \<forall>\<pi>\<^sub>1'. (\<exists>\<sigma>\<^sub>1'. \<E> \<pi>\<^sub>1' = Some \<sigma>\<^sub>1') \<longrightarrow> (\<forall>\<pi>\<^sub>2'. (\<exists>\<sigma>\<^sub>2'. \<E> \<pi>\<^sub>2' = Some \<sigma>\<^sub>2') \<longrightarrow> two_paths_ordered \<pi>\<^sub>1' \<pi>\<^sub>2' \<or> \<not> two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2');
    \<E>' \<pi>\<^sub>1' = Some \<sigma>\<^sub>1'; 
    \<E>' \<pi>\<^sub>2' = Some \<sigma>\<^sub>2'; 
    \<not> two_paths_ordered \<pi>\<^sub>1' \<pi>\<^sub>2';  
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  False
"

 apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?; (simp add: two_paths_ordered_def))
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>\<bar>x"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>\<bar>x"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>:x"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>:x"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi>\<^sub>r ;; `x\<^sub>r"; auto))
  apply ((case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>r ;; `x\<^sub>r"; auto))
  apply ((case_tac "\<pi>\<^sub>1' \<noteq> \<pi>\<^sub>s ;; `x\<^sub>s"; auto))
  apply ((case_tac "\<pi>\<^sub>2' \<noteq> \<pi>\<^sub>s ;; `x\<^sub>s"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply (drule_tac x = \<pi>\<^sub>s in spec, erule impE, rule exI, assumption)
  apply (drule_tac x = \<pi>\<^sub>r in spec, erule impE, rule exI, assumption; auto)
  apply (metis exp.inject(1) leaf_def option.inject prefix_order.le_less state.inject)
  apply (metis exp.inject(1) leaf_def option.inject prefix_order.le_less state.inject)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)



  apply ((case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>s ;; `x\<^sub>s"; auto))
  apply (drule_tac x = \<pi>\<^sub>s in spec, erule impE, rule exI, assumption)
  apply (drule_tac x = \<pi>\<^sub>r in spec, erule impE, rule exI, assumption; auto)
  apply (metis exp.inject(1) leaf_def option.inject prefix_order.le_less state.inject)
  apply (metis exp.inject(1) leaf_def option.inject prefix_order.le_less state.inject)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)


  apply ((case_tac "\<pi>\<^sub>1' = \<pi>\<^sub>s ;; `x\<^sub>s"; auto))
  apply ((case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>r ;; `x\<^sub>r"; auto), (solve_case_of_paths_ordered_or_nonexclusive_preserved))
  apply (drule_tac x = \<pi>\<^sub>2' in spec, erule impE, rule exI, assumption)
  apply (drule_tac x = \<pi>\<^sub>s in spec, erule impE, rule exI, assumption; auto)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>r ;; `x\<^sub>r"; auto))
  apply (drule_tac x = \<pi>\<^sub>s in spec, erule impE, rule exI, assumption)
  apply (drule_tac x = \<pi>\<^sub>r in spec, erule impE, rule exI, assumption; auto)
  apply (metis exp.inject(1) leaf_def option.inject prefix_order.le_less state.inject)
  apply (metis exp.inject(1) leaf_def option.inject prefix_order.le_less state.inject)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>r ;; `x\<^sub>r"; auto))
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)

  apply ((case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>s ;; `x\<^sub>s "; auto))
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)

  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; `x"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `x"; auto), solve_case_of_paths_ordered_or_nonexclusive_preserved)

  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; .x"; auto))
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `x"; auto))
  apply (simp add: not_exclusive_with_process_split)
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>1' = \<pi> ;; `x"; auto))
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; .x"; auto)) 
  using not_exclusive_with_process_split two_paths_exclusive_commut apply blast
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; .x"; auto)) 
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
  apply ((case_tac "\<pi>\<^sub>2' = \<pi> ;; `x"; auto)) 
  apply (solve_case_of_paths_ordered_or_nonexclusive_preserved)
done


lemma paths_ordered_or_nonexclusive_preserved_star': "
  \<lbrakk>
    \<E>\<^sub>0 \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow> 
  \<E>\<^sub>0 = [[.x\<^sub>0] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
  (\<forall> \<pi>\<^sub>1' \<pi>\<^sub>2' \<sigma>\<^sub>1' \<sigma>\<^sub>2'.
    \<E>' \<pi>\<^sub>1' = Some \<sigma>\<^sub>1' \<longrightarrow>
    \<E>' \<pi>\<^sub>2' = Some \<sigma>\<^sub>2' \<longrightarrow>
    two_paths_ordered \<pi>\<^sub>1' \<pi>\<^sub>2' \<or> \<not>(two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2')
  )
"
 apply (drule star_implies_star_left)
 apply (erule star_left.induct; auto)
 using two_paths_ordered_def apply blast
 apply (rename_tac \<E> \<E>' \<pi>\<^sub>1' \<sigma>\<^sub>1' \<pi>\<^sub>2' \<sigma>\<^sub>2')
 using paths_ordered_or_nonexclusive_preserved apply blast
done

lemma paths_ordered_or_nonexclusive_preserved_star: "
  \<lbrakk>
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>1' = Some \<sigma>\<^sub>1';
    \<E>' \<pi>\<^sub>2' = Some \<sigma>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  two_paths_ordered \<pi>\<^sub>1' \<pi>\<^sub>2' \<or> \<not>(two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2')
"
by (simp add: paths_ordered_or_nonexclusive_preserved_star')

lemma paths_exclusive_implies_equal: "
  \<lbrakk>
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>1' = Some \<sigma>\<^sub>1'; 
    \<E>' \<pi>\<^sub>2' = Some \<sigma>\<^sub>2'; 
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' = \<pi>\<^sub>2'
"
using paths_ordered_or_nonexclusive_preserved_star two_paths_exclusive_and_ordered_implies_equal' by blast


lemma send_paths_exclusive_implies_equal: "
  \<lbrakk>
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' c \<pi>\<^sub>1'; 
    is_send_path \<E>' c \<pi>\<^sub>2'; 
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' = \<pi>\<^sub>2'
"
 apply (unfold is_send_path_def)[1]
 apply (blast dest: paths_exclusive_implies_equal)
done


theorem topology_all_exclusive_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    all_exclusive (is_static_send_path (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  all_paths_equal (is_send_path \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (unfold all_paths_equal_def; auto)
 apply (unfold all_exclusive_def; auto)
 apply (drule_tac x = \<pi>\<^sub>1 in spec; auto; (drule_tac x = \<pi>\<^sub>2 in spec; auto)?)
 apply (blast dest: isnt_send_path_sound)
 apply (blast dest: isnt_send_path_sound)
 apply (simp add: send_paths_exclusive_implies_equal)
done


lemma static_recv_chan_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
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

lemma static_recv_evt_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
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
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' (\<pi>\<^sub>y ;; `x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<omega>);\<kappa>\<^sub>y\<rangle>)
  \<rbrakk> \<Longrightarrow> 
  { | \<omega> | } \<subseteq> \<V> x\<^sub>y
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto?)
done

lemma isnt_recv_path_sound': "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

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
 apply (rule conjI, (erule static_recv_chan_doesnt_exist_sound; assumption))
 apply (rule conjI, (erule static_recv_evt_doesnt_exist_sound; assumption))
 apply (drule abstract_value_doesnt_exist_sound; assumption)
done

lemma isnt_recv_path_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    is_recv_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>y
  \<rbrakk> \<Longrightarrow> 
  is_static_recv_path (\<V>, \<C>, e) x\<^sub>c \<pi>\<^sub>y
"
 apply (unfold is_recv_path_def is_static_recv_path_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_recv_path_sound'; blast?; assumption?; blast)
  apply (frule isnt_recv_path_sound'; blast?; assumption?; blast)
done


lemma recv_paths_exclusive_implies_equal: "
  \<lbrakk>
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_recv_path \<E>' c \<pi>\<^sub>1'; 
    is_recv_path \<E>' c \<pi>\<^sub>2'; 
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' = \<pi>\<^sub>2'
"
 apply (unfold is_recv_path_def)[1]
 apply (blast dest: paths_exclusive_implies_equal)
done


theorem topology_all_exclusive_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

    all_exclusive (is_static_recv_path (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  all_paths_equal (is_recv_path \<E>' (Ch \<pi> x\<^sub>c))
"
by (simp add: isnt_recv_path_sound recv_paths_exclusive_implies_equal all_exclusive_def all_paths_equal_def)


theorem topology_one_shot_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    static_one_shot (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold static_one_shot_def, auto)
 apply (unfold one_shot_def; auto)
 apply (auto dest: topology_all_exclusive_send_sound)
 apply (auto dest: topology_all_exclusive_recv_sound)
done

lemma send_paths_noncompetitive_implies_ordered: "
  \<lbrakk>
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' c \<pi>\<^sub>1'; 
    is_send_path \<E>' c \<pi>\<^sub>2'; 
    two_paths_noncompetitive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  two_paths_ordered \<pi>\<^sub>1' \<pi>\<^sub>2'
"
 apply (unfold is_send_path_def)[1]
 using paths_ordered_or_nonexclusive_preserved_star' two_paths_noncompetitive_def apply fastforce
done


theorem topology_all_noncompetitive_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    all_noncompetitive (is_static_send_path (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  all_ordered (is_send_path \<E>' (Ch \<pi> x\<^sub>c))
"
by (simp add: isnt_send_path_sound send_paths_noncompetitive_implies_ordered all_noncompetitive_def all_ordered_def)



lemma recv_paths_noncompetitive_implies_ordered: "
  \<lbrakk>
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_recv_path \<E>' c \<pi>\<^sub>1'; 
    is_recv_path \<E>' c \<pi>\<^sub>2'; 
    two_paths_noncompetitive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  two_paths_ordered \<pi>\<^sub>1' \<pi>\<^sub>2'
"
 apply (unfold is_recv_path_def)[1]
 using paths_ordered_or_nonexclusive_preserved_star' two_paths_noncompetitive_def apply fastforce
done


theorem topology_all_noncompetitive_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    all_noncompetitive (is_static_recv_path (\<V>, \<C>, e) x\<^sub>c);
  
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  all_ordered (is_recv_path \<E>' (Ch \<pi> x\<^sub>c))
"
by (simp add: isnt_recv_path_sound recv_paths_noncompetitive_implies_ordered all_noncompetitive_def all_ordered_def)


theorem topology_one_to_one_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    static_one_to_one (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold static_one_to_one_def, auto)
 apply (unfold one_to_one_def, auto)
  apply (erule topology_all_noncompetitive_send_sound; auto)
  apply (erule topology_all_noncompetitive_recv_sound; auto)
done

theorem topology_fan_out_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    static_fan_out (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold static_fan_out_def)
 apply (unfold fan_out_def)
  apply (erule topology_all_noncompetitive_send_sound; auto)
done

theorem topology_fan_in_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    static_fan_in (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold static_fan_in_def)
 apply (unfold fan_in_def)
  apply (erule topology_all_noncompetitive_recv_sound; auto)
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
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
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
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

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
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';

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
    [[.x\<^sub>0] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
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

theorem is_static_topo_sound' : "
  \<lbrakk>
    (x\<^sub>c, t) \<TTurnstile> e;
    [[.x\<^sub>0] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
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


theorem is_static_topo_sound: "
  \<lbrakk>
    \<A> \<bind> e;
    [[.x\<^sub>0] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'; \<pi>\<rangle>\<rangle> \<sqsubseteq>\<^sub>t \<A> 
"
 apply (unfold topo_accept_def)
 apply (unfold topo_env_precision_def)
 apply (intro allI, drule spec)
 apply (drule is_static_topo_sound', simp)
 apply (unfold state_pool_to_topo_env_def, auto)
done

end