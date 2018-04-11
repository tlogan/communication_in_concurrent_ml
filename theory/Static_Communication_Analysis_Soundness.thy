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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>
  \<rbrakk> \<Longrightarrow> 
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c
"
 apply (frule accept_exp_to_pool)
 apply (drule accept_preserved_under_concur_step_star[of _ _ _ \<E>']; assumption?)
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> 
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto)
done

lemma static_message_isnt_sent_sound: "
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
  apply (frule accept_exp_to_pool)
  apply (drule accept_preserved_under_concur_step_star [of _ _ _ \<E>']; assumption?)
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>;
    \<E>' (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e\<^sub>y;\<rho>\<^sub>y(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>y\<rangle>) 
  \<rbrakk> \<Longrightarrow> 
  \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e

"
 apply (rule conjI)
 apply (insert isnt_traceable_sound, blast)
 apply (rule conjI, (erule static_send_chan_doesnt_exist_sound; assumption))
 apply (erule static_send_evt_doesnt_exist_sound; assumption)
done


lemma inclusive_preserved: "
  \<E> \<rightarrow> \<E>' \<Longrightarrow>
  \<forall>\<pi>\<^sub>1. (\<exists>\<sigma>\<^sub>1. \<E> \<pi>\<^sub>1 = Some \<sigma>\<^sub>1) \<longrightarrow> (\<forall>\<pi>\<^sub>2. (\<exists>\<sigma>\<^sub>2. \<E> \<pi>\<^sub>2 = Some \<sigma>\<^sub>2) \<longrightarrow> \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow>
  \<E>' \<pi>\<^sub>1 = Some \<sigma>\<^sub>1 \<Longrightarrow> \<E>' \<pi>\<^sub>2 = Some \<sigma>\<^sub>2 \<Longrightarrow> 
  \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
"
 apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; `xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; `xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; `xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; `xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; \<upharpoonleft>xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; \<upharpoonleft>xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; \<upharpoonleft>xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; \<upharpoonleft>xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)
   
   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; \<upharpoonleft>xa"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; \<upharpoonleft>xa"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `x"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; `x"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; .x"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; .x"; auto))
   apply (simp add: Ordered)
   apply (case_tac "\<pi>\<^sub>2 = \<pi> ;; `x"; auto)
  apply (simp add: Spawn_Left)
  apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
  apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `x"; auto)
  apply (simp add: Spawn_Right)
  apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict) 
   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; `x"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; `x"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>\<^sub>1 = \<pi>\<^sub>r ;; `x\<^sub>r"; auto)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; `x\<^sub>r"; auto)
   apply (simp add: Ordered)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; `x\<^sub>s"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf_def prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>\<^sub>1 = \<pi>\<^sub>s ;; `x\<^sub>s"; auto)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; `x\<^sub>r"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf_def prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; `x\<^sub>s"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; `x\<^sub>r"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; `x\<^sub>s"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; `x\<^sub>r"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; `x\<^sub>s"; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
 
done

lemma runtime_paths_are_inclusive': "
  \<E>\<^sub>0 \<rightarrow>* \<E> \<Longrightarrow>
  (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 \<sigma>\<^sub>1 \<sigma>\<^sub>2.
    \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E> \<pi>\<^sub>1 = Some \<sigma>\<^sub>1 \<longrightarrow>
    \<E> \<pi>\<^sub>2 = Some \<sigma>\<^sub>2 \<longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  )
"
 apply (drule star_implies_star_left)
 apply (erule star_left.induct; auto)
  apply (simp add: Ordered)
 apply (rename_tac \<E> \<E>' \<pi>\<^sub>1 \<sigma>\<^sub>1 \<pi>\<^sub>2 \<sigma>\<^sub>2)
 apply (blast dest: inclusive_preserved)
done

lemma runtime_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>1' = Some \<sigma>\<^sub>1';
    \<E>' \<pi>\<^sub>2' = Some \<sigma>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' \<asymp> \<pi>\<^sub>2'
"
by (blast dest: runtime_paths_are_inclusive')


lemma isnt_send_path_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>y
  \<rbrakk> \<Longrightarrow> 
  is_static_send_path (\<V>, \<C>, e) x\<^sub>c \<pi>\<^sub>y
"
 apply (unfold is_send_path_def is_static_send_path_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_send_path_sound'; assumption?; auto; blast)
  apply (frule isnt_send_path_sound'; assumption?; blast)
done


lemma runtime_send_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' c \<pi>\<^sub>1';
    is_send_path \<E>' c \<pi>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' \<asymp> \<pi>\<^sub>2'
"
apply (unfold is_send_path_def; auto)
using runtime_paths_are_inclusive by blast

theorem topology_all_singular_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    all (is_static_send_path (\<V>, \<C>, e) x\<^sub>c) singular
  \<rbrakk> \<Longrightarrow>
  all (is_send_path \<E>' (Ch \<pi> x\<^sub>c)) op=
"
 apply (simp add: all_def singular_def; auto)
using isnt_send_path_sound runtime_send_paths_are_inclusive by blast


lemma static_recv_chan_doesnt_exist_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace>;
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace>
  \<rbrakk> \<Longrightarrow> 
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c
"
 apply (frule accept_exp_to_pool)
 apply (drule accept_preserved_under_concur_step_star[of _ _ _ \<E>']; assumption?)
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>y x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace>
  \<rbrakk> \<Longrightarrow> 
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e 
"
  apply (drule isnt_abstract_value_sound_coro; assumption?; auto)
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
  \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e
"
 apply (rule conjI, erule isnt_traceable_sound; assumption?)
 apply (rule conjI, (erule static_recv_chan_doesnt_exist_sound; assumption))
 apply (erule static_recv_evt_doesnt_exist_sound; assumption)
done


lemma isnt_recv_path_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    is_recv_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>y
  \<rbrakk> \<Longrightarrow> 
  is_static_recv_path (\<V>, \<C>, e) x\<^sub>c \<pi>\<^sub>y
"
 apply (unfold is_recv_path_def is_static_recv_path_def; auto)
  apply (rule exI, rule conjI)
   apply (frule isnt_recv_path_sound'; blast?; assumption?; blast)
  apply (frule isnt_recv_path_sound'; blast?; assumption?; blast)
done

lemma runtime_recv_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_recv_path \<E>' c \<pi>\<^sub>1';
    is_recv_path \<E>' c \<pi>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' \<asymp> \<pi>\<^sub>2'
"
apply (unfold is_recv_path_def; auto)
using runtime_paths_are_inclusive by auto

lemma topology_trim_equal_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e;
    \<V> (trim \<L>n e) \<tturnstile> \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2;

    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>1;
    is_send_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>2
  \<rbrakk> \<Longrightarrow>
  \<pi>\<^sub>1 = \<pi>\<^sub>2
"
sorry

theorem topology_one_shot_strong_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e;

    static_one_shot_strong (\<V>, \<C>, e) (trim \<L>n e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c)
"

 apply (unfold static_one_shot_strong_def)
 apply (unfold one_shot_def, auto)
 apply (unfold all_def; auto)
 apply (unfold singular_strong_def)
by (metis isnt_send_path_sound runtime_send_paths_are_inclusive topology_trim_equal_sound)


theorem topology_one_shot_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    static_one_shot (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold static_one_shot_def)
 apply (unfold one_shot_def)
 apply (auto dest: topology_all_singular_send_sound)
done



theorem topology_all_noncompetitive_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    all (is_static_send_path (\<V>, \<C>, e) x\<^sub>c) noncompetitive
  \<rbrakk> \<Longrightarrow>
  all (is_send_path \<E>' (Ch \<pi> x\<^sub>c)) ordered
"
apply (simp add: all_def noncompetitive_def; auto)
using isnt_send_path_sound runtime_send_paths_are_inclusive by blast




theorem topology_all_noncompetitive_recv_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    all (is_static_recv_path (\<V>, \<C>, e) x\<^sub>c) noncompetitive;
  
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  all (is_recv_path \<E>' (Ch \<pi> x\<^sub>c)) ordered
"
apply (simp add: all_def noncompetitive_def; auto)
using isnt_recv_path_sound runtime_recv_paths_are_inclusive by blast


theorem topology_one_to_one_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    static_fan_in (\<V>, \<C>, e) x\<^sub>c
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (unfold static_fan_in_def)
 apply (unfold fan_in_def)
  apply (erule topology_all_noncompetitive_recv_sound; auto)
done

end