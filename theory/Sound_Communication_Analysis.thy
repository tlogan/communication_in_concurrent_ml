theory Sound_Communication_Analysis
  imports 
    Main
    Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Dynamic_Communication_Analysis Static_Communication_Analysis
begin

(*
lemma static_send_chan_doesnt_exist_sound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi> x\<^sub>c));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c
"
 apply (frule static_eval_to_pool)
 apply (drule static_eval_preserved_under_concur_step_star[of _ _ _ \<E>']; assumption?)
 apply (erule static_eval_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule static_eval_state.cases; auto)
 apply (erule static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule static_eval_value.cases; auto)
 apply (erule static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ "(VChan (Ch \<pi> x\<^sub>c))"]; simp)
done

lemma static_send_evt_doesnt_exist_sound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
"
  apply (drule values_not_bound_sound; assumption?; auto)
done


lemma isnt_send_path_sound': "
  \<lbrakk>
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi> x\<^sub>c));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e

"
 apply (rule conjI)
 apply (insert isnt_static_traceable_sound, blast)
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

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LReturn x\<^sub>\<kappa>')"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LReturn x\<^sub>\<kappa>')"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)
   
   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext x)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext x)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LSpawn x)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LSpawn x)"; auto))
   apply (simp add: Ordered)
   apply (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext x)"; auto)
  apply (simp add: Spawn_Left)
  apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
  apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext x)"; auto)
  apply (simp add: Spawn_Right)
  apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict) 
   apply (case_tac "\<pi>\<^sub>1 = \<pi> ;; (LNext x)"; auto; (case_tac "\<pi>\<^sub>2 = \<pi> ;; (LNext x)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>\<^sub>1 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (simp add: Ordered)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf_def prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>\<^sub>1 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf_def prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf_def option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf_def option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>\<^sub>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
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
    is_send_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>y;
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow> 
  is_static_path LF (NLet xC) (is_static_send_node_label V e xC) \<pi>\<^sub>y
"
 apply (unfold is_send_path_def is_static_send_path_def; auto)
   apply (frule isnt_send_path_sound'; assumption?; auto; blast)
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




lemma static_recv_chan_doesnt_exist_sound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi> x\<^sub>c));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c
"
 apply (frule static_eval_to_pool)
 apply (drule static_eval_preserved_under_concur_step_star[of _ _ _ \<E>']; assumption?)
 apply (erule static_eval_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule static_eval_state.cases; auto)
 apply (erule static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule static_eval_value.cases; auto)
 apply (erule static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>r\<^sub>c], drule spec[of _ "(VChan (Ch \<pi> x\<^sub>c))"]; simp)
done

lemma static_recv_evt_doesnt_exist_sound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e 
"
  apply (drule values_not_bound_sound; assumption?; auto)
done

lemma isnt_recv_path_sound': "
  \<lbrakk>
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>); 
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi> x\<^sub>c));
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y \<and>
  ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
  {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e
"
 apply (rule conjI, erule isnt_static_traceable_sound; assumption?)
 apply (rule conjI, (erule static_recv_chan_doesnt_exist_sound; assumption))
 apply (erule static_recv_evt_doesnt_exist_sound; assumption)
done

lemma isnt_recv_path_sound: "
  \<lbrakk>
    is_recv_path \<E>' (Ch \<pi> x\<^sub>c) \<pi>\<^sub>y;
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow> 
  is_static_path LF (NLet xC) (is_static_recv_node_label V e xC) \<pi>\<^sub>y
"
 apply (unfold is_recv_path_def is_static_recv_path_def; auto)
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


*)


theorem singular_send_to_equal_send: "

  every_two_static_paths (is_static_path LF (NLet x\<^sub>c) (is_static_send_node_label \<V> e x\<^sub>c)) singular \<Longrightarrow>
  static_live_flow_set Ln Lx F LF \<Longrightarrow> 
  static_chan_liveness \<V> Ln Lx x\<^sub>c e \<Longrightarrow> 
  static_flow_set \<V> F e \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  all (is_send_path \<E>' (Ch \<pi> x\<^sub>c)) op =
"
sorry
(*
 apply (simp add: all_def singular_def; auto)
using isnt_send_path_sound runtime_send_paths_are_inclusive by blast
*)



theorem one_shot_sound: "
  \<lbrakk>
    static_one_shot \<V> e x\<^sub>c;
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (erule static_one_shot.cases; auto)
 apply (unfold one_shot_def)
 apply (metis singular_send_to_equal_send)
done


theorem noncompetitive_send_to_ordered_send: "
   every_two_static_paths (is_static_path LF (NLet x\<^sub>c) (is_static_send_node_label \<V> e x\<^sub>c)) noncompetitive \<Longrightarrow>
   static_live_flow_set Ln Lx F LF \<Longrightarrow> 
   static_chan_liveness \<V> Ln Lx x\<^sub>c e \<Longrightarrow> 
   static_flow_set \<V> F e \<Longrightarrow>
   (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
   [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
   all (is_send_path \<E>' (Ch \<pi> x\<^sub>c)) ordered
"
sorry
(*
apply (simp add: all_def noncompetitive_def; auto)
using isnt_send_path_sound runtime_send_paths_are_inclusive by blast
*)

theorem fan_out_sound: "
  \<lbrakk>
    static_fan_out \<V> e x\<^sub>c;
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (erule static_fan_out.cases; auto)
 apply (unfold fan_out_def)
 apply (metis noncompetitive_send_to_ordered_send)
done

lemma noncompetitive_recv_to_ordered_recv: "
   every_two_static_paths (is_static_path LF (NLet x\<^sub>c) (is_static_recv_node_label \<V> e x\<^sub>c)) noncompetitive \<Longrightarrow>
   static_live_flow_set Ln Lx F LF \<Longrightarrow> 
   static_chan_liveness \<V> Ln Lx x\<^sub>c e \<Longrightarrow> 
   static_flow_set \<V> F e \<Longrightarrow>
   (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
   [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
   all (is_recv_path \<E>' (Ch \<pi> x\<^sub>c)) ordered
"
sorry


theorem fan_in_sound: "
  \<lbrakk>
    static_fan_in \<V> e x\<^sub>c;
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (erule static_fan_in.cases; auto)
 apply (unfold fan_in_def)
 apply (metis noncompetitive_recv_to_ordered_recv)
done


theorem one_to_one_sound: "
  \<lbrakk>
    static_one_to_one \<V> e x\<^sub>c;
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> x\<^sub>c)
"
 apply (erule static_one_to_one.cases; auto)
 apply (unfold one_to_one_def)
 apply (simp add: noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send)
done


end