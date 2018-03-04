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

(*
lemma "
\<pi> \<in> send_paths (\<E>(\<pi>';;l \<mapsto> \<sigma>'')) c \<Longrightarrow>
\<E> \<pi>' = Some \<sigma>' \<Longrightarrow>
\<pi> \<noteq> \<pi>';;l \<Longrightarrow>
\<pi> \<in> send_paths \<E> c
"
apply (unfold send_paths_def; auto)
apply (case_tac "\<pi>\<^sub>y = \<pi>' ;; l"; meson?)
apply clarsimp
apply (drule_tac x =

*)

lemma two_paths_exclusive_commut: "
  two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>two_paths_exclusive \<pi>\<^sub>2 \<pi>\<^sub>1  
"
 apply (erule two_paths_exclusive.induct; auto?)
  apply (simp add: Base two_paths_ordered_def)
  apply (simp add: Induc)
done


lemma paths_exclusive_implies_equal_in_sync_case: "
  \<lbrakk>
    \<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2);
    \<pi>\<^sub>s ;; `x\<^sub>s \<in> send_paths (\<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) c;
    \<pi>\<^sub>2' \<in> send_paths (\<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) c;
    two_paths_exclusive (\<pi>\<^sub>s ;; `x\<^sub>s) \<pi>\<^sub>2';
    \<E>' = \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>);
    leaf \<E> \<pi>\<^sub>s;
    \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>);
    \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>;
    \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>;
    \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m;
    leaf \<E> \<pi>\<^sub>r;
    \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>);
    \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>;
    \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>; x\<^sub>s \<noteq> x\<^sub>r; \<pi>\<^sub>2' \<noteq> \<pi>\<^sub>r ;; `x\<^sub>r;
    \<pi>\<^sub>1' = \<pi>\<^sub>s ;; `x\<^sub>s; \<pi>\<^sub>2' \<noteq> \<pi>\<^sub>s ;; `x\<^sub>s; ca = c 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>s ;; `x\<^sub>s = \<pi>\<^sub>2'
"
sorry

lemma paths_exclusive_implies_equal: "
  \<lbrakk>
    \<E> \<rightarrow> \<E>';
    \<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2);
    \<pi>\<^sub>1' \<in> send_paths \<E>' c; 
    \<pi>\<^sub>2' \<in> send_paths \<E>' c; 
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2'
  \<rbrakk> \<Longrightarrow>
  \<pi>\<^sub>1' = \<pi>\<^sub>2'
"
 apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'", simp, (unfold send_paths_def)[1], blast)
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>'", simp, (unfold send_paths_def)[1], blast)
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>\<bar>x", simp, (unfold send_paths_def)[1], blast)
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>\<bar>x", simp, (unfold send_paths_def)[1], blast)
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>:x", simp, (unfold send_paths_def)[1], blast)
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>:x", simp, (unfold send_paths_def)[1], blast)
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; \<upharpoonleft>xa", simp, (unfold send_paths_def)[1], blast)
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; \<upharpoonleft>xa", simp, (unfold send_paths_def)[1], blast)
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa", simp, (unfold send_paths_def)[1])
  apply (smt append_self_conv bind.distinct(5) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 state.inject)
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa", simp, (unfold send_paths_def)[1])
  apply (smt append_self_conv bind.distinct(5) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 option.inject state.inject)
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )

  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa", simp, (unfold send_paths_def)[1])
  apply (smt append1_eq_conv control_label.inject(1) fun_upd_triv map_upd_eqD1 mem_Collect_eq state.inject val.distinct(5))
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa", simp, (unfold send_paths_def)[1])
  apply (smt append1_eq_conv control_label.inject(1) fun_upd_triv map_upd_eqD1 mem_Collect_eq state.inject val.distinct(5))
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )

  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa", simp, (unfold send_paths_def)[1])
  apply (smt append_self_conv bind.distinct(43) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 option.inject state.inject)
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa", simp, (unfold send_paths_def)[1])
  apply (smt append_self_conv bind.distinct(43) butlast_snoc exp.inject(1) map_upd_Some_unfold mem_Collect_eq not_Cons_self2 option.inject state.inject)
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )

  apply (case_tac "\<pi>\<^sub>1' = \<pi> ;; `xa", simp)
  apply (
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto)
  )
  apply (case_tac "\<pi>\<^sub>2' = \<pi> ;; `xa", simp)
  apply (
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto)
  )
  apply (
    (case_tac "\<pi>\<^sub>1' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )
  apply (
    (case_tac "\<pi>\<^sub>2' \<notin> send_paths \<E> c"),
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto),
    (metis leaf_def option.distinct(1) prefixI prefix_snocD)+
  )

  apply (case_tac "\<pi>\<^sub>1' = \<pi>\<^sub>r ;; `x\<^sub>r", simp)
  apply (
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>2' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto)
  )
  apply (metis bind.inject(2) exp.inject(1) leaf_def option.inject prim.distinct(29) state.inject strict_prefixI' val.inject(2))
  apply (case_tac "\<pi>\<^sub>2' = \<pi>\<^sub>r ;; `x\<^sub>r", simp)
  apply (
    (thin_tac "\<forall>\<pi>\<^sub>1. \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow> (\<forall>\<pi>\<^sub>2. \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2)"),
    (thin_tac "\<pi>\<^sub>1' \<in> send_paths _ c"),
    ((unfold send_paths_def)[1]; auto)
  )
  apply (metis bind.inject(2) exp.inject(1) leaf_def option.inject prim.distinct(29) state.inject strict_prefixI' val.inject(2))

  apply (case_tac "(\<pi>\<^sub>1' = \<pi>\<^sub>s;;`x\<^sub>s) \<and> (\<pi>\<^sub>2' \<noteq> \<pi>\<^sub>s;;`x\<^sub>s) \<and> ca = c", simp)
  apply (blast dest: paths_exclusive_implies_equal_in_sync_case)
  apply (case_tac "(\<pi>\<^sub>1' \<noteq> \<pi>\<^sub>s;;`x\<^sub>s) \<and> (\<pi>\<^sub>2' = \<pi>\<^sub>s;;`x\<^sub>s) \<and> ca = c", simp)
  apply (blast dest: two_paths_exclusive_commut paths_exclusive_implies_equal_in_sync_case)

sorry


lemma send_paths_exclusive_implies_equal_star'': "
  \<lbrakk>
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow> 
  
  (\<forall> \<pi>\<^sub>1' \<pi>\<^sub>2' .
  (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow>
    \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow>
    \<pi>\<^sub>1 = \<pi>\<^sub>2
  ) \<longrightarrow>
    \<pi>\<^sub>1' \<in> send_paths \<E>' c \<longrightarrow>
    \<pi>\<^sub>2' \<in> send_paths \<E>' c \<longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' \<longrightarrow>
    \<pi>\<^sub>1' = \<pi>\<^sub>2'
  )
"
apply (erule star.induct; auto)
apply (rename_tac \<E> \<E>' \<E>'' \<pi>\<^sub>1'' \<pi>\<^sub>2'' \<pi>\<^sub>1' \<pi>\<^sub>2')
using paths_exclusive_implies_equal by blast

lemma send_paths_exclusive_implies_equal_star': "
  \<lbrakk>
    (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
      \<pi>\<^sub>1 \<in> send_paths \<E> c \<longrightarrow>
      \<pi>\<^sub>2 \<in> send_paths \<E> c \<longrightarrow>
      two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow>
      \<pi>\<^sub>1 = \<pi>\<^sub>2
    );
    \<E> \<rightarrow>* \<E>';
    \<pi>\<^sub>1' \<in> send_paths \<E>' c;
    \<pi>\<^sub>2' \<in> send_paths \<E>' c;
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' = \<pi>\<^sub>2'
"
using send_paths_exclusive_implies_equal_star'' by blast

lemma start_paths_exclusive_implies_equal: "
  \<lbrakk>
    \<pi>\<^sub>1 \<in> send_paths [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] c;
    \<pi>\<^sub>2 \<in> send_paths [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] c;
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  \<rbrakk> \<Longrightarrow>
  \<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (unfold send_paths_def, simp)


lemma send_paths_exclusive_implies_equal: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<pi>\<^sub>1' \<in> send_paths \<E>' c; 
    \<pi>\<^sub>2' \<in> send_paths \<E>' c; 
    two_paths_exclusive \<pi>\<^sub>1' \<pi>\<^sub>2' 
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1' = \<pi>\<^sub>2'
"
using send_paths_exclusive_implies_equal_star' start_paths_exclusive_implies_equal by blast

theorem topology_set_exclusive_send_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
  
    set_exclusive (abstract_send_paths (\<V>, \<C>, e) x\<^sub>c)
  \<rbrakk> \<Longrightarrow>
  set_paths_equal (send_paths \<E>' (Ch \<pi> x\<^sub>c))
"
 apply (unfold set_paths_equal_def; auto)
 apply (unfold set_exclusive_def; auto)
 apply (drule_tac x = \<pi>\<^sub>1 in spec; auto; (drule_tac x = \<pi>\<^sub>2 in spec; auto)?)
 apply (blast dest: isnt_send_path_sound)
 apply (blast dest: isnt_send_path_sound)
 apply (blast intro: send_paths_exclusive_implies_equal send_paths_exclusive_implies_equal_star')
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
sorry


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
sorry

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