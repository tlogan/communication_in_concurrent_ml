theory Sound_Communication
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics 
    Sound_Semantics
    Dynamic_Communication
    Static_Communication
begin

lemma path_statePreservedDynamicEval_for_non_leaf: "
(env, H) \<rightarrow> (E', H') \<Longrightarrow>
E' (\<pi> @ [l]) = Some \<sigma> \<Longrightarrow>
\<not> leaf env \<pi> \<Longrightarrow>
env (\<pi> @ [l]) = Some \<sigma>
"
apply (erule dynamicEval.cases; auto; (erule seqEval.cases; auto)?)
  apply presburger+
  apply (metis append1_eq_conv fun_upd_other)
  apply (metis butlast_snoc fun_upd_apply)
done


lemma spawn_point: "
  (env, H) \<rightarrow> (E', H') \<Longrightarrow>
  leaf env \<pi> \<Longrightarrow>
  E' (\<pi> @ [l1]) = Some \<sigma>1 \<Longrightarrow>
  E' (\<pi> @ [l2]) = Some \<sigma>2 \<Longrightarrow>
  l1 = l2 \<or> 
  (\<exists> x . l1 = (LNxt x) \<and> l2 = (LSpwn x)) \<or>
  (\<exists> x . l1 = (LSpwn x) \<and> l2 = (LNxt x))
"
apply (erule dynamicEval.cases; auto; (erule seqEval.cases; auto)?)
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis leaf.cases option.distinct(1) strict_prefixI')
  apply (metis (mono_tags, lifting) append1_eq_conv fun_upd_apply leaf.cases option.distinct(1) strict_prefixI')
  apply (smt butlast_snoc tm.inject(1) fun_upd_apply last_snoc leaf.cases option.distinct(1) option.inject state.inject strict_prefixI')
done

lemma staticEvalSendEvtSound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H');
    \<E>' \<pi>\<^sub>y = Some (Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>y) \<rho>\<^sub>y \<kappa>\<^sub>y);
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {SAtm (SendEvt x\<^sub>s\<^sub>c x\<^sub>m)} \<subseteq> V x\<^sub>e
"
  apply (drule staticEvalSound; assumption?; auto)
done

lemma staticEvalRecvEvtSound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H');
    \<E>' \<pi>\<^sub>y = Some (Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>y) \<rho>\<^sub>y \<kappa>\<^sub>y);
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {SAtm (RecvEvt x\<^sub>r\<^sub>c)} \<subseteq> V x\<^sub>e
"
  apply (drule staticEvalSound; assumption?; auto)
done

lemma staticEvalSendChanSound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi> xC));
    \<rho>\<^sub>y x\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>y) \<rho>\<^sub>y \<kappa>\<^sub>y);
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H');
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  SChn xC \<in> V x\<^sub>s\<^sub>c
"
 apply (frule staticEval_to_pool)
 apply (drule staticEvalPreserved[of _ _ _ ]; assumption?)
 apply (erule staticEvalPool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "(Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>y) \<rho>\<^sub>y \<kappa>\<^sub>y)"], simp)
 apply (erule staticEvalState.cases; auto)
 apply (erule staticEvalEnv.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule staticEvalVal.cases; auto)
 apply (erule staticEvalEnv.cases; auto)
 apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ "(VChn (Ch \<pi> xC))"]; simp)
done

lemma staticEvalRecvChanSound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi> xC));
    \<rho>\<^sub>y x\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>y) \<rho>\<^sub>y \<kappa>\<^sub>y);
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H');
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  SChn xC \<in> V x\<^sub>r\<^sub>c
"
 apply (frule staticEval_to_pool)
 apply (drule staticEvalPreserved[of _ _ _ ]; assumption?)
 apply (erule staticEvalPool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "(Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>y) \<rho>\<^sub>y \<kappa>\<^sub>y)"], simp)
 apply (erule staticEvalState.cases; auto)
 apply (erule staticEvalEnv.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule staticEvalVal.cases; auto)
 apply (erule staticEvalEnv.cases; auto)
 apply (drule spec[of _ x\<^sub>r\<^sub>c], drule spec[of _ "(VChn (Ch \<pi> xC))"]; simp)
done

lemma staticSendSiteSound: "
  \<E> \<pi>Sync = Some (Stt (Bind x (Sync x\<^sub>e) e\<^sub>n) \<rho> \<kappa>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>C xC)) \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (\<E>, H) \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  staticSendSite V e0 xC (IdBind x)
"
 apply (unfold staticSendSite.simps; auto)
 apply (rule exI[of _ x\<^sub>s\<^sub>c]; auto) 
 apply (auto simp: staticEvalSendChanSound)
 apply (rule exI[of _ x\<^sub>m]; auto?)
  apply (rule exI[of _ x\<^sub>e]; auto?)
   apply (blast dest: staticEvalSendEvtSound)
  using staticReachableSound apply blast
done

lemma staticRecvSiteSound: "
  \<E>' \<pi>Sync = Some (Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>n) \<rho> \<kappa>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>C xC)) \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticRecvSite V e xC (IdBind x\<^sub>y)
"
 apply (unfold staticRecvSite.simps; auto)
 apply (rule exI[of _ x\<^sub>r\<^sub>c]; auto)
 apply (auto simp: staticEvalRecvChanSound)
 apply (rule exI[of _ x\<^sub>e]; auto?)
   apply (blast dest: staticEvalRecvEvtSound)
  using staticReachableSound apply blast
done

end
