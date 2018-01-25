theory Abstract_Value_Flow_Soundness
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin


lemma flow_state_to_flow_exp: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e\<^sub>\<kappa>
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_stack.cases, auto)
done

lemma flow_over_state_to_env: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (erule accept_stack.cases, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_val_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
    apply (drule spec[of _ x]; auto)
     apply (erule accept_stack.cases; auto)+
    apply (erule accept_val_env.cases; auto)+
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
   apply (drule spec[of _ x]; auto)
    apply (erule accept_stack.cases; auto)+
   apply (erule accept_val_env.cases; auto)+
done

lemma flow_over_state_to_stack: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply (drule spec)+
 apply (erule impE, auto)
 apply (erule accept_stack.cases, auto)+
done

lemma flow_over_state_1: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp, auto)
   apply (erule flow_over_state_to_env, auto)
  apply (erule flow_over_state_to_stack, auto)
done

lemma flow_state_to_flow_exp_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_state_to_env_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)
"
 apply (rule accept_value_accept_val_env.Any, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_exp.cases, auto)
    apply (rule accept_value_accept_val_env.Unit)
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
  apply (erule accept_state.cases, auto)
 apply (erule accept_val_env.cases, auto)
done

lemma flow_over_state_to_stack_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_2)
   apply (erule flow_over_state_to_env_2)
  apply (erule flow_over_state_to_stack_2)
done

lemma flow_over_state_to_exp_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)  
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_state_to_env_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)
"
 apply (rule accept_value_accept_val_env.Any, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_exp.cases, auto)
    apply (erule accept_state.cases, auto)
    apply ((erule accept_exp.cases, auto); rule, auto)
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
   apply (erule accept_state.cases, auto)
  apply (erule accept_val_env.cases, auto)
done

lemma flow_over_state_to_stack_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_over_state_to_exp_3)
   apply (erule flow_over_state_to_env_3)
  apply (erule flow_over_state_to_stack_3)
done

lemma flow_state_to_flow_exp_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e\<^sub>l
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply ((drule spec)+, auto)
done

lemma flow_state_to_flow_env_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>s]; auto)
      apply (erule accept_value.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>l']; auto)
      apply (erule accept_exp.cases, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_val_env.cases, auto)
     apply (drule spec[of _ x\<^sub>s]; auto)
     apply (erule accept_value.cases, auto)
     apply (erule accept_val_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_state_to_flow_stack_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
 apply (rule accept_stack.Nonempty)
    apply (erule accept_state.cases, auto, rename_tac \<omega>)
    apply (erule accept_val_env.cases, auto)
    apply (drule spec[of _ x\<^sub>s]; auto)
    apply (erule accept_exp.cases, auto)
   apply (erule accept_state.cases, auto)
   apply (erule accept_exp.cases, auto)
  apply (erule accept_state.cases, auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_4, simp, auto)
   apply (erule flow_state_to_flow_env_4, simp, auto)
  apply (erule flow_state_to_flow_stack_4, simp, auto)
done

lemma flow_state_to_flow_exp_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e\<^sub>r
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply ((drule spec)+, auto)
done

lemma flow_state_to_flow_env_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>s]; auto)
      apply (erule accept_value.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>r']; auto)
      apply (erule accept_exp.cases, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_val_env.cases, auto)
     apply (drule spec[of _ x\<^sub>s]; auto)
     apply (erule accept_value.cases, auto)
     apply (erule accept_val_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_state_to_flow_stack_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
 apply (rule accept_stack.Nonempty)
    apply (erule accept_state.cases, auto, rename_tac \<omega>)
    apply (erule accept_val_env.cases, auto)
    apply (drule spec[of _ x\<^sub>s]; auto)
    apply (erule accept_exp.cases, auto)
   apply (erule accept_state.cases, auto)
   apply (erule accept_exp.cases, auto)
  apply (erule accept_state.cases, auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_5, simp, auto)
   apply (erule flow_state_to_flow_env_5, simp, auto)
  apply (erule flow_state_to_flow_stack_5, simp, auto)
done


lemma flow_state_to_flow_exp_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_state_to_flow_env_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>p]; auto)
      apply (erule accept_value.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>1]; auto)
      apply (erule accept_exp.cases, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_val_env.cases, auto)
     apply (drule spec[of _ x\<^sub>p]; auto)
     apply (erule accept_value.cases, auto)
     apply (erule accept_val_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_state_to_flow_stack_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_6, simp, auto)
   apply (erule flow_state_to_flow_env_6, simp, auto)
  apply (erule flow_state_to_flow_stack_6, simp, auto)
done

lemma flow_state_to_flow_exp_7: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_state_to_flow_env_7: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>p]; auto)
      apply (erule accept_value.cases, auto)
      apply (erule accept_val_env.cases, auto)
      apply (drule spec[of _ x\<^sub>2]; auto)
      apply (erule accept_exp.cases, auto)
     apply (erule accept_state.cases, auto)
     apply (erule accept_val_env.cases, auto)
     apply (drule spec[of _ x\<^sub>p]; auto)
     apply (erule accept_value.cases, auto)
     apply (erule accept_val_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_state_to_flow_stack_7: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_7: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_7, simp, auto)
   apply (erule flow_state_to_flow_env_7, simp, auto)
  apply (erule flow_state_to_flow_stack_7, simp, auto)
done

lemma flow_state_to_flow_exp_8: "
 (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
 \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
 (\<V>, \<C>) \<Turnstile>\<^sub>e  e\<^sub>l
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply (drule spec[of _ f]; auto)
 apply (erule accept_value.cases, auto)
done

lemma flow_state_to_flow_env_8: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a)
"
 apply (rule accept_value_accept_val_env.Any, auto)
           apply (erule accept_state.cases, auto)
           apply (erule accept_exp.cases, auto, (drule spec)+, auto)
            apply (erule accept_val_env.cases, auto, (drule spec)+, auto)
           apply (erule accept_val_env.cases, auto)
          apply (erule accept_state.cases, auto)
          apply (erule accept_val_env.cases, auto)
         apply (erule accept_state.cases, auto)
         apply (erule accept_val_env.cases, auto)
         apply (drule spec[of _ f]; auto)
         apply (erule accept_value.cases, auto)
        apply (erule accept_state.cases, auto)
        apply (erule accept_val_env.cases, auto)
       apply (erule accept_state.cases, auto)
       apply (erule accept_val_env.cases, auto)
       apply (frule spec[of _ f])
       apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
       apply (drule spec[of _ x\<^sub>a])
       apply (drule spec[of _ \<omega>\<^sub>a], auto)
       apply (erule accept_exp.cases, auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_val_env.cases, auto)
     apply (rename_tac x' \<omega>)
     apply (erule accept_state.cases, auto)
     apply (erule accept_val_env.cases, auto)
     apply (frule spec[of _ f])
     apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
     apply (drule spec[of _ x\<^sub>a])
     apply (drule spec[of _ \<omega>\<^sub>a]; auto)
     apply (erule accept_value.cases, auto)
     apply (erule accept_val_env.cases, auto)
    apply (rename_tac x' \<omega>)
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
    apply (frule spec[of _ f])
    apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
    apply (drule spec[of _ x\<^sub>a])
    apply (drule spec[of _ \<omega>\<^sub>a]; auto)
    apply (erule accept_value.cases, auto)
    apply (erule accept_val_env.cases, auto)
done

lemma flow_state_to_flow_stack_8: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
 apply (rule accept_stack.Nonempty)
    apply (erule accept_state.cases, auto) 
    apply (erule accept_exp.cases, auto)
    apply (erule accept_val_env.cases, (drule spec)+, auto)
   apply (erule accept_state.cases, auto) 
   apply (erule accept_exp.cases, auto)
  apply (erule accept_state.cases, auto) 
 apply (erule accept_state.cases, auto) 
done

lemma flow_over_state_8: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>l; \<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_8, simp, auto)
   apply (erule flow_state_to_flow_env_8, simp, auto)
  apply (erule flow_state_to_flow_stack_8, simp, auto)
done

theorem flow_over_state_preservation : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>; 
    \<sigma> \<hookrightarrow> \<sigma>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'
"
 apply (erule seq_step.cases, auto)
        apply (erule flow_over_state_1, auto)
       apply (erule flow_over_state_2)
      apply (erule flow_over_state_3)
     apply (erule flow_over_state_4, simp, auto)
    apply (erule flow_over_state_5, simp, auto)
   apply (erule flow_over_state_6, simp, auto)
  apply (erule flow_over_state_7, simp, auto)
 apply (erule flow_over_state_8, auto)
done

lemma flow_seq_step_down_preservation: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
sorry

lemma flow_seq_step_up_preservation: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>;;\<upharpoonleft>x \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
sorry

lemma flow_seq_step_preservation: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
  apply (erule flow_over_state_preservation, auto)
 apply (erule accept_state_pool.cases, auto)
done

lemma flow_over_pool_to_exp_1: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_1: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)
"
apply (rule accept_value_accept_val_env.Any; auto)
    apply (erule accept_state_pool.cases, auto)
    apply (frule spec[of _ \<pi>\<^sub>s])
    apply (drule spec[of _ \<pi>\<^sub>r])
    apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"])
    apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"])
    apply (drule mp[of "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) "])
    apply (drule mp[of "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"], auto)
    apply (erule accept_state.cases[of "(\<V>, \<C>)" "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
    apply (erule accept_state.cases[of "(\<V>, \<C>)" "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
    apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>r"], auto)
    apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s"], auto)
    apply (drule spec[of _ x\<^sub>r\<^sub>e])
    apply (drule spec[of _ x\<^sub>s\<^sub>e])
    apply (drule spec[of _ "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"])
    apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
    apply (drule mp[of "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"], simp)
    apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
    apply (erule accept_value.cases[of "(\<V>, \<C>)" "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"]; auto)
    apply (erule accept_value.cases[of "(\<V>, \<C>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
    apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>r\<^sub>e"], auto)
    apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s\<^sub>e"], auto)
    apply (erule accept_exp.cases[of "(\<V>, \<C>)" "LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r"]; auto)
    apply (erule accept_exp.cases[of "(\<V>, \<C>)" "LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s"]; auto)
    apply (thin_tac "\<forall>x\<^sub>s\<^sub>c x\<^sub>m. ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow> ^\<lparr>\<rparr> \<in> \<V> x\<^sub>r \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c)")
    apply (thin_tac "\<forall>x\<^sub>r\<^sub>c. ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>s\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>s)")
    apply (drule spec[of _ x\<^sub>r\<^sub>c])
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (drule spec[of _ x\<^sub>r\<^sub>c])
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (case_tac c; auto)
    apply (rule accept_value_accept_val_env.Unit)
   apply (erule accept_state_pool.cases, auto)
   apply (drule spec[of _ \<pi>\<^sub>s])
   apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"]; auto)
   apply (erule accept_state.cases; auto)
   apply (drule accept_val_env.cases; auto)
  apply (erule accept_state_pool.cases, auto)
  apply (drule spec[of _ \<pi>\<^sub>s])
  apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"]; auto)
  apply (erule accept_state.cases; auto)
  apply (drule accept_val_env.cases; auto)
done

lemma flow_over_pool_to_stack_1: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
 apply (erule accept_state.cases, auto) 
done

lemma flow_over_pool_to_exp_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e  e\<^sub>r
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>r])
 apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
apply (rule accept_value_accept_val_env.Any; auto)
      apply (erule accept_state_pool.cases, auto)
      apply (frule spec[of _ \<pi>\<^sub>s])
      apply (drule spec[of _ \<pi>\<^sub>r])
      apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"])
      apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"])
      apply (drule mp[of "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) "])
      apply (drule mp[of "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"], auto)
      apply (erule accept_state.cases[of "(\<V>, \<C>)" "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
      apply (erule accept_state.cases[of "(\<V>, \<C>)" "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
      apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>r"], auto)
      apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s"], auto)
      apply (drule spec[of _ x\<^sub>r\<^sub>e])
      apply (drule spec[of _ x\<^sub>s\<^sub>e])
      apply (drule spec[of _ "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"])
      apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
      apply (drule mp[of "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"], simp)
      apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
      apply (erule accept_value.cases[of "(\<V>, \<C>)" "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"]; auto)
      apply (erule accept_value.cases[of "(\<V>, \<C>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
      apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>r\<^sub>e"], auto)
      apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s\<^sub>e"], auto)
      apply (erule accept_exp.cases[of "(\<V>, \<C>)" "LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r"]; auto)
      apply (erule accept_exp.cases[of "(\<V>, \<C>)" "LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s"]; auto)
      apply (thin_tac "\<forall>x\<^sub>s\<^sub>c x\<^sub>m. ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow> ^\<lparr>\<rparr> \<in> \<V> x\<^sub>r \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c)")
      apply (thin_tac "\<forall>x\<^sub>r\<^sub>c. ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>s\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>s)")
      apply (drule spec[of _ x\<^sub>r\<^sub>c])
      apply (frule spec[of _ x\<^sub>s\<^sub>c])
      apply (drule spec[of _ x\<^sub>m])
      apply (drule spec[of _ x\<^sub>r\<^sub>c])
      apply (drule spec[of _ x\<^sub>s\<^sub>c])
      apply (drule spec[of _ "\<lbrace>c\<rbrace>"])
      apply (drule spec[of _ "\<lbrace>c\<rbrace>"])
      apply (drule spec[of _ "\<omega>\<^sub>m"])
      apply (drule spec[of _ "x\<^sub>m"])
      apply (case_tac c, rename_tac \<pi> x\<^sub>c, auto)

    apply (erule accept_state_pool.cases, auto)
    apply (drule spec[of _ \<pi>\<^sub>s])
    apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"])
    apply (drule mp[of "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) "], auto)
    apply (erule accept_state.cases[of "(\<V>, \<C>)" "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
    apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s"], auto)
    apply (drule spec[of _ x\<^sub>s\<^sub>e])
    apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
    apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
    apply (erule accept_value.cases[of "(\<V>, \<C>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
    apply (erule accept_val_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s\<^sub>e"], auto)
   apply (erule accept_state_pool.cases, auto)
   apply (drule spec[of _ \<pi>\<^sub>r])
   apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"]; auto)
   apply (erule accept_state.cases; auto)
   apply (drule accept_val_env.cases; auto)
  apply (erule accept_state_pool.cases, auto)
  apply (drule spec[of _ \<pi>\<^sub>r])
  apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"]; auto)
  apply (erule accept_state.cases; auto)
  apply (drule accept_val_env.cases; auto)
done

lemma flow_over_pool_to_stack_2: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>r])
 apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
 apply (erule accept_state.cases, auto) 
done

lemma flow_let_sync_preservation: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>)
"
 apply (rule accept_state_pool.Any, auto)
     apply (rule accept_state.Any)
      apply (erule flow_over_pool_to_exp_1, auto)
     apply (erule flow_over_pool_to_env_1; (erule Pure.asm_rl)+)
    apply (erule flow_over_pool_to_stack_1, auto)
   apply (rule accept_state.Any)
     apply (erule flow_over_pool_to_exp_1, auto)
    apply ((erule flow_over_pool_to_env_1); (erule Pure.asm_rl)+)
   apply (erule flow_over_pool_to_stack_1, auto)
   apply (unfold not_def, erule impE, auto)
   apply (rule accept_state.Any)
   apply (erule flow_over_pool_to_exp_2, auto)
     apply (erule flow_over_pool_to_env_2; (erule Pure.asm_rl)+)
    apply (erule flow_over_pool_to_stack_2, auto)
    apply (unfold not_def, erule impE, auto)
    apply (rule accept_state.Any)
     apply (erule flow_over_pool_to_exp_2, auto)
    apply ((erule flow_over_pool_to_env_2); (erule Pure.asm_rl)+)
   apply (erule flow_over_pool_to_stack_2; auto)
  apply (erule accept_state_pool.cases; auto)
done

lemma flow_over_pool_to_exp_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)
"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state_pool.cases, auto)
      apply (drule spec[of _ \<pi>])
      apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_exp.cases, auto)
     apply (rule accept_value_accept_val_env.Chan)
    apply (rename_tac x' \<omega>)
    apply (erule accept_state_pool.cases, auto)
    apply (drule spec[of _ \<pi>])
    apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
    apply (erule accept_state.cases, auto)
    apply (erule accept_exp.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (rename_tac x' \<omega>)
   apply (erule accept_state_pool.cases, auto)
   apply (drule spec[of _ \<pi>])
   apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
   apply (erule accept_state.cases, auto)
   apply (erule accept_exp.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_over_pool_to_stack_3: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_exp_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; `x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e  e'
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_env_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; `x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>'
"
 apply (rule accept_value_accept_val_env.Any, auto)
    apply (erule accept_state_pool.cases, auto)
    apply (drule spec[of _ \<pi>'])
    apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
    apply (erule accept_state.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (erule accept_state_pool.cases, auto)
   apply (drule spec[of _ \<pi>'])
   apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
   apply (erule accept_state.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_over_pool_to_stack_4: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; `x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e'\<rfloor>) \<Rrightarrow> \<kappa>'
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_let_chan_preservation: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>)
"
 apply (rule accept_state_pool.Any, auto)
  apply (rule accept_state.Any)
    apply (erule flow_over_pool_to_exp_3, auto)
   apply (erule flow_over_pool_to_env_3, auto)
  apply (erule flow_over_pool_to_stack_3, auto)
 apply (case_tac "\<sigma>", rename_tac e' \<rho>' \<kappa>', auto)
 apply (rule accept_state.Any)
   apply (erule flow_over_pool_to_exp_4, auto)
   apply (erule flow_over_pool_to_env_4, auto)
  apply (erule flow_over_pool_to_stack_4, auto)
done


lemma flow_over_pool_to_exp_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)"
 apply (rule accept_value_accept_val_env.Any, auto)
      apply (erule accept_state_pool.cases, auto)
      apply (drule spec[of _ \<pi>])
      apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
      apply (erule accept_state.cases, auto)
      apply (erule accept_exp.cases, auto)
     apply (rule accept_value_accept_val_env.Unit)
    apply (rename_tac x' \<omega>)
    apply (erule accept_state_pool.cases, auto)
    apply (drule spec[of _ \<pi>])
    apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
    apply (erule accept_state.cases, auto)
    apply (erule accept_exp.cases, auto)
    apply (erule accept_val_env.cases, auto)
   apply (rename_tac x' \<omega>)
   apply (erule accept_state_pool.cases, auto)
   apply (drule spec[of _ \<pi>])
   apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
   apply (erule accept_state.cases, auto)
   apply (erule accept_exp.cases, auto)
   apply (erule accept_val_env.cases, auto)
done

lemma flow_over_pool_to_stack_5: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_exp_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e  e\<^sub>c
"   
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
"   
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_stack_6: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []
"   
 apply (rule accept_stack.Empty)
done


lemma flow_let_spawn_preservation: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
"
  apply (rule accept_state_pool.Any, auto)
    apply (rule accept_state.Any)
     apply (erule flow_over_pool_to_exp_5, auto)
    apply (erule flow_over_pool_to_env_5, auto)
   apply (erule flow_over_pool_to_stack_5, auto)
   apply (unfold not_def, erule impE, auto)
   apply (rule accept_state.Any)
     apply (erule flow_over_pool_to_exp_6, auto)
    apply (erule flow_over_pool_to_env_6, auto)
   apply (erule flow_over_pool_to_stack_6, auto)
  apply (erule accept_state_pool.cases, auto)
done

theorem flow_preservation : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
 apply (erule concur_step.cases, auto)
       apply (erule flow_seq_step_down_preservation, auto)
     apply (erule flow_seq_step_up_preservation, auto)
    apply (erule flow_seq_step_preservation, auto)
   apply ((erule flow_let_sync_preservation; blast?), auto)
  apply (erule flow_let_chan_preservation, auto)
 apply (erule flow_let_spawn_preservation, auto)
sorry

theorem flow_preservation_star' : "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow>
  ((\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>')
"
 apply (erule star.induct[of concur_step], auto)
 apply (rename_tac \<E> \<E>' \<E>'')
 apply (erule notE)
 apply (erule flow_preservation, auto)
done
 

theorem flow_preservation_star : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;  
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
by (drule flow_preservation_star', auto)

theorem flow_over_env_precision : "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (unfold abstract_value_env_precision_def, unfold env_to_abstract_value_env_def)
 apply (rule allI, rename_tac x)
 apply (case_tac "\<rho> x = None", auto, rename_tac \<omega>)
 apply (erule accept_val_env.cases, auto)
done

theorem flow_over_state_precision : "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (erule accept_state.cases, auto)
 apply (erule flow_over_env_precision)
done

lemma flow_over_pool_to_state: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<pi> = Some \<sigma> 
  \<rbrakk>
  \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<sigma>
"
 apply (erule accept_state_pool.cases)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ \<sigma>])
 apply (erule impE, auto)
done
  
theorem flow_over_pool_precision : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;
    \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)
  \<rbrakk>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (drule flow_over_pool_to_state, simp)
 apply (erule flow_over_state_precision)
done

theorem lift_flow_exp_to_state: "(\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; empty; []\<rangle>"
 apply (rule accept_state.Any, auto)
 apply (rule+, auto, rule)
done

theorem  lift_flow_state_to_pool: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<sigma> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<sigma>]"
  apply (rule accept_state_pool.Any)
  apply (case_tac "\<pi> = []", auto)
done

theorem lift_flow_exp_to_pool: "(\<V>, \<C>) \<Turnstile>\<^sub>e  e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]"
  apply (drule lift_flow_exp_to_state)
  apply (erule lift_flow_state_to_pool)
done

theorem flow_over_pool_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule flow_preservation_star[of \<V> \<C> _ \<E>'], auto)
 apply (erule flow_over_pool_precision[of \<V> \<C> \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done


theorem isnt_abstract_value_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e; 
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule lift_flow_exp_to_pool)
 apply (erule flow_over_pool_sound [of \<V> \<C> _ \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done

corollary isnt_abstract_value_sound_coro: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e ;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
    \<rho>' x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
  apply (drule isnt_abstract_value_sound; assumption?)
  apply (unfold abstract_value_env_precision_def)
  apply (unfold env_to_abstract_value_env_def)
  apply (drule spec[of _ x]; auto)
done

lemma nonempty_pool: "
  \<lbrakk>
    \<E> \<rightarrow> \<E>'
  \<rbrakk>\<Longrightarrow>
  (\<exists> \<pi> e \<rho> \<kappa> \<pi>' e' \<rho>' \<kappa>'. 
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<and> 
    leaf \<E> \<pi> \<and>
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<and>
    prefix \<pi> \<pi>'
  )
"
 apply (erule concur_step.cases, auto, blast)
done

lemma trace_preservation: "
  \<E> \<rightarrow> \<E>' \<Longrightarrow> 
  \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>)
"
 apply (erule concur_step.cases; (erule seq_step.cases)?; auto)
 apply (metis leaf_def option.distinct(1) strict_prefixI')+
done

lemma nonempty_pool_star_left: "
  \<lbrakk>
   star_left op \<rightarrow> \<E> \<E>\<^sub>m
  \<rbrakk>\<Longrightarrow>
  (\<forall> \<E>'' . \<E>\<^sub>m \<rightarrow> \<E>'' \<longrightarrow> 
  (\<forall> \<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> leaf \<E> \<pi> \<longrightarrow>
  (\<forall> \<pi>'' e'' \<rho>'' \<kappa>''. \<E>'' \<pi>'' = Some (\<langle>e'';\<rho>'';\<kappa>''\<rangle>) \<longrightarrow> prefix \<pi> \<pi>'' \<longrightarrow>
      (\<exists> \<pi>\<^sub>m e\<^sub>m \<rho>\<^sub>m \<kappa>\<^sub>m .
        \<E>\<^sub>m \<pi>\<^sub>m = Some (\<langle>e\<^sub>m;\<rho>\<^sub>m;\<kappa>\<^sub>m\<rangle>) \<and>
        prefix \<pi> \<pi>\<^sub>m \<and>
        leaf \<E>\<^sub>m \<pi>\<^sub>m \<and>
        prefix \<pi>\<^sub>m \<pi>''
      )
   )))
"
 apply (erule star_left.induct, blast)
 apply (rename_tac \<E> \<E>\<^sub>m \<E>')
 apply (drule spec, erule impE, assumption)
 apply (rule allI, rule impI, (rule allI)+, rule impI, rule impI, (rule allI)+, (rule impI)+)
 apply ((drule spec)+, erule impE, assumption)
 apply (erule impE, assumption)
 apply (drule nonempty_pool, (erule exE)+, (erule conjE)+)
 apply ((drule spec)+, erule impE, assumption)
 apply (erule impE)
sorry

lemma isnt_traceable_sound''': "
  \<lbrakk>
    \<E> \<rightarrow> \<E>';
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>); leaf \<E> \<pi>;
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
    prefix \<pi>\<^sub>m \<pi>';
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e); (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>', e')
"
 apply (erule concur_step.cases; (erule seq_step.cases; auto)?)
sorry

lemma isnt_traceable_sound'': "
   star_left op \<rightarrow> \<E> \<E>\<^sub>m \<Longrightarrow>
   \<E>\<^sub>m \<rightarrow> \<E>' \<Longrightarrow>
   (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>

   \<forall>\<pi> e. \<V> \<turnstile> e\<^sub>0 \<down>  (\<pi>, e) \<longrightarrow>
              (\<exists>\<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>)) \<longrightarrow>
              leaf \<E> \<pi> \<longrightarrow> (\<forall>\<pi>' e'. (\<exists>\<rho>' \<kappa>'. \<E>\<^sub>m \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)) \<longrightarrow> prefix \<pi> \<pi>' \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down>  (\<pi>', e')) \<Longrightarrow>

   \<V> \<turnstile> e\<^sub>0 \<down>  (\<pi>, e) \<Longrightarrow> \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> prefix \<pi> \<pi>' \<Longrightarrow> 
   \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>', e')
"
 apply (frule nonempty_pool_star_left)
 apply (drule star_left_implies_star)
 apply (drule flow_preservation_star, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ \<E>'])
 apply (drule spec[of _ e])
 apply simp
 apply (drule spec[of _ \<pi>])
 apply (erule impE, (rule exI)+, assumption)
 apply (erule impE, assumption)
 apply (rotate_tac 9)
 apply (drule spec[of _ \<pi>'])
 apply (erule impE, (rule exI)+, assumption)
 apply (erule impE, assumption)
 apply ((erule exE), (erule conjE), (erule exE), (erule conjE)+, (erule exE)+)
 apply ((drule spec)+, erule impE, (rule exI)+, assumption)
 apply (erule impE, assumption)
 apply (erule accept_state_pool.cases, auto)
 apply ((drule spec)+, erule impE, assumption)
 apply (erule accept_state.cases, auto)
 apply (rename_tac \<pi>\<^sub>m e\<^sub>m \<rho>\<^sub>m \<kappa>\<^sub>m)
 apply (erule isnt_traceable_sound'''; auto)
done

lemma isnt_traceable_sound': "
  \<lbrakk>
    star_left op \<rightarrow> \<E> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow>
  (\<forall> \<pi> e \<rho> \<kappa> \<pi>' e' \<rho>' \<kappa>' .
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e) \<longrightarrow>
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
    leaf \<E> \<pi> \<longrightarrow>
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow>
    prefix \<pi> \<pi>' \<longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>', e')
  )
"
 apply (erule star_left.induct, auto)
  apply (metis leaf_def option.distinct(1) option.sel prefix_order.dual_order.order_iff_strict state.inject)
 apply (rename_tac \<E> \<E>\<^sub>m \<E>' \<pi> e \<rho> \<kappa> \<pi>' e' \<rho>' \<kappa>')
 apply (insert isnt_traceable_sound''[of _ _ _ \<V> \<C> e\<^sub>0], blast)
done

lemma first_step_implies_traceable: "
  [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow> \<E> 
  \<Longrightarrow>
  (\<exists> \<pi> e \<rho> \<kappa> . 
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<and>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e)
  ) 
"
by (meson Start fun_upd_same trace_preservation)

lemma isnt_traceable_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>0;
    [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) 
  \<rbrakk> \<Longrightarrow>
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>', e')
"
 apply (erule star.cases, auto)
  apply (metis Start option.sel option.simps(3) state.inject)
 apply (frule first_step_implies_traceable[of _ _ \<V>])
 apply (rename_tac \<E>, auto)
 apply (drule star_implies_star_left)
 apply (insert isnt_traceable_sound'[of _ \<E>' \<V> \<C> e\<^sub>0], auto)
 apply (smt Nil_prefix Start fun_upd_apply leaf_def lift_flow_exp_to_pool nonempty_pool star_left_step1 star_left_trans)
done

end
