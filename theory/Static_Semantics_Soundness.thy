theory Static_Semantics_Soundness
  imports Main Syntax Runtime_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin


lemma accept_state_to_exp_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" by (simp add: accept_state.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (rule accept_stack.cases; auto)
qed


lemma accept_state_to_exp_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l
"
proof -
  assume "\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e"  
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>"
  by (simp add: accept_state.simps)+ then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: accept_val_env.simps)
  with `\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>`
  have "^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s" by fastforce
  with `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l"
  proof cases
    case Let_Case 
    with 
      `\<forall>x\<^sub>l'. ^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l`  
      `^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" by blast
  qed
qed


lemma accept_state_to_exp_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r
"
proof -
  assume "\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e"  
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" 
    by (simp add: accept_state.simps)+ then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: accept_val_env.simps)
  with `\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>`
  have "^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s" by fastforce
  with `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r"
  proof cases
    case Let_Case 
    with 
      `\<forall>x\<^sub>r'. ^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r`  
      `^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by blast
  qed
qed


lemma accept_state_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = b in e" by (simp add: accept_state.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (rule accept_exp.cases; auto)
qed


lemma accept_state_to_exp_let_app: "
 (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
 \<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace> \<Longrightarrow>
 (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b
"

proof -
  assume "\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps) then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: accept_val_env.simps)
  with `\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>" by simp then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b" by (rule accept_value.cases; auto)
qed


lemma accept_state_to_env_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
"
proof
 assume "\<rho> x = Some \<omega> "
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (rule accept_state.cases; auto)+ then
 show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
 proof cases
   case Nonempty
   {
     fix x' \<omega>'
     assume "(\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x' = Some \<omega>'" and "x' = x\<^sub>\<kappa>" then
     have "\<omega>' = \<omega>" by simp

     from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x = Some \<omega>`
     have "{|\<omega>|} \<subseteq> \<V> x" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: accept_val_env.simps)+
     with `\<V> x \<subseteq> \<V> x\<^sub>\<kappa>` `x' = x\<^sub>\<kappa>` `\<omega>' = \<omega>`
     have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by blast
   } moreover
   {
     fix x' \<omega>'
     assume "(\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x' = Some \<omega>'" and "x' \<noteq> x\<^sub>\<kappa>" then
     have "\<rho>\<^sub>\<kappa> x' = Some \<omega>'" by simp 
     with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>`
     have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)+
   } then
   show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" using calculation by auto
 qed
qed

(*
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
*)

lemma accept_state_to_stack_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply (drule spec)+
 apply (erule impE, auto)
 apply (erule accept_stack.cases, auto)+
done

lemma accept_state_to_state_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_result)
   apply (erule accept_state_to_env_result, auto)
  apply (erule accept_state_to_stack_result, auto)
done


lemma accept_state_to_env_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)
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

lemma accept_state_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma accept_state_to_state_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let)
   apply (erule accept_state_to_env_let_unit)
  apply (erule accept_state_to_stack_let)
done

lemma accept_state_to_env_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)
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

lemma accept_state_to_state_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let)
   apply (erule accept_state_to_env_let_prim)
  apply (erule accept_state_to_stack_let)
done


lemma accept_state_to_env_let_case_left: "
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

lemma accept_state_to_stack_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
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

lemma accept_state_to_state_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let_case_left, simp)
   apply (erule accept_state_to_env_let_case_left, simp, auto)
  apply (erule accept_state_to_stack_let_case_left, simp, auto)
done

lemma accept_state_to_env_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
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

lemma accept_state_to_stack_let_case_right: "
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

lemma accept_state_to_state_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let_case_right, simp)
   apply (erule accept_state_to_env_let_case_right, simp, auto)
  apply (erule accept_state_to_stack_let_case_right, simp, auto)
done


lemma accept_state_to_env_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
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

lemma accept_state_to_state_left_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let)
   apply (erule accept_state_to_env_let_fst, simp, auto)
  apply (erule accept_state_to_stack_let)
done

lemma accept_state_to_env_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
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


lemma accept_state_to_state_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let)
   apply (erule accept_state_to_env_let_snd, simp, auto)
  apply (erule accept_state_to_stack_let)
done

lemma accept_state_to_env_let_app: "
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

lemma accept_state_to_stack_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
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


lemma accept_state_to_state_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>b; \<rho>'(f' \<mapsto> \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>, x\<^sub>p \<mapsto> \<omega>\<^sub>a); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule accept_state_to_exp_let_app, simp)
   apply (erule accept_state_to_env_let_app, simp, auto)
  apply (erule accept_state_to_stack_let_app, simp, auto)
done


theorem accept_state_preserved_under_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>; 
    \<sigma> \<hookrightarrow> \<sigma>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'
"
 apply (erule seq_step.cases, auto)
  apply (simp add: accept_state_to_state_result)
  apply (simp add: accept_state_to_state_let_unit)
  apply (simp add: accept_state_to_state_let_prim)
  apply (simp add: accept_state_to_state_left_fst)
  apply (simp add: accept_state_to_state_let_snd)
  apply (simp add: accept_state_to_state_let_case_left)
  apply (simp add: accept_state_to_state_let_case_right)
  apply (simp add: accept_state_to_state_let_app)
done

lemma accept_preserved_under_seq_step_down: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
  apply (simp add: accept_state_preserved_under_step)
  apply (simp add: accept_state_pool.simps)
done

lemma accept_preserved_under_seq_step_up: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>;;\<upharpoonleft>x \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
  apply (simp add: accept_state_preserved_under_step)
  apply (simp add: accept_state_pool.simps)
done

lemma accept_preserved_under_seq_step: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
  apply (erule accept_state_preserved_under_step, auto)
 apply (erule accept_state_pool.cases, auto)
done

lemma accept_pool_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma accept_pool_to_env_let_sync_send: "
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

lemma accept_pool_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto) 
done


lemma accept_pool_to_env_let_sync_recv: "
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


lemma accept_preserved_under_sync: "
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
      apply (erule accept_pool_to_exp_let, auto)
     apply (erule accept_pool_to_env_let_sync_send; (erule Pure.asm_rl)+)
    apply (erule accept_pool_to_stack_let, auto)
   apply (rule accept_state.Any)
     apply (erule accept_pool_to_exp_let, auto)
    apply ((erule accept_pool_to_env_let_sync_send); (erule Pure.asm_rl)+)
   apply (erule accept_pool_to_stack_let, auto)
   apply (unfold not_def, erule impE, auto)
   apply (rule accept_state.Any)
   apply (erule accept_pool_to_exp_let, auto)
     apply (erule accept_pool_to_env_let_sync_recv; (erule Pure.asm_rl)+)
    apply (erule accept_pool_to_stack_let, auto)
    apply (unfold not_def, erule impE, auto)
    apply (rule accept_state.Any)
     apply (erule accept_pool_to_exp_let, auto)
    apply ((erule accept_pool_to_env_let_sync_recv); (erule Pure.asm_rl)+)
   apply (erule accept_pool_to_stack_let; auto)
  apply (erule accept_state_pool.cases; auto)
done



lemma accept_pool_to_env_let_chan: "
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


lemma accept_pool_to_exp_let_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; `x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e'
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma accept_pool_to_env_let_chan_inequal: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; `x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>'
"
by (smt accept_state.cases accept_state_pool.cases state.inject)


lemma accept_pool_to_stack_let_chan_inequal: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; `x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e'\<rfloor>) \<Rrightarrow> \<kappa>'
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma accept_preserved_under_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>)
"
 apply (rule accept_state_pool.Any, auto)
  apply (rule accept_state.Any)
    apply (erule accept_pool_to_exp_let, auto)
   apply (erule accept_pool_to_env_let_chan, auto)
  apply (erule accept_pool_to_stack_let, auto)
 apply (case_tac "\<sigma>", rename_tac e' \<rho>' \<kappa>', auto)
 apply (rule accept_state.Any)
   apply (erule accept_pool_to_exp_let_chan, auto)
   apply (erule accept_pool_to_env_let_chan_inequal, auto)
  apply (erule accept_pool_to_stack_let_chan_inequal, auto)
done

lemma accept_pool_to_env_let_spawn: "
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


lemma accept_pool_to_exp_let_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c
"   
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma accept_pool_to_env_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> 
  \<E> \<pi> = Some (\<langle>LET x = n in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
"   
by (smt accept_state.cases accept_state_pool.cases state.inject)



lemma accept_preserved_under_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
"
  apply (rule accept_state_pool.Any, auto)
    apply (rule accept_state.Any)
     apply (erule accept_pool_to_exp_let, auto)
    apply (erule accept_pool_to_env_let_spawn, auto)
   apply (erule accept_pool_to_stack_let, auto)
   apply (unfold not_def, erule impE, auto)
   apply (rule accept_state.Any)
     apply (erule accept_pool_to_exp_let_spawn, auto)
    apply (erule accept_pool_to_env_let, auto)
  apply (simp add: accept_stack.Empty)
  apply (erule accept_state_pool.cases, auto)
done

theorem accept_preserved_under_concur_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
 apply (erule concur_step.cases, auto)
   apply (erule accept_preserved_under_seq_step_down, auto)
   apply (erule accept_preserved_under_seq_step, auto)
   apply (erule accept_preserved_under_seq_step_up, auto)
   apply (erule accept_preserved_under_chan, auto)
   apply (erule accept_preserved_under_spawn, auto)
   apply ((erule accept_preserved_under_sync; blast?), auto)
done

theorem accept_preserved_under_concur_step_star' : "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow>
  ((\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>')
"
 apply (erule star.induct[of concur_step], auto)
 apply (rename_tac \<E> \<E>' \<E>'')
 apply (erule notE)
 apply (erule accept_preserved_under_concur_step, auto)
done
 

theorem accept_preserved_under_concur_step_star : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;  
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
by (drule accept_preserved_under_concur_step_star', auto)

theorem accept_env_to_precise : "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (unfold abstract_value_env_precision_def, unfold env_to_abstract_value_env_def)
 apply (rule allI, rename_tac x)
 apply (case_tac "\<rho> x = None", auto, rename_tac \<omega>)
 apply (erule accept_val_env.cases, auto)
done

theorem accept_state_to_precise : "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_env_to_precise)
done

lemma accept_pool_to_state: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<pi> = Some \<sigma> 
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>
"
 apply (erule accept_state_pool.cases)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ \<sigma>])
 apply (erule impE, auto)
done
  
theorem accept_pool_to_precise : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;
    \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)
  \<rbrakk>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (drule accept_pool_to_state, simp)
 apply (erule accept_state_to_precise)
done

theorem lift_accept_exp_to_state: "(\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; empty; []\<rangle>"
 apply (rule accept_state.Any, auto)
 apply (rule+, auto, rule)
done

theorem  lift_accept_state_to_pool: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<sigma> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<sigma>]"
  apply (rule accept_state_pool.Any)
  apply (case_tac "\<pi> = []", auto)
done

theorem lift_accept_exp_to_pool: "(\<V>, \<C>) \<Turnstile>\<^sub>e  e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]"
  apply (drule lift_accept_exp_to_state)
  apply (erule lift_accept_state_to_pool)
done

theorem accept_pool_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule accept_preserved_under_concur_step_star[of \<V> \<C> _ \<E>'], auto)
 apply (erule accept_pool_to_precise[of \<V> \<C> \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done


theorem isnt_abstract_value_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e; 
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule lift_accept_exp_to_pool)
 apply (erule accept_pool_sound [of \<V> \<C> _ \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done

corollary abstracted_value_exists: "
  \<lbrakk>
    \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>;
    \<rho>' x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
  apply (unfold abstract_value_env_precision_def)
  apply (unfold env_to_abstract_value_env_def)
  apply (drule spec[of _ x]; auto)
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
  apply fastforce
done

lemma traceable_exp_preserved_sync_recv_evt: "
\<lbrakk>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>);
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n;\<rho>\<^sub>r;\<kappa>'\<rangle>)
\<rbrakk> \<Longrightarrow> 
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> e\<^sub>n
"
 apply ((drule spec)+, erule impE, assumption)
 apply (drule accept_pool_to_precise; simp?; blast?)
 apply (drule abstracted_value_exists; simp; blast?; rule; auto)
done

lemma traceable_exp_preserved_sync_send_evt: "
\<lbrakk>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e';\<rho>\<^sub>s;\<kappa>'\<rangle>);
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>);
  \<pi>\<^sub>s \<noteq> \<pi>\<^sub>r
\<rbrakk> \<Longrightarrow> 
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> e'
"
 apply ((drule spec)+, erule impE, assumption)
 apply (drule accept_pool_to_precise[of \<V> \<C> _ "\<pi>\<^sub>s ;; `x\<^sub>s" e' "\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)" \<kappa>'], auto)
 apply (drule abstracted_value_exists; simp; blast?; rule traceable.Let_Sync; auto)
 apply (subgoal_tac "|\<lbrace>\<rbrace>| \<in> \<V> x\<^sub>s", assumption, simp)
done

lemma traceable_exp_preserved: "
\<lbrakk>
  \<E> \<rightarrow> \<E>';
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
  (\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>
  );
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
\<rbrakk> \<Longrightarrow>
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
apply (frule concur_step.cases, auto)
  
  apply (case_tac "\<pi>' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>", auto)
  apply (((drule spec)+, erule impE, assumption, erule conjE))
  apply (erule stack_traceable.cases; auto)
  apply (erule seq_step.cases; auto; rule traceable.Result; auto)
  
  apply (case_tac "\<pi>' = \<pi> ;; `x", auto)
  apply ((drule spec)+, erule impE, assumption, erule conjE)
  apply (drule accept_preserved_under_concur_step, auto)
  apply (drule accept_pool_to_precise, auto)
  apply (erule seq_step.cases, auto)
  apply (drule abstracted_value_exists; auto; simp; rule traceable.Let_Unit; auto)
  apply (drule abstracted_value_exists; auto; simp; rule traceable.Let_Prim; auto)
  apply (drule abstracted_value_exists; auto; rule traceable.Let_Fst; auto)
  apply (drule abstracted_value_exists; auto; rule traceable.Let_Snd; auto)
  
  apply (case_tac "\<pi>' = \<pi> ;; \<upharpoonleft>x", auto)
  apply ((drule spec)+, erule impE, assumption, erule conjE)
  apply (drule accept_pool_to_precise, auto)
  apply (erule seq_step.cases, auto)
  apply (drule abstracted_value_exists, simp+, rule traceable.Let_Case_Left; auto)
  apply (drule abstracted_value_exists, simp+, rule traceable.Let_Case_Right; auto)
  apply (drule abstracted_value_exists, simp+, rule traceable.Let_App; auto)
  
  apply (case_tac "\<pi>' = \<pi> ;; `x", auto)
  apply (drule accept_preserved_under_concur_step, auto)
  apply (drule accept_pool_to_precise, auto)
  apply ((drule spec)+, erule impE, assumption, erule conjE)
  apply (drule abstracted_value_exists; auto; simp; rule traceable.Let_Chan; auto)
  
  apply (case_tac "\<pi>' = \<pi> ;; .x"; auto)
  apply ((drule spec)+, erule impE, assumption, erule conjE)
  apply (rule traceable.Let_Spawn_Child; auto)
  apply (case_tac "\<pi>' = \<pi> ;; `x"; auto; rule traceable.Let_Spawn; auto)
  
  
  apply (case_tac "\<pi>' = \<pi>\<^sub>r ;; `x\<^sub>r", auto)
  apply (drule accept_preserved_under_concur_step, auto)
  apply (meson traceable_exp_preserved_sync_recv_evt)
  apply (case_tac "\<pi>' = \<pi>\<^sub>s ;; `x\<^sub>s", auto)
  apply (drule accept_preserved_under_concur_step, auto)
  apply (meson traceable_exp_preserved_sync_send_evt)
  apply (smt exp.inject(1) accept_preserved_under_concur_step option.inject state.inject traceable_exp_preserved_sync_send_evt)

done


lemma traceable_stack_preserved: "
\<lbrakk>
  \<E> \<rightarrow> \<E>';
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>;
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> 
\<rbrakk> \<Longrightarrow>
\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> \<kappa>'
"
apply (frule concur_step.cases, auto)

apply (case_tac "\<pi>' = \<pi> ;; \<downharpoonleft>x\<^sub>\<kappa>", auto)
apply ((drule spec)+, erule impE, assumption, erule conjE)
apply (erule seq_step.cases; auto)
apply (erule stack_traceable.cases; auto)
  using Up_Down stack_traceable_preserved_over_balanced_extension apply blast

apply (case_tac "\<pi>' = \<pi> ;; `x", auto)
  using stack_traceable_preserved_over_seq_extension apply blast

apply (case_tac "\<pi>' = \<pi> ;; \<upharpoonleft>x", auto)
apply ((drule spec)+, erule impE, assumption, erule conjE) 
apply (simp add: path_balanced.Empty stack_traceable.Nonempty)

apply (case_tac "\<pi>' = \<pi> ;; `x", auto)
  using stack_traceable_preserved_over_seq_extension apply blast

apply (case_tac "\<pi>' = \<pi> ;; .x", auto)
using Empty_Local path_balanced.Empty apply blast
apply (case_tac "\<pi>' = \<pi> ;; `x", auto)
  using stack_traceable_preserved_over_seq_extension apply blast


apply (case_tac "\<pi>' = \<pi>\<^sub>r ;; `x\<^sub>r", auto)
  apply (simp add: stack_traceable_preserved_over_seq_extension)

apply (case_tac "\<pi>' = \<pi>\<^sub>s ;; `x\<^sub>s", auto)
  using stack_traceable_preserved_over_seq_extension apply blast

  using stack_traceable_preserved_over_seq_extension apply blast

done

lemma isnt_traceable_sound': "
  \<lbrakk>
    star_left op \<rightarrow> \<E>\<^sub>0 \<E>
  \<rbrakk> \<Longrightarrow>
  \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
  (\<forall> \<pi> e \<rho> \<kappa> . \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> (
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>
  ))
"
 apply (erule star_left.induct; auto)
  apply (simp add: Start)
  using path_balanced.Empty stack_traceable.Empty apply blast
  apply (rename_tac \<E> \<E>' \<pi> e \<rho> \<kappa>)
  apply (drule star_left_implies_star)
  apply (drule accept_preserved_under_concur_step_star, blast)
  apply (drule traceable_exp_preserved, auto)
 apply (rename_tac \<E> \<E>' \<pi> e \<rho> \<kappa>)
 apply (drule star_left_implies_star)
 apply (drule accept_preserved_under_concur_step_star, blast)
 apply (drule traceable_stack_preserved, auto)
done


lemma isnt_traceable_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>0;
    [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>;
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) 
  \<rbrakk> \<Longrightarrow>
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e
"
 apply (drule star_implies_star_left)
using isnt_traceable_sound' lift_accept_exp_to_pool by blast

end
