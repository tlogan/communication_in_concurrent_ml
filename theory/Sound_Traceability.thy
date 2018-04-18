theory Sound_Traceability
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Static_Traceability
    "~~/src/HOL/Library/List"
begin


inductive stack_static_traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> control_path \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<tturnstile> _ \<down> _ \<mapsto> _" [56,0,0,56]55)  where
  Empty: "
    \<lbrakk> 
      balanced \<pi>
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e \<down> \<pi> \<mapsto> []
  " |
  Empty_Local: "
    \<lbrakk> 
      balanced \<pi>\<^sub>2
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LSpawn x) # \<pi>\<^sub>2 \<mapsto> []
  " |
  Nonempty: "
    \<lbrakk> 
      balanced \<pi>\<^sub>2;
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>;
      \<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> \<kappa>
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2 \<mapsto> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>
  "

lemma singleton_eq_empty_surround: "
  [l] = ([] @ l # [])
"
by simp

lemma stack_static_traceable_preserved_over_balanced_extension:
  "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow> 
  balanced \<pi>' \<Longrightarrow> 
  \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" 
proof -
  assume "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>" "balanced \<pi>'" then 
  show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>"
  proof (cases rule: stack_static_traceable.cases)
    case Empty assume "\<kappa> = []" "balanced \<pi>"
    
    from `balanced \<pi>` `balanced \<pi>'`
    have "balanced (\<pi> @ \<pi>')" by (simp add: Append) then
    have "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> []" by (simp add: stack_static_traceable.Empty)
    with `\<kappa> = []`
    show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" by blast
  next
    case (Empty_Local \<pi>\<^sub>2 \<pi>\<^sub>1 x) assume "\<pi> = \<pi>\<^sub>1 @ (LSpawn x) # \<pi>\<^sub>2" "\<kappa> = []" "balanced \<pi>\<^sub>2"
    from `balanced \<pi>\<^sub>2` `balanced \<pi>'` 
    have "balanced (\<pi>\<^sub>2 @ \<pi>')" by (simp add: Append) then
    have "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LSpawn x) # \<pi>\<^sub>2 @ \<pi>' \<mapsto> []" by (simp add: stack_static_traceable.Empty_Local)
    with `\<pi> = \<pi>\<^sub>1 @ (LSpawn x) # \<pi>\<^sub>2` `\<kappa> = []` 
    show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" by simp
  next
    case (Nonempty \<pi>\<^sub>2 \<pi>\<^sub>1 x\<^sub>\<kappa> b e\<^sub>\<kappa> \<kappa>' \<rho>\<^sub>\<kappa>) 
    assume 
      "\<pi> = \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2" "\<kappa> = \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>'" 
      "balanced \<pi>\<^sub>2" "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>" "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> \<kappa>'"

    from `balanced \<pi>\<^sub>2` `balanced \<pi>'`
    have "balanced (\<pi>\<^sub>2 @ \<pi>')" by (simp add: Append)
    with `\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>` `\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> \<kappa>'`
    have "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2 @ \<pi>' \<mapsto> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>'" by (auto simp: stack_static_traceable.Nonempty)
    with `\<pi> = \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2` `\<kappa> = \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>'`
    show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" by simp
  qed
qed


lemma stack_static_traceable_preserved_over_seq_extension:"
  \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> \<kappa>
"
by (simp add: balanced.Next stack_static_traceable_preserved_over_balanced_extension)

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" ("_ \<preceq>\<^sub>e _" [56,56]55) where
  Refl : "
    e \<preceq>\<^sub>e e
  " | 
  Let: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = b in e\<^sub>n)
  " | 
  Let_Spawn_Child: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>c
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = SPAWN e\<^sub>c in e\<^sub>n)
  " |
  Let_Case_Left: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>l
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " | 
  Let_Case_Right: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>r
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " |
  Let_Abs_Body: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>b 
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)
  "

lemma static_traceable_exp_preserved_sync_recv_evt: "
\<lbrakk>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>);
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n;\<rho>\<^sub>r;\<kappa>'\<rangle>)
\<rbrakk> \<Longrightarrow> 
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> e\<^sub>n
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)"
  assume " \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n;\<rho>\<^sub>r;\<kappa>'\<rangle>)" then
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r \<mapsto> LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n" by simp
  have "(\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)) (\<pi>\<^sub>r ;; (LNext x\<^sub>r)) 
      = Some (\<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)" by simp
  with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)\<close>
  have "\<parallel>\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)\<parallel> \<sqsubseteq> \<V>" by (blast intro: static_eval_pool_to_precise)

  have "(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x\<^sub>r = Some \<omega>\<^sub>m" by simp
  with `\<parallel>\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)\<parallel> \<sqsubseteq> \<V>`
  have "|\<omega>\<^sub>m| \<in> \<V> x\<^sub>r" using abstracted_value_exists by blast
  with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r \<mapsto> LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n\<close> 
  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> e\<^sub>n" by (blast intro: static_traceable.Let_Sync)
qed


lemma static_traceable_exp_preserved_sync_send_evt: "
\<lbrakk>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e';\<rho>\<^sub>s;\<kappa>'\<rangle>);
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>);
  \<pi>\<^sub>s \<noteq> \<pi>\<^sub>r
\<rbrakk> \<Longrightarrow> 
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> e'
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)"
  and "\<pi>\<^sub>s \<noteq> \<pi>\<^sub>r"
  assume "\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e';\<rho>\<^sub>s;\<kappa>'\<rangle>)" then
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s \<mapsto> LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e'" by simp

  with `\<pi>\<^sub>s \<noteq> \<pi>\<^sub>r`
  have "(\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) (\<pi>\<^sub>s ;; (LNext x\<^sub>s)) 
      = Some (\<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>'\<rangle>)" by simp
  with `\<pi>\<^sub>s \<noteq> \<pi>\<^sub>r` \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)\<close>
  have "\<parallel>\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)\<parallel> \<sqsubseteq> \<V>" using static_eval_pool_to_precise by blast

  have "(\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)) x\<^sub>s = Some \<lbrace>\<rbrace>" by simp
  with `\<parallel>\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)\<parallel> \<sqsubseteq> \<V>`
  have " |\<lbrace>\<rbrace>| \<in> \<V> x\<^sub>s" using abstracted_value_exists by fastforce

  from \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s \<mapsto> LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e'\<close> \<open>|\<lbrace>\<rbrace>| \<in> \<V> x\<^sub>s\<close>
  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> e'" using static_traceable.Let_Sync by blast

qed

lemma static_traceable_exp_preserved_under_seq_step_down: "
  (\<E>(\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>')) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  (\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>
  ) \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
proof -
  assume "(\<E>(\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>')) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"
  assume 
    "(\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>
    )"
  and "\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'"

  assume "\<E> \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)"
  with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close>
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> RESULT x" "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" by simp+

  from `\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>`
  obtain b \<pi>\<^sub>1 \<pi>\<^sub>2 
  where "\<pi> = \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2" 
  and "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>"
  and "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> \<kappa>" and "balanced \<pi>\<^sub>2"
  by (blast intro: stack_static_traceable.cases)

  from `\<pi> = \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2` and `\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> RESULT x`
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2 \<mapsto> RESULT x" by simp

  from `\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'`
  obtain \<omega> where "\<rho> x = Some \<omega>" and "\<sigma>' = \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>"
  by (blast intro: seq_step.cases)
 
  from `\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2 \<mapsto> RESULT x` 
  and `\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>`
  and `balanced \<pi>\<^sub>2`
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # (\<pi>\<^sub>2 ;; (LReturn x\<^sub>\<kappa>)) \<mapsto> e\<^sub>\<kappa>" by (blast intro: static_traceable.Result)

  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'"
  proof cases
    assume "\<pi>' = \<pi> ;; (LReturn x\<^sub>\<kappa>)"
    with \<open>(\<E>(\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>')) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
    have "\<sigma>' = \<langle>e';\<rho>';\<kappa>'\<rangle>" by simp
    with \<open>\<sigma>' = \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>\<close>
    have "e' = e\<^sub>\<kappa>" by simp

    from `\<pi>' = \<pi> ;; (LReturn x\<^sub>\<kappa>)`
    and `\<pi> = \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # \<pi>\<^sub>2`
    and `e' = e\<^sub>\<kappa>`
    and \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ (LCall x\<^sub>\<kappa>) # (\<pi>\<^sub>2 ;; (LReturn x\<^sub>\<kappa>)) \<mapsto> e\<^sub>\<kappa>\<close> 
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by simp
  next
    assume "\<pi>' \<noteq> \<pi> ;; (LReturn x\<^sub>\<kappa>)"
    with \<open>(\<E>(\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>')) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
    have "\<E> \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by simp
    with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by simp
  qed
qed

lemma static_traceable_exp_preserved_under_seq_step: "
  \<E> \<rightarrow> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>) \<Longrightarrow>
  (\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<kappa>\<rangle> \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
proof -
  assume "(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"
  assume "\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>"
  and "\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<kappa>\<rangle>"
  assume "\<E> \<rightarrow> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)" by (blast intro: static_eval_preserved_under_concur_step)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)\<close> and \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
  have "\<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>" by (blast intro: static_eval_pool_to_precise)

  assume "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)"
  with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close>
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e" "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>" by simp+

  from `\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<kappa>\<rangle>`
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''"
  proof cases
    case Let_Unit
    assume "b = \<lparr>\<rparr>" and "e'' = e"
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<close> 
    have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = \<lparr>\<rparr> in e''" by simp then
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by (simp add: static_traceable.Let_Unit)
  next
    case (Let_Prim p)
    assume "b = Prim p" and "e'' = e"
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<close>
    have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = Prim p in e''" by simp then
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by (simp add: static_traceable.Let_Prim)
  next
    case (Let_Fst x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p \<omega>)
    assume "\<rho>'' = \<rho> ++ [x \<mapsto> \<omega>]"
    assume "b = FST x\<^sub>p" and "e'' = e"
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<close>
    have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST x\<^sub>p in e''" by simp 
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)\<close>
    and `\<rho>'' = \<rho> ++ [x \<mapsto> \<omega>]`
    have "\<parallel>\<rho> ++ [x \<mapsto> \<omega>]\<parallel> \<sqsubseteq> \<V>" using values_not_bound_pool_sound by fastforce then
    have "{|\<omega>|} \<subseteq> \<V> x" using abstracted_value_exists by auto
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST x\<^sub>p in e''\<close> \<open>{|\<omega>|} \<subseteq> \<V> x\<close> 
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by (blast intro: static_traceable.Let_Fst)
  next
    case (Let_Snd x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p \<omega>)
    assume "\<rho>'' = \<rho> ++ [x \<mapsto> \<omega>]"
    assume "b = SND x\<^sub>p" and "e'' = e"
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<close>
    have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SND x\<^sub>p in e''" by simp 
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)\<close>
    and `\<rho>'' = \<rho> ++ [x \<mapsto> \<omega>]`
    have "\<parallel>\<rho> ++ [x \<mapsto> \<omega>]\<parallel> \<sqsubseteq> \<V>" using values_not_bound_pool_sound by fastforce then
    have "{|\<omega>|} \<subseteq> \<V> x" using abstracted_value_exists by auto
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SND x\<^sub>p in e''\<close> \<open>{|\<omega>|} \<subseteq> \<V> x\<close> 
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by (blast intro: static_traceable.Let_Snd)
  next
    case (Let_Case_Left x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)
    from `\<kappa> = \<langle>x,e,\<rho>\<rangle> # \<kappa>`
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by auto
  next
    case (Let_Case_Right x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)
    from `\<kappa> = \<langle>x,e,\<rho>\<rangle> # \<kappa>`
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by auto
  next
    case (Let_App f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a)
    from `\<kappa> = \<langle>x,e,\<rho>\<rangle> # \<kappa>`
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by auto
  qed

  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'"
  proof cases
    assume "\<pi>' = \<pi> ;; (LNext x)"
    with \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> 
    have "\<langle>e'';\<rho>'';\<kappa>\<rangle> = \<langle>e';\<rho>';\<kappa>'\<rangle>" by simp then
    have "e'' = e'" by simp
    from \<open>\<pi>' = \<pi> ;; (LNext x)\<close> and \<open>e'' = e'\<close> and \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''\<close>
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by auto
  next
    assume "\<pi>' \<noteq> \<pi> ;; (LNext x)"
    with \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
    have "\<E> \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by simp
    with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by simp
  qed
qed


lemma static_traceable_exp_preserved_under_seq_step_up: "
  \<E> \<rightarrow> \<E>(\<pi> ;; (LCall x) \<mapsto> \<langle>e'a;\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>) \<Longrightarrow>
  (\<E>(\<pi> ;; (LCall x) \<mapsto> \<langle>e'a;\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e'a;\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
  apply (case_tac "\<pi>' = \<pi> ;; (LCall x)"; auto)
  apply ((drule spec)+, erule impE, assumption, erule conjE)
  apply (drule static_eval_pool_to_precise, auto)
  apply (erule seq_step.cases, auto)
  apply (drule abstracted_value_exists, simp+, rule static_traceable.Let_Case_Left; auto)
  apply (drule abstracted_value_exists, simp+, rule static_traceable.Let_Case_Right; auto)
  apply (drule abstracted_value_exists, simp+, rule static_traceable.Let_App; auto)
done

lemma static_traceable_exp_preserved_under_chan:"
  (\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>);\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
  apply (smt map_upd_Some_unfold state.inject static_traceable.Let_Chan)
done

lemma static_traceable_exp_preserved_under_spawn: "
  (\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
  apply (smt map_upd_Some_unfold state.inject static_traceable.Let_Spawn static_traceable.Let_Spawn_Child)
done
 
lemma static_traceable_exp_preserved_under_sync: "
  \<E> \<rightarrow> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  (\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
  apply (case_tac "\<pi>' = \<pi>\<^sub>r ;; (LNext x\<^sub>r)", auto)
  apply (drule static_eval_preserved_under_concur_step, auto)
  apply (meson static_traceable_exp_preserved_sync_recv_evt)
  apply (case_tac "\<pi>' = \<pi>\<^sub>s ;; (LNext x\<^sub>s)")
  apply (drule static_eval_preserved_under_concur_step; auto)
  apply (meson static_traceable_exp_preserved_sync_send_evt)
  apply (smt exp.inject(1) option.inject state.inject static_traceable_exp_preserved_sync_send_evt)
  apply simp
done


lemma static_traceable_exp_preserved: "
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
proof -
  assume "\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"
  and "\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>"
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"

  assume "\<E> \<rightarrow> \<E>'" then

  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<sigma>')

    assume "\<E>' = \<E> ++ [\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>']"
    and "\<E> \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)"
    and "\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'"

    from `\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)` and `\<E>' = \<E> ++ [\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>']`

    have "(\<E>(\<pi> ;; (LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>')) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto
    with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>\<E> \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)\<close>
    and \<open>\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (blast intro: static_traceable_exp_preserved_under_seq_step_down)
  next
    case (Seq_Step \<pi> x b e \<rho> \<kappa>'' e'' \<rho>'')

    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>]"
    and "leaf \<E> \<pi>"
    and "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>''\<rangle>)"
    and "\<langle>LET x = b in e;\<rho>;\<kappa>''\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<kappa>''\<rangle>"

    from `\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)` and \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>]\<close>
    have "(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto

    from `\<E> \<rightarrow> \<E>'` and \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>]\<close>
    have "\<E> \<rightarrow> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>)" by auto

    from  \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
    and \<open>\<E> \<rightarrow> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>)\<close> \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e'';\<rho>'';\<kappa>''\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
    and \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>''\<rangle>)\<close>
    and \<open>\<langle>LET x = b in e;\<rho>;\<kappa>''\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<kappa>''\<rangle>\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_seq_step)
  next
    case (Seq_Step_Up \<pi> x b e \<rho> \<kappa> e'' \<rho>'')

    assume "\<E>' = \<E> ++ [\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]"
    and "leaf \<E> \<pi>"
    and "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)"
    and "\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>"

    from \<open>\<E> \<rightarrow> \<E>'\<close> and \<open>\<E>' = \<E> ++ [\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]\<close>
    have \<open>\<E> \<rightarrow> \<E>(\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)\<close> by auto

    from \<open>\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> and \<open>\<E>' = \<E> ++ [\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]\<close>
    have \<open>(\<E>(\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> by auto

    from \<open>\<E> \<rightarrow> \<E>(\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)\<close>
    and \<open>(\<E>(\<pi> ;; (LCall x) \<mapsto> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
    and \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    and \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close>
    and \<open>\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)\<close>
    and \<open>\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e'';\<rho>'';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_seq_step_up)
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)

    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>];\<kappa>\<rangle>]"
    and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)"

    from \<open>\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> 
    and \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>];\<kappa>\<rangle>]\<close>

    have \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>];\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> by auto
    with  \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_chan)
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]"
    and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)"

    from \<open>\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> and \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]\<close>

    have \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> by auto
    with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_spawn)
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    assume "\<E>' = \<E> ++ [\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]"
    and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
    and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"

    from \<open>\<E> \<rightarrow> \<E>'\<close> `\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)` and `\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)`
    and \<open>\<E>' = \<E> ++ [\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]\<close>

    have "\<E> \<rightarrow> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>)"
    and "(\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto+
    with  \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
    and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
    and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_sync)
  qed
qed


lemma static_traceable_stack_preserved: "
\<lbrakk>
  \<E> \<rightarrow> \<E>';
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>;
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> 
\<rbrakk> \<Longrightarrow>
\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> \<kappa>'
"
apply (frule concur_step.cases, auto)

apply (case_tac "\<pi>' = \<pi> ;; (LReturn x\<^sub>\<kappa>)", auto)
apply ((drule spec)+, erule impE, assumption, erule conjE)
apply (erule seq_step.cases; auto)
apply (erule stack_static_traceable.cases; auto)
  using balanced.CallReturn stack_static_traceable_preserved_over_balanced_extension apply blast

apply (case_tac "\<pi>' = \<pi> ;; (LNext x)", auto)
  using stack_static_traceable_preserved_over_seq_extension apply blast

apply (case_tac "\<pi>' = \<pi> ;; (LCall x)", auto)
apply ((drule spec)+, erule impE, assumption, erule conjE) 
apply (simp add: balanced.Empty stack_static_traceable.Nonempty)

apply (case_tac "\<pi>' = \<pi> ;; (LNext x)", auto)
  using stack_static_traceable_preserved_over_seq_extension apply blast

apply (case_tac "\<pi>' = \<pi> ;; (LSpawn x)", auto)
using Empty_Local balanced.Empty apply blast
apply (case_tac "\<pi>' = \<pi> ;; (LNext x)", auto)
  using stack_static_traceable_preserved_over_seq_extension apply blast


apply (case_tac "\<pi>' = \<pi>\<^sub>r ;; (LNext x\<^sub>r)", auto)
  apply (simp add: stack_static_traceable_preserved_over_seq_extension)

apply (case_tac "\<pi>' = \<pi>\<^sub>s ;; (LNext x\<^sub>s)", auto)
  using stack_static_traceable_preserved_over_seq_extension apply blast

  using stack_static_traceable_preserved_over_seq_extension apply blast

done

lemma isnt_static_traceable_sound': "
  \<lbrakk>
    \<E>\<^sub>0 \<rightarrow>* \<E>
  \<rbrakk> \<Longrightarrow>
  \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
  (\<forall> \<pi> e \<rho> \<kappa> . \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> (
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>
  ))
"
 apply (drule star_implies_star_left)
 apply (erule star_left.induct; auto)
  apply (simp add: Start)
  using balanced.Empty stack_static_traceable.Empty apply blast
  apply (rename_tac \<E> \<E>' \<pi> e \<rho> \<kappa>)
  apply (drule star_left_implies_star)
  apply (drule static_eval_preserved_under_concur_step_star, blast)
  apply (drule static_traceable_exp_preserved, auto)
 apply (rename_tac \<E> \<E>' \<pi> e \<rho> \<kappa>)
 apply (drule star_left_implies_star)
 apply (drule static_eval_preserved_under_concur_step_star, blast)
 apply (drule static_traceable_stack_preserved, auto)
done


lemma isnt_static_traceable_sound: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>0;
    [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>;
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) 
  \<rbrakk> \<Longrightarrow>
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>0" and "[[] \<mapsto> \<langle>e\<^sub>0; empty; []\<rangle>] \<rightarrow>* \<E>"
  and "\<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>0`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e\<^sub>0; empty; []\<rangle>]" by (simp add: static_eval_to_pool)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]\<close> \<open>\<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>)\<close> \<open>[[] \<mapsto> \<langle>e\<^sub>0; empty; []\<rangle>] \<rightarrow>* \<E>\<close>
  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e" using isnt_static_traceable_sound' by blast
qed

  
end