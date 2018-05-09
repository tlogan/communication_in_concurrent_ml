theory Z_Scraps
  imports Main
begin

inductive test1 :: "int \<Rightarrow> bool" where
  "test1 2"

fun foo1 :: "int \<Rightarrow> int" where
  "foo1 i = (if (test1 i) then 2 else 3)"

value "foo1 2"

fun test2 :: "int \<Rightarrow> bool" where
  "test2 i = (i = 2)"

fun foo2 :: "int \<Rightarrow> int" where
  "foo2 i = (if (test2 i) then 2 else 3)"

value "foo2 2"


(*

*)

(*


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

lemma static_traceable_exp_preserved_sync_recv_evt: "
\<lbrakk>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>);
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n;\<rho>\<^sub>r;\<kappa>'\<rangle>)
\<rbrakk> \<Longrightarrow> 
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> e\<^sub>n
"
proof -

  have "(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x\<^sub>r = Some \<omega>\<^sub>m" by simp

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)"
  assume " \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n;\<rho>\<^sub>r;\<kappa>'\<rangle>)" then
  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r \<mapsto> LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n" by simp
  have "(\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)) (\<pi>\<^sub>r ;; (LNext x\<^sub>r)) 
      = Some (\<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)" by simp
  with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e';\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>'\<rangle>)\<close>
  and `(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x\<^sub>r = Some \<omega>\<^sub>m`

  have "{ | \<omega>\<^sub>m | } \<subseteq> \<V> x\<^sub>r"  using static_eval_pool_to_precise by blast
  with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r \<mapsto> LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>n\<close> 

  show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> e\<^sub>n" by (blast intro: static_traceable.Let_Sync)
qed


lemma static_traceable_exp_preserved_sync_send_evt: "
\<lbrakk>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e';\<rho>\<^sub>s;\<kappa>'\<rangle>);
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>);
  \<pi>\<^sub>s \<noteq> \<pi>\<^sub>r
\<rbrakk> \<Longrightarrow> 
\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> e'
"
proof -
  have "(\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)) x\<^sub>s = Some VUnit" by simp

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)"
  and "\<pi>\<^sub>s \<noteq> \<pi>\<^sub>r"

  assume "\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e';\<rho>\<^sub>s;\<kappa>'\<rangle>)" then

  have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s \<mapsto> LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e'" by simp
  with `\<pi>\<^sub>s \<noteq> \<pi>\<^sub>r`

  have "(\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) (\<pi>\<^sub>s ;; (LNext x\<^sub>s)) 
      = Some (\<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>'\<rangle>)" by simp
  with `\<pi>\<^sub>s \<noteq> \<pi>\<^sub>r` \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e';\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>'\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)\<close>
  and `(\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)) x\<^sub>s = Some VUnit`
  have  "|VUnit| \<in> \<V> x\<^sub>s" using static_eval_pool_to_precise by blast

  from \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>s \<mapsto> LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e'\<close> \<open>|VUnit| \<in> \<V> x\<^sub>s\<close>
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
    assume "\<rho>'' = \<rho> ++ [x \<mapsto> \<omega>]" then
    have "\<rho>'' x = Some \<omega>" by simp

    assume "b = FST x\<^sub>p" and "e'' = e"
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<close>

    have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST x\<^sub>p in e''" by simp 

    from \<open>\<E> \<rightarrow> \<E>(\<pi> ;; LNext x \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)\<close>
    have "\<E> \<rightarrow>* \<E>(\<pi> ;; LNext x \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)" by simp

    from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
    and \<open>\<E> \<rightarrow>* \<E>(\<pi> ;; LNext x \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)\<close>
    and \<open>\<rho>'' x = Some \<omega>\<close> 

    have "{|\<omega>|} \<subseteq> \<V> x" by (meson fun_upd_same values_not_bound_pool_sound)
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST x\<^sub>p in e''\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; (LNext x) \<mapsto> e''" by (blast intro: static_traceable.Let_Fst)
  next
    case (Let_Snd x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p \<omega>)
    assume "\<rho>'' = \<rho> ++ [x \<mapsto> \<omega>]" then
    have "\<rho>'' x = Some \<omega>" by simp

    assume "b = SND x\<^sub>p" and "e'' = e"
    with \<open>\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<close>
    have "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SND x\<^sub>p in e''" by simp 

    from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
    and \<open>\<E> \<rightarrow> \<E>(\<pi> ;; LNext x \<mapsto> \<langle>e'';\<rho>'';\<kappa>\<rangle>)\<close> 
    and `\<rho>'' x = Some \<omega>`
    have "{|\<omega>|} \<subseteq> \<V> x" by (metis fun_upd_same star_step1 values_not_bound_pool_sound)
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
  apply (erule seq_step.cases, auto)
  apply (simp add: static_traceable.Let_Case_Left)
  apply (simp add: static_traceable.Let_Case_Right)
  apply (drule static_eval_pool_to_precise, auto)
    using static_traceable.Let_App apply blast
done

lemma static_traceable_exp_preserved_under_chan:"
  (\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChan (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
  apply (smt map_upd_Some_unfold state.inject static_traceable.Let_Chan)
done

lemma static_traceable_exp_preserved_under_spawn: "
  (\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnit);\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow> 
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'
"
  apply (smt map_upd_Some_unfold state.inject static_traceable.Let_Spawn static_traceable.Let_Spawn_Child)
done
 
lemma static_traceable_exp_preserved_under_sync: "
  \<E> \<rightarrow> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  (\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
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

    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))];\<kappa>\<rangle>]"
    and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)"

    from \<open>\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> 
    and \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))];\<kappa>\<rangle>]\<close>

    have \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))];\<kappa>\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> by auto
    with  \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_chan)
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]"
    and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)"

    from \<open>\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> and \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]\<close>

    have \<open>(\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> by auto
    with \<open>\<forall>\<pi> e \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<and> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>\<close> 
    and \<open>\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)\<close>

    show "\<V> \<turnstile> e\<^sub>0 \<down> \<pi>' \<mapsto> e'" by (auto simp: static_traceable_exp_preserved_under_spawn)
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    assume "\<E>' = \<E> ++ [\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]"
    and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
    and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"

    from \<open>\<E> \<rightarrow> \<E>'\<close> `\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)` and `\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)`
    and \<open>\<E>' = \<E> ++ [\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]\<close>

    have "\<E> \<rightarrow> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>)"
    and "(\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>)) \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto+
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


*)



(*

type_synonym flow_set = "(exp \<times> control_label \<times> exp) set"
(* this a nice order for the rules; update other definitions to use same order*)
inductive flow :: "(abstract_value_env \<times> flow_set) \<Rightarrow> exp \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  Result: "
    (\<V>, \<F>) \<TTurnstile> RESULT x
  " |
  Let_Unit: "
    \<lbrakk>
      {(LET x = \<lparr>\<rparr> in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = \<lparr>\<rparr> in e
  " |
  Let_Chan: "
    \<lbrakk>
      {(LET x = CHAN \<lparr>\<rparr> in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(LET x = SEND EVT x\<^sub>c x\<^sub>m  in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(LET x = RECV EVT x\<^sub>c  in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Pair: "
    \<lbrakk>
      {(LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left: "
    \<lbrakk>
      {(LET x = LEFT x\<^sub>p in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = LEFT x\<^sub>p in e
  " |
  Let_Right: "
    \<lbrakk>
      {(LET x = RIGHT x\<^sub>p in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = RIGHT x\<^sub>p in e
  " |
  Let_Abs: "
    \<lbrakk>
      {(LET x = FN f x\<^sub>p . e\<^sub>b  in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>b;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = FN f x\<^sub>p . e\<^sub>b  in e
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (LET x = SPAWN e\<^sub>c  in e, (LNext x), e),
        (LET x = SPAWN e\<^sub>c  in e, (LSpawn x), e\<^sub>c)
      } \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>c;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SPAWN e\<^sub>c in e
  " |
  Let_Sync: "
    \<lbrakk>
      {(LET x = SYNC x\<^sub>e in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SYNC x\<^sub>e in e
  " |
  Let_Fst: "
    \<lbrakk>
      {(LET x = FST x\<^sub>p in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk>
      {(LET x = FST x\<^sub>p in e, (LNext x), e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SND x\<^sub>p in e
  " |
  Let_Case: "
    \<lbrakk>
      {
        (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e, (LCall x), e\<^sub>l),
        (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e, (LCall x), e\<^sub>r),
        (RESULT \<lfloor>e\<^sub>l\<rfloor>, (LReturn x), e),
        (RESULT \<lfloor>e\<^sub>r\<rfloor>, (LReturn x), e)
      } \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>l;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>r;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  "|
  Let_App: "
    \<lbrakk>

      \<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow>
      {
        (LET x = APP f x\<^sub>a in e, (LCall x), e\<^sub>b),
        (RESULT \<lfloor>e\<^sub>b\<rfloor>, (LReturn x), e)
      } \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = APP f x\<^sub>a in e
  "


inductive life_in_exp :: "exp_map \<Rightarrow> exp => bool" where
  Base: "
    \<lbrakk>
      \<L>n e \<noteq> Set.empty
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n e
  " |
  Abs: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>b \<or>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)
  " |
  Spawn: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>c \<or>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = SPAWN e\<^sub>c in e\<^sub>n)
  " |
  Case: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>l \<or>
      life_in_exp \<L>n e\<^sub>r \<or>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " |
  Let: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = b in e\<^sub>n)
  "
  
fun trim :: "exp_map \<Rightarrow> exp \<Rightarrow> exp" where
  "trim \<L>n (RESULT y) = (RESULT y)" |

  "trim \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)) then
       (LET x = FN f x\<^sub>p . trim \<L>n e\<^sub>b in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " |

  "trim \<L>n (LET x = SPAWN e\<^sub>c in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = SPAWN e\<^sub>c in e\<^sub>n)) then
       (LET x = SPAWN trim \<L>n e\<^sub>c in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " |

  "trim \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)) then
       (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> trim \<L>n e\<^sub>l RIGHT x\<^sub>r |> trim \<L>n e\<^sub>r in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " |

  "trim \<L>n (LET x = b in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = b in e\<^sub>n)) then
       (LET x = b in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " 




(*
lemma trim_equal_sound: "
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

theorem one_shot_strong_sound: "
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
by (metis isnt_send_path_sound runtime_send_paths_are_inclusive trim_equal_sound)







lemma traceable_result_implies_traceable_case: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ \<upharpoonleft>x # \<pi>' \<mapsto> RESULT y; \<downharpoonright>\<pi>'\<upharpoonleft>;
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<^sub>n
  \<rbrakk> \<Longrightarrow>
  b = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r \<and> (y = \<lfloor>e\<^sub>l\<rfloor> \<or> y = \<lfloor>e\<^sub>r\<rfloor>)
"
sorry

lemma traceable_result_implies_traceable_app: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ \<upharpoonleft>x # \<pi>' \<mapsto> RESULT y; \<downharpoonright>\<pi>'\<upharpoonleft>;
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<^sub>n
  \<rbrakk> \<Longrightarrow>
  b = APP f x\<^sub>a \<and> y \<in> {\<lfloor>e\<^sub>b\<rfloor> |  f' x\<^sub>p . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f} (*not sure which function is bound to f; do I need unique names for f in labels?*)
"
sorry


(* abstract representation of paths *)
datatype abstract_path =
  Empty |
  Atom control_label ("&_" [66]66) |
  Union abstract_path abstract_path (infix ":|:" 64) |
  Star abstract_path ("{_}*" [0]66) |
  Concat abstract_path abstract_path (infixr ":@:" 65)


inductive ap_matches :: "abstract_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "|\<rhd>" 55) where
 Empty: "
   Empty |\<rhd> []
 " |
 Atom: "
   &l |\<rhd> [l]
 " |
 Union_Left: "
   \<lbrakk>
     p\<^sub>a |\<rhd> \<pi>
   \<rbrakk> \<Longrightarrow>
   p\<^sub>a :|: p\<^sub>b |\<rhd> \<pi>
 " | 
 Union_Right: "
   \<lbrakk>
     p\<^sub>b |\<rhd> \<pi>
   \<rbrakk> \<Longrightarrow>
   p\<^sub>a :|: p\<^sub>b |\<rhd> \<pi>
 " | 
 Star_Empty: "
   {p}* |\<rhd> []
 " |
 Star: "
   \<lbrakk>
     p |\<rhd> \<pi>;
     {p}* |\<rhd> \<pi>'
   \<rbrakk> \<Longrightarrow>
   {p}* |\<rhd> \<pi> @ \<pi>'
 " |
 Concat: "
   \<lbrakk>
     p\<^sub>a |\<rhd> \<pi>\<^sub>a;
     p\<^sub>b |\<rhd> \<pi>\<^sub>b
   \<rbrakk> \<Longrightarrow>
   p\<^sub>a :@: p\<^sub>b |\<rhd> \<pi>\<^sub>a @ \<pi>\<^sub>b
 " 

inductive ap_single :: "abstract_path \<Rightarrow> bool" where
 Empty: "
   ap_single Empty
 " |
 Atom: "
   ap_single (&l)
 " |
 Concat: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_single p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_single (p\<^sub>a :@: p\<^sub>b)
 "

inductive ap_ordered :: "abstract_path \<Rightarrow> bool" where
 Single: "
   ap_single ap \<Longrightarrow> ap_ordered ap
 " |
 Star: "
   \<lbrakk>
     ap_single p
   \<rbrakk> \<Longrightarrow>
   ap_ordered ({p}*)
 " |
 Concat: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_ordered p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_ordered (p\<^sub>a :@: p\<^sub>b)
 " |
 Union_Right: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_ordered p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_ordered (p\<^sub>a :@: (Empty :|: p\<^sub>b))
 " |
 Union_Left: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_ordered p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_ordered (p\<^sub>a :@: (p\<^sub>b :|: Empty))
 "

inductive ap_inclusive :: "abstract_path \<Rightarrow> bool" where
 Ordered: "
   \<lbrakk>
     ap_ordered ap 
   \<rbrakk> \<Longrightarrow> 
   ap_inclusive ap
 " | 
 Spawn_Left: "
   \<lbrakk>
     ap_single ap 
   \<rbrakk> \<Longrightarrow> 
   ap_inclusive (ap :@: (&.x :@: ap\<^sub>1) :|: (&`x :@: ap\<^sub>2))
 " | 
 Spawn_Right: "
   \<lbrakk>
     ap_single ap 
   \<rbrakk> \<Longrightarrow> 
   ap_inclusive (ap :@: (&`x :@: ap\<^sub>1) :|: (&.x :@: ap\<^sub>2))
 "

definition ap_noncompetitive :: "abstract_path \<Rightarrow> bool" where 
  "ap_noncompetitive ap = (ap_ordered ap \<or> \<not> ap_inclusive ap)"

lemma atom_matches_implies: "
 &l |\<rhd> \<pi> \<Longrightarrow> [l] = \<pi>
"
 apply (erule ap_matches.cases; auto)
done

lemma union_matches_implies: "
  p\<^sub>a :|: p\<^sub>b |\<rhd> \<pi> \<Longrightarrow> p\<^sub>a |\<rhd> \<pi> \<or> p\<^sub>b |\<rhd> \<pi>
"
 apply (erule ap_matches.cases; auto)
done

lemma concat_matches_implies: "
  p\<^sub>a :@: p\<^sub>b |\<rhd> \<pi> \<Longrightarrow> \<exists> \<pi>\<^sub>a \<pi>\<^sub>b . \<pi> = \<pi>\<^sub>a @ \<pi>\<^sub>b \<and> p\<^sub>a |\<rhd> \<pi>\<^sub>a \<and> p\<^sub>b |\<rhd> \<pi>\<^sub>b
"
 apply (erule ap_matches.cases; auto)
done


lemma ap_noncompetitive_implies_noncompetitive': "
  ap |\<rhd> \<pi>\<^sub>1 \<Longrightarrow>
  (\<forall> \<pi>\<^sub>2 .
    ap |\<rhd> \<pi>\<^sub>2 \<longrightarrow>
    ap_noncompetitive ap \<longrightarrow>
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
 )
"
 apply (simp add: ap_noncompetitive_def noncompetitive_def)
 apply (erule ap_matches.induct; auto)
  apply (simp add: atom_matches_implies)
  apply (simp add: atom_matches_implies)
  using ap_ordered.simps ap_single.simps apply blast

sorry



lemma ap_noncompetitive_implies_noncompetitive: "
  \<lbrakk>
    ap |\<rhd> \<pi>\<^sub>1;
    ap |\<rhd> \<pi>\<^sub>2;
    ap_noncompetitive ap
  \<rbrakk> \<Longrightarrow>
  noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
"
by (simp add: ap_noncompetitive_implies_noncompetitive')


lemma cons_eq_append: "
  [x] @ xs = x # xs
"
by simp

lemma concat_assoc[simp]: "
  (x :@: y) :@: z |\<rhd> \<pi> \<longleftrightarrow> x :@: (y :@: z) |\<rhd> \<pi>
"
  apply auto
   apply (erule ap_matches.cases; auto; erule ap_matches.cases; auto)
   apply (drule ap_matches.Concat[of y _ z], simp)
   apply (erule ap_matches.Concat, simp)
  apply (erule ap_matches.cases; auto; erule ap_matches.cases[of "y :@: z"]; auto)
  apply (drule ap_matches.Concat, simp)
  apply (drule ap_matches.Concat[of "x :@: y" _ "z"], auto)
done

lemma concat_star_implies_star': "
  ps |\<rhd> \<pi>\<^sub>a \<Longrightarrow> \<forall> p . ps = {p}* \<longrightarrow> p |\<rhd> \<pi>\<^sub>b \<longrightarrow> {p}* |\<rhd> \<pi>\<^sub>a @ \<pi>\<^sub>b
"
 apply (erule ap_matches.induct; auto)
  using Star_Empty ap_matches.Star apply fastforce
  apply (thin_tac "\<forall>pa. p = {pa}* \<longrightarrow> pa |\<rhd> \<pi>\<^sub>b \<longrightarrow> {pa}* |\<rhd> \<pi> @ \<pi>\<^sub>b")
  apply (drule ap_matches.Star; auto)
done

lemma concat_star_implies_star: "
 {p}* :@: p |\<rhd> \<pi> \<Longrightarrow> {p}* |\<rhd> \<pi>
"
 apply (erule ap_matches.cases; auto)
by (simp add: concat_star_implies_star')


abbreviation g100 where "g100 \<equiv> Var ''g100''"
abbreviation g101 where "g101 \<equiv> Var ''g101''"
abbreviation g102 where "g102 \<equiv> Var ''g102''"
abbreviation g103 where "g103 \<equiv> Var ''g103''"
abbreviation g104 where "g104 \<equiv> Var ''g104''"
abbreviation g105 where "g105 \<equiv> Var ''g105''"
abbreviation g106 where "g106 \<equiv> Var ''g106''"
abbreviation g107 where "g107 \<equiv> Var ''g107''"
abbreviation g108 where "g108 \<equiv> Var ''g108''"
abbreviation g109 where "g109 \<equiv> Var ''g109''"
abbreviation g110 where "g110 \<equiv> Var ''g110''"
abbreviation g111 where "g111 \<equiv> Var ''g111''"
abbreviation g112 where "g112 \<equiv> Var ''g112''"
abbreviation g113 where "g113 \<equiv> Var ''g113''"
abbreviation g114 where "g114 \<equiv> Var ''g114''"
abbreviation g115 where "g115 \<equiv> Var ''g115''"
abbreviation g116 where "g116 \<equiv> Var ''g116''"
abbreviation g117 where "g117 \<equiv> Var ''g117''"
abbreviation g118 where "g118 \<equiv> Var ''g118''"
abbreviation g119 where "g119 \<equiv> Var ''g119''"
abbreviation g120 where "g120 \<equiv> Var ''g120''"

(*
normalize (
  $LET ch = $CHAN \<lparr>\<rparr> in
  $LET u = $SPAWN (
    $APP ($FN f x .
      $LET u = $SYNC ($SEND EVT ($ch) ($x)) in  
      ($APP ($f) ($x))  
    ) $\<lparr>\<rparr>
  ) in
  $LET u = $SPAWN (
    $APP ($FN f x .
      $LET r = $SYNC ($RECV EVT ($ch)) in  
      ($APP ($f) ($x))  
    ) $\<lparr>\<rparr>
  ) in
  $\<lparr>\<rparr>
)"
*)

definition infinite_prog where
  "infinite_prog \<equiv> (
    LET g100 = CHAN \<lparr>\<rparr> in 
    LET g101 = SPAWN 
      LET g102 = FN g103 g104 . 
        LET g105 = SEND EVT g100 g104 in 
        LET g106 = SYNC g105 in 
        LET g107 = APP g103 g104 in 
        RESULT g107 
      in 
      LET g108 = \<lparr>\<rparr> in 
      LET g109 = APP g102 g108 in 
      RESULT g109 
    in 
    LET g110 = SPAWN 
      LET g111 = FN g112 g113 . 
        LET g114 = RECV EVT g100 in 
        LET g115 = SYNC g114 in 
        LET g116 = APP g112 g113 in 
        RESULT g116 
      in 
      LET g117 = \<lparr>\<rparr> in 
      LET g118 = APP g111 g117 in 
      RESULT g118 
    in 
    LET g119 = \<lparr>\<rparr> in 
    RESULT g119
  )"

definition infinite_prog_send_g100_abstract_path :: abstract_path where
  "infinite_prog_send_g100_abstract_path \<equiv> 
    &`g100 :@:
    &.g101 :@: &`g102 :@: &`g108 :@:
    &\<upharpoonleft>g109 :@: &`g105 :@: &`g106 :@: {&\<upharpoonleft>g107 :@: &`g105 :@: &`g106}*
  "

definition infinite_prog_recv_g100_abstract_path :: abstract_path where
  "infinite_prog_recv_g100_abstract_path \<equiv> 
    &`g100 :@: &`g101 :@:
    &.g110 :@: &`g111 :@: &`g117 :@: 
    &\<upharpoonleft>g118 :@: &`g114 :@: &`g115 :@: {&\<upharpoonleft>g116 :@: &`g114 :@: &`g115}*
  "

theorem infinite_prog_single_sender: "
   [[] \<mapsto> \<langle>infinite_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
   all_ordered (is_send_path \<E>' (Ch [] g100))
"
sorry


theorem infinite_prog_single_receiver: "
  [[] \<mapsto> \<langle>infinite_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<longrightarrow>
   all_ordered (is_recv_path \<E>' (Ch [] g100))
"
sorry

theorem "
  [[] \<mapsto> \<langle>infinite_prog; Map.empty;[]\<rangle>] \<rightarrow>* \<E>' 
  \<Longrightarrow>
  one_to_one \<E>' (Ch [] g100)
"
  apply (simp add: one_to_one_def, auto)
  using infinite_prog_single_sender apply blast
  using infinite_prog_single_receiver apply blast
done


definition infinite_prog_\<V> :: "abstract_value_env" where 
  "infinite_prog_\<V> \<equiv> (\<lambda> _ . {})(
    g100 := {^Chan g100}, 

    g101 := {^\<lparr>\<rparr>},
    g102 := {^(Abs g103 g104 (
      LET g105 = SEND EVT g100 g104 in 
      LET g106 = SYNC g105 in 
      LET g107 = APP g103 g104 in 
      RESULT g107 
    ))},
    g103 := {^(Abs g103 g104 (
      LET g105 = SEND EVT g100 g104 in 
      LET g106 = SYNC g105 in 
      LET g107 = APP g103 g104 in 
      RESULT g107
    ))}, g104 := {^\<lparr>\<rparr>},
    g105 := {^(Send_Evt g100 g104)},
    g106 := {^\<lparr>\<rparr>}, g107 := {},
    g108 := {^\<lparr>\<rparr>}, g109 := {},

    g110 := {^\<lparr>\<rparr>},
    g111 := {^(Abs g112 g113 (
              LET g114 = RECV EVT g100 in 
              LET g115 = SYNC g114 in 
              LET g116 = APP g112 g113 in 
              RESULT g116 
    ))},
    g112 := {^(Abs g112 g113 (
              LET g114 = RECV EVT g100 in 
              LET g115 = SYNC g114 in 
              LET g116 = APP g112 g113 in 
              RESULT g116 
    ))}, g113 := {^\<lparr>\<rparr>},
    g114 := {^(Recv_Evt g100)},
    g115 := {^\<lparr>\<rparr>}, g116 := {},
    g117 := {^\<lparr>\<rparr>}, g118 := {},

    g119 := {^\<lparr>\<rparr>}
  )"

definition infinite_prog_\<C> :: "abstract_value_env" where 
  "infinite_prog_\<C>  \<equiv> (\<lambda> _ . {})(
    g100 := {^\<lparr>\<rparr>}
  )"


theorem infinite_prog_has_intuitive_avf_analysis: "
  (infinite_prog_\<V>, infinite_prog_\<C>) \<Turnstile>\<^sub>e infinite_prog 
"
 apply (simp add: infinite_prog_\<V>_def infinite_prog_\<C>_def infinite_prog_def)
 apply (rule; simp?)+
done

lemma infinite_prog_\<V>_restricted: "
  (\<forall> x \<omega> . |\<omega>| \<in> infinite_prog_\<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e infinite_prog))
"
sorry

method elim_traceable_result uses dest = (
  (
    (frule traceable_implies_subexp, rule infinite_prog_\<V>_restricted),
    (simp add: infinite_prog_def; (erule subexp.cases; auto)+, fold infinite_prog_def),
    (rotate_tac -2),
    (frule traceable_implies_subexp, rule infinite_prog_\<V>_restricted),
    (simp add: infinite_prog_def; (erule subexp.cases; auto)+, fold infinite_prog_def),
    (
      (rotate_tac 3),
      (drule dest; simp?; auto),
      ((erule subexp.cases; auto)+)
    )+
  )+
)

method elim_traceable_app = (
  (thin_tac "^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y"),
  (thin_tac "infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>, LET x = APP f x\<^sub>a in e\<^sub>n') "),
  (simp add: infinite_prog_\<V>_def; (match premises in I: "_ \<in> (if P then _ else _) " for P \<Rightarrow> \<open>cases P\<close>, auto)+)
)

method elim_traceable = (
  (drule traceable_implies_subexp, rule infinite_prog_\<V>_restricted),
  (simp add: infinite_prog_def; (erule subexp.cases; auto)+)
)

  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> ;; l \<mapsto> e';
    (\<V>, \<F>) \<TTurnstile> e\<^sub>0
  \<rbrakk> \<Longrightarrow>
  \<exists> e . {(e, l, e')} \<subseteq> \<F>

lemma infinite_prog_has_earlier_sync: "
  \<lbrakk>
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;
    ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y;
    \<pi>\<^sub>y ;; `x\<^sub>y \<noteq> [`g100, .g101, `g102, `g108, \<upharpoonleft>g109, `g105, `g106]
  \<rbrakk> \<Longrightarrow>
  (\<exists>\<pi> x. 
    \<pi>\<^sub>y ;; `x\<^sub>y = (\<pi> ;; `x) @ [\<upharpoonleft>g107, `g105, `g106] \<and>
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> \<pi> \<mapsto> LET x = SYNC x\<^sub>e in e\<^sub>n \<and> 
    ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x
  )
"

these proof procedures take way too long.
There is quite a bit of eliminating false premises, by looking at cases of cases of cases ... at multiple depths.

Perhaps, the correct behavior of a computable function would be much faster to prove.
Since it's deterministic, there would be no need to waste time eliminating false premises.

 apply (erule traceable.cases; clarsimp)
  apply (simp add: infinite_prog_def)
  apply (elim_traceable_result dest: traceable_result_implies_traceable_case)
  apply (elim_traceable_result dest: traceable_result_implies_traceable_case)
  apply (elim_traceable_result dest: traceable_result_implies_traceable_app)
  apply (elim_traceable_app)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)

  apply (erule traceable.cases; clarsimp)
    apply (simp add: infinite_prog_def; auto)
sorry


lemma infinite_prog_matches': "
  (\<forall> \<pi>\<^sub>y x\<^sub>y x\<^sub>e e\<^sub>n x\<^sub>s\<^sub>c x\<^sub>m.
    (n :: nat) = length (\<pi>\<^sub>y ;; `x\<^sub>y) \<longrightarrow>
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n \<longrightarrow>
    ^Chan g100 \<in> infinite_prog_\<V> x\<^sub>s\<^sub>c \<longrightarrow>
    ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> infinite_prog_\<V> x\<^sub>e \<longrightarrow>
    ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y \<longrightarrow>
    infinite_prog_\<V> x\<^sub>m \<subseteq> infinite_prog_\<C> g100 \<longrightarrow>
    infinite_prog_send_g100_abstract_path |\<rhd> (\<pi>\<^sub>y ;; `x\<^sub>y)
  )
"
 apply (unfold infinite_prog_\<C>_def infinite_prog_send_g100_abstract_path_def)
 apply (rule nat_less_induct[of _ n], (rule allI)+, (rule impI)+)
  (* base case *)
 apply (case_tac "\<pi>\<^sub>y ;; `x\<^sub>y = [`g100, .g101, `g102, `g108, \<upharpoonleft>g109, `g105, `g106]", clarsimp)
  apply (match conclusion in 
    "(&x) :@: _  |\<rhd> x # _" for x \<Rightarrow> \<open>(rule cons_eq_append[THEN subst], rule ap_matches.Concat, rule ap_matches.Atom)\<close>
  )+
  apply (rule ap_matches.Star_Empty)
 (* Inductive case *)
 apply ((drule infinite_prog_has_earlier_sync; simp), (erule exE)+)
  apply (drule_tac x = "(length (\<pi> ;; `x))" in spec, clarsimp)
  apply (drule_tac x = "\<pi>" in spec, clarsimp)
  apply (drule_tac x = "x" in spec)
  apply (drule_tac x = "x\<^sub>e" in spec, erule impE, rule_tac x = "e\<^sub>n" in exI, assumption)
  apply (drule_tac x = "x\<^sub>s\<^sub>c" in spec, erule impE, assumption)
  apply (drule_tac x = "x\<^sub>m" in spec, (erule impE, assumption)+)
  apply (subgoal_tac "&\<upharpoonleft>g107 :@: &`g105 :@: &`g106 |\<rhd> [\<upharpoonleft>g107, `g105, `g106]")
  apply (drule ap_matches.Concat; simp)
  apply (thin_tac "&\<upharpoonleft>g107 :@: &`g105 :@: &`g106 |\<rhd> [\<upharpoonleft>g107, `g105, `g106]")
  apply ((erule ap_matches.cases; auto), erule ap_matches.Concat)+
  apply (erule concat_star_implies_star)
  apply (match conclusion in 
    "(&x) :@: _  |\<rhd> x # _" for x \<Rightarrow> \<open>(rule cons_eq_append[THEN subst], rule ap_matches.Concat, rule ap_matches.Atom)\<close>
  )+
  apply (rule ap_matches.Atom)
done

lemma infinite_prog_matches: "
  is_static_send_path (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100 \<pi> \<Longrightarrow> 
  infinite_prog_send_g100_abstract_path |\<rhd> \<pi>
"
(*
 apply (simp add: is_static_send_path_def; clarsimp)
 apply (insert infinite_prog_matches', blast)
*)
sorry

theorem infinite_prog_has_single_sender_communication_analysis: "
  all (is_static_send_path (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100) noncompetitive 
"

sorry


theorem infinite_prog_has_single_receiver_communication_analysis: "
  all (is_static_recv_path (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100) noncompetitive
"
sorry

theorem infinite_prog_has_one_to_one_communication_analysis: "
  static_one_to_one (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100
"
sorry

(*

method condition_split = (
  match premises in 
    I: "(if P then _ else _) = Some _" for P \<Rightarrow> \<open>cases P\<close>
, auto)


method leaf_elim_loop for m :: state_pool and stpool :: state_pool and l :: control_path uses I = (
  match (m) in 
    "Map.empty" \<Rightarrow> \<open> fail \<close> \<bar>
    "m'((p :: control_path) \<mapsto> (_ :: state))" for m' p \<Rightarrow> 
        \<open>((insert I, (drule leaf_elim[of stpool l p]), auto); leaf_elim_loop m' stpool l I: I)\<close>
)

method leaf_elim_search = (
  match premises in 
    I: "leaf stpool lf" for stpool lf \<Rightarrow> \<open>(leaf_elim_loop stpool stpool lf I: I)\<close>
)


method topo_solve = 
  (
    (erule star.cases, auto),
    (simp add: recv_sites_def send_sites_def leaf_def, auto),
    (condition_split+),
    (erule concur_step.cases, auto),
    (erule seq_step.cases),
    (condition_split | leaf_elim_search)+
  )

    
abbreviation a where "a \<equiv> Var ''a''"
abbreviation b where "b \<equiv> Var ''b''"
abbreviation c where "c \<equiv> Var ''c''"
abbreviation d where "d \<equiv> Var ''d''"
abbreviation e where "e \<equiv> Var ''e''"
abbreviation f where "f \<equiv> Var ''f''"
abbreviation w where "w \<equiv> Var ''w''"
abbreviation x where "x \<equiv> Var ''x''"
abbreviation y where "y \<equiv> Var ''y''"
abbreviation z where "z \<equiv> Var ''z''"

definition prog_one where 
  "prog_one = 
    LET a = CHAN \<lparr>\<rparr> in
    LET b = SPAWN (
      LET c = CHAN \<lparr>\<rparr> in
      LET d = SEND EVT a b in
      LET w = SYNC d in
      RESULT d
    ) in
    LET e = RECV EVT a in
    LET f = SYNC e in
    RESULT f
  "
 
theorem prog_one_properties: "single_receiver prog_one a"
  apply (unfold single_receiver_def single_side_def single_side'_def recv_sites_def prog_one_def)
  apply auto
  apply topo_solve+
done


theorem prog_one_properties2: "single_sender prog_one a"
  apply (unfold single_sender_def single_side_def single_side'_def send_sites_def prog_one_def)
  apply auto
  apply topo_solve+
done

definition prog_two where 
  "prog_two = 
    LET a = CHAN \<lparr>\<rparr> in
    LET b = SPAWN (
      LET c = CHAN \<lparr>\<rparr> in
      LET x = SEND EVT a c in
      LET y = SYNC x in
      LET z = RECV EVT c in
      RESULT z
    ) in
    LET d = RECV EVT a in
    LET e = SYNC d in
    LET f = SEND EVT e b in
    LET w = SYNC f in
    RESULT w
  "
    
definition prog_three where 
  "prog_three = 
    .LET a = .CHAN \<lparr>\<rparr> in
    .LET b = .SPAWN (
      .LET c = .CHAN \<lparr>\<rparr> in
      .LET x = .SEND EVT .a .c in
      .LET y = .SYNC .x in
      .LET z = .RECV EVT .c in
      .z
    ) in
    .LET d = .RECV EVT .a in
    .LET e = .SYNC .d in
    .LET f = .SEND EVT .e .b in
    .LET w = .SYNC .f in
    .w
  "
  
definition prog_four where
  "prog_four = 
    .LET a = .FN f x .
      .CASE .x
      LEFT b |> .RIGHT (.APP .f .b)
      RIGHT b |> .LEFT .b
    in
    .APP .a (.LEFT (.LEFT (.LEFT (.RIGHT .\<lparr>\<rparr>))))
  "



*)


end
