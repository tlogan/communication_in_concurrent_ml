theory Sound_Semantics
  imports Main Syntax Dynamic_Semantics Static_Semantics
    "~~/src/HOL/Library/List"
begin


fun valToStaticVal :: "val \<Rightarrow> static_val" ("|_|" [0]61) where
  "|VUnt| = ^Unt"
| "|VChn (Ch \<pi> x)| = ^Chan x"
| "|VClsr p \<rho>| = ^p"

inductive 
    staticEvalVal :: "static_env \<times> static_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55) 
and staticEvalEnv :: "static_env \<times> static_env \<Rightarrow> env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt
  "
| Chan:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VChn c
  "
| SendEvt:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt _ _) \<rho>)
  "
| RecvEvt:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (RecvEvt _) \<rho>)
  "
| Lft:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Lft _) \<rho>)
  "
| Rht:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Rht _) \<rho>)
  "
| Fun:
  "
    {^Fun f x e} \<subseteq> \<V> f \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Fun f x e) \<rho>)
  "
| Pair:
  "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Pair _ _) \<rho>)
  "
| Intro: " 
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive staticEval_stack :: "static_env \<times> static_env \<Rightarrow> static_val set \<Rightarrow> contin list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []"
| Nonempty:
  "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> ((Ctn x e \<rho>) # \<kappa>)
  "


inductive staticEvalState :: "static_env \<times> static_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Intro:
  "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive staticEvalPool :: "static_env \<times> static_env \<Rightarrow> trace_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Intro:
  "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>) \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
  "

lemma staticEvalState_to_tm_result:
"
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x;\<rho>;(Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>
"
proof -
  assume 
    "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x;\<rho>;(Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" 
  then have 
    "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>" by (simp add: staticEvalState.simps) then
  show 
    "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (rule staticEval_stack.cases; auto)
qed


lemma staticEvalState_to_tm_CaseLft:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l
"
proof -
  assume 
    H1: "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" and
    H2: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>"


  from H2 have 
    H3: "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" and
    H4: "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" using staticEvalState.cases by blast+

  from H4 have H5: "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" using staticEvalEnv.simps by auto

  from H1 H5 have 
    H6: "^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s" by fastforce

  from H3 show 
    "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l"
  proof cases
    case BindCase 

    from H6 local.BindCase(1) show 
      "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" using local.BindCase(2) by blast 
  qed
qed


lemma staticEvalState_to_tm_CaseRht:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r
"
proof -
  assume "\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e"
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" 
    by (simp add: staticEvalState.simps)+ then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: staticEvalEnv.simps)
  with `\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)`
  have "^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s" by fastforce
  with `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r"
  proof cases
    case BindCase 
    with 
      `\<forall>x\<^sub>r'. ^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x`  
      `^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by blast
  qed
qed


lemma staticEvalState_to_tm_let:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x b e" by (simp add: staticEvalState.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (rule staticEval.cases; auto)
qed


lemma staticEvalState_to_tm_App:
  "
 (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
 \<rho> f = Some (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>') \<Longrightarrow>
 (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b
"

proof -
  assume "\<rho> f = Some (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>')"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps) then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: staticEvalEnv.simps)
  with `\<rho> f = Some (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>')`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>')" by simp then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b" by (rule staticEvalVal.cases; auto)
qed

lemma staticEvalState_to_env_result:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
"
proof
 assume "\<rho> x = Some \<omega> "

 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (rule staticEvalState.cases; auto)+

 from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x = Some \<omega>`
 have "{|\<omega>|} \<subseteq> \<V> x" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: staticEvalEnv.simps)+

 from `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>`
 show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
 proof cases
   case Nonempty
   assume "\<V> x \<subseteq> \<V> x\<^sub>\<kappa>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>"

   from `{|\<omega>|} \<subseteq> \<V> x` `\<V> x \<subseteq> \<V> x\<^sub>\<kappa>`
   have "{|\<omega>|} \<subseteq> \<V> x\<^sub>\<kappa>" by blast

   {
     fix x' \<omega>'
     assume "(\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x' = Some \<omega>'" 

     have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" 
     proof cases
       assume "x' = x\<^sub>\<kappa>" with `(\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x' = Some \<omega>'`
       and  `{|\<omega>|} \<subseteq> \<V> x\<^sub>\<kappa>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>`
     
       show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
     next
       assume "x' \<noteq> x\<^sub>\<kappa>" with `(\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x' = Some \<omega>'`

       have "\<rho>\<^sub>\<kappa> x' = Some \<omega>'" by simp 
       with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>`
       
       show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)+
     qed
   } then

   show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
 qed
qed


lemma staticEvalState_to_stack_result:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "\<rho> x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>" by (simp add: staticEvalState.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (rule staticEval_stack.cases; auto)
qed


lemma staticEvalState_to_state_result:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "\<rho> x = Some \<omega>" "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)" by (blast intro: staticEvalState_to_env_result)

  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (blast intro: staticEvalState_to_tm_result)

  with `\<rho> x = Some \<omega>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: staticEvalState_to_stack_result)
qed


lemma staticEvalState_to_env_let_unit:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x Unt e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+ 

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x Unt e`
  have "{^Unt} \<subseteq> \<V> x" by (rule staticEval.cases; auto)+
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt" by (simp add: Unit)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>'" 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
    proof cases
      assume "x' = x" 
      with `(\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>'` 
      and `{^Unt} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
    next 
      assume "x' \<noteq> x"  with `(\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>'` 

      have "\<rho> x' = Some \<omega>'" by simp

      from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x' = Some \<omega>'`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
    qed

  }
  with `{^Unt} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma staticEvalState_to_stack_let:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
by (erule staticEvalState.cases; auto)

lemma staticEvalState_to_state_let_unit:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> VUnt); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: staticEvalState_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)" by (auto simp: staticEvalState_to_env_let_unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: staticEvalState_to_stack_let)

qed

lemma staticEval_to_value_let_atom:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Atom p) e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr p \<rho>)
"
by (erule staticEval.cases; auto; rule; auto)

lemma staticEvalState_to_env_let_atom:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VClsr p \<rho>))
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle> " then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Atom p) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+ then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr p \<rho>)" by (simp add: staticEval_to_value_let_atom)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Atom p) e`
  have "{^p} \<subseteq> \<V> x" by (rule staticEval.cases; auto)+
 
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> (VClsr p \<rho>))) x' = Some \<omega>'" 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
    proof cases
      assume "x' = x" with \<open>(\<rho>(x \<mapsto> (VClsr p \<rho>))) x' = Some \<omega>'\<close>
      and `{^p} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr p \<rho>)`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
    next
      assume  "x' \<noteq> x"  with \<open>(\<rho>(x \<mapsto> (VClsr p \<rho>))) x' = Some \<omega>'\<close>

      have "\<rho> x' = Some \<omega>'" by simp
      with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
  
      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
    qed

  } then

  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> (VClsr p \<rho>))) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma staticEvalState_to_state_let_atom:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> (VClsr p \<rho>)); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: staticEvalState_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: staticEvalState_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VClsr p \<rho>))" by (auto simp: staticEvalState_to_env_let_atom)

qed


lemma staticEvalState_to_env_CaseLft:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
"

proof
  assume "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" by (blast intro: staticEvalEnv.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (blast intro: staticEvalVal.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l" by (blast intro: staticEvalEnv.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)`
  have " | (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) | \<in> \<V> x\<^sub>s" by (blast intro: staticEvalEnv.cases) then
  have "^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  have "\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l"
  proof cases
    case BindCase
    from `\<forall>x\<^sub>l'. ^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x`
    and `^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l" by simp
  qed

  from `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'` `\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l` 
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
   
  }
  with `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma staticEvalState_to_stack_CaseLft:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: staticEvalState.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)`
  have " | (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) | \<in> \<V> x\<^sub>s" by (blast intro: staticEvalEnv.cases) then
  have "^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  show "\<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x" 
  proof cases
    case BindCase
    assume "\<forall>x\<^sub>l'. ^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x"
    with `^atom.Lft x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "\<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x" by blast
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: staticEvalState_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: staticEvalState.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: staticEvalState_to_stack_let)
  
qed


lemma staticEvalState_to_state_CaseLft:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); (Ctn x e \<rho>) # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" by (simp add: staticEvalState_to_tm_CaseLft)

  assume "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)" by (simp add: staticEvalState_to_env_CaseLft)

  from `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>`
  and `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>" by (simp add: staticEvalState_to_stack_CaseLft)
qed


lemma staticEvalState_to_env_CaseRht:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
"

proof
  assume "\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)" by (blast intro: staticEvalEnv.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (blast intro: staticEvalVal.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r" by (blast intro: staticEvalEnv.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)`
  have " | (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r) | \<in> \<V> x\<^sub>s" by (blast intro: staticEvalEnv.cases) then
  have "^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  have "\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r"
  proof cases
    case BindCase
    from `\<forall>x\<^sub>r'. ^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x`
    and `^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'` `\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r` 
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
   
  }
  with `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma staticEvalState_to_stack_CaseRht:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: staticEvalState.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)`
  have " | (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r) | \<in> \<V> x\<^sub>s" by (blast intro: staticEvalEnv.cases) then
  have "^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  show "\<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x" 
  proof cases
    case BindCase
    assume "\<forall>x\<^sub>r'. ^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x"
    with `^atom.Rht x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "\<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x" by blast
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: staticEvalState_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: staticEvalState.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: staticEvalState_to_stack_let)
  
qed

lemma staticEvalState_to_state_CaseRht:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); (Ctn x e \<rho>) # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (simp add: staticEvalState_to_tm_CaseRht)

  assume "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)" by (simp add: staticEvalState_to_env_CaseRht)

  from `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>`
  and `\<rho> x\<^sub>s = Some (VClsr (Rht x\<^sub>r') \<rho>\<^sub>r)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>" by (simp add: staticEvalState_to_stack_CaseRht)
qed


lemma staticEvalState_to_env_let_fst:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
proof
  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Fst x\<^sub>p) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" by (blast intro: staticEvalEnv.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: staticEvalVal.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>1" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: staticEvalEnv.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have " | (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) | \<in> \<V> x\<^sub>p" by (blast intro: staticEvalEnv.cases) then
  have "^atom.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Fst x\<^sub>p) e`
  have "\<V> x\<^sub>1 \<subseteq> \<V> x"
  proof cases
    case BindFst
    from `\<forall>x\<^sub>1 x\<^sub>2. ^atom.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x`
    and `^atom.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p`
    show "\<V> x\<^sub>1 \<subseteq> \<V> x" by blast
  qed

  from `{|\<omega>|} \<subseteq> \<V> x\<^sub>1` `\<V> x\<^sub>1 \<subseteq> \<V> x` 
  have "{|\<omega>|} \<subseteq> \<V> x" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>'" "x' \<noteq> x" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
  }
  with `{|\<omega>|} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed



lemma staticEvalState_to_state_let_fst:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: staticEvalState_to_tm_let)

  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)"  by (simp add: staticEvalState_to_env_let_fst)

  from `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)` and `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: staticEvalState_to_stack_let)
qed

lemma "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>"
sorry

lemma staticEvalState_to_env_let_snd:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>) 
"
proof
  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Snd x\<^sub>p) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" by (blast intro: staticEvalEnv.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: staticEvalVal.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>2" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: staticEvalEnv.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have " | (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) | \<in> \<V> x\<^sub>p" by (blast intro: staticEvalEnv.cases) then
  have "^atom.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Snd x\<^sub>p) e`
  have "\<V> x\<^sub>2 \<subseteq> \<V> x"
  proof cases
    case BindSnd
    from `\<forall>x\<^sub>1 x\<^sub>2. ^atom.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x`
    and `^atom.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p`
    show "\<V> x\<^sub>2 \<subseteq> \<V> x" by blast
  qed


  from `{|\<omega>|} \<subseteq> \<V> x\<^sub>2` `\<V> x\<^sub>2 \<subseteq> \<V> x` 
  have "{|\<omega>|} \<subseteq> \<V> x" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>'" "x' \<noteq> x" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
  }
  with \<open>{|\<omega>|} \<subseteq> \<V> x\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<close> 
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma staticEvalState_to_state_let_snd:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: staticEvalState_to_tm_let)

  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)" by (simp add: staticEvalState_to_env_let_snd)

  from `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)` and `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: staticEvalState_to_stack_let)
qed


lemma staticEvalState_to_env_App:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l) \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)
"
proof
  assume "\<rho> f = Some (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)" "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (App f x\<^sub>a) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x\<^sub>a = Some \<omega>\<^sub>a`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a" by (blast intro: staticEvalEnv.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)`
  have "{|(VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)" by (blast intro: staticEvalEnv.cases)+

  from `{|(VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f`
  have "^Fun f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)`
  have "{|(VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f\<^sub>l" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (rule staticEvalVal.cases; auto)+


  with `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (App f x\<^sub>a) e`
  have "\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l"
  proof cases
    case App
    assume "\<forall>f' x' e'. ^Fun f' x' e' \<in> \<V> f \<longrightarrow> \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x"
    with `^Fun f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f`
    show "\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l" by blast
  qed

  from `{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a` `\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l" by blast


  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" "x' \<noteq> f\<^sub>l" then
    have "\<rho>\<^sub>l x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
  }
  with \<open>{|(VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f\<^sub>l\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a\<close> \<open>{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l\<close>
  show "\<forall>x \<omega>. (\<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClsr (Fun f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto

qed

lemma staticEvalState_to_stack_App:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>') \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>
"
proof
  assume "\<rho> f = Some (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>')" and "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (App f x\<^sub>a) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: staticEvalState.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some (VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>')`
  have " {|(VClsr (Fun f' x\<^sub>p e\<^sub>b) \<rho>')|} \<subseteq> \<V> f" by (blast intro: staticEvalEnv.cases) then
  have " ^Fun f' x\<^sub>p e\<^sub>b \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (App f x\<^sub>a) e`
  show " \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> \<V> x"
  proof cases
    case App
    assume "\<forall>f' x' e'. ^Fun f' x' e' \<in> \<V> f \<longrightarrow> \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x"
    with `^Fun f' x\<^sub>p e\<^sub>b \<in> \<V> f`
    show " \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> \<V> x" by simp
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: staticEvalState_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: staticEvalState.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: staticEvalState_to_stack_let)
qed


theorem staticEvalStatePreservedDynamicEval_under_step :
  "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>; 
    seqEval b \<rho> \<omega>
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>" and
    H2: "seqEval b \<rho> \<omega>"
    
  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>"
  proof cases
    case UNIT
    
    assume
      H3: "b = Unt" and
      H4: "\<omega> = VUnt"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x Unt e; \<rho>; \<kappa>\<rangle>" by simp

    then have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho> ++ [x \<mapsto> VUnt]; \<kappa>\<rangle>" by (simp add: staticEvalState_to_state_let_unit)
    
    with H4 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by simp
  next
    case (PRIM p)

    assume
      H3: "b = Atom p" and
      H4: "\<omega> = VClsr p \<rho>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Atom p) e; \<rho>; \<kappa>\<rangle>" by simp

    then have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho> ++ [x \<mapsto> VClsr p \<rho>]; \<kappa>\<rangle>" by (simp add: staticEvalState_to_state_let_atom)
    
    with H4 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by simp
  next
    case (FST x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)

    assume 
      H3: "b = (Fst x\<^sub>p)" and
      H4: "\<rho> x\<^sub>p = Some (VClsr (atom.Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and
      H5: "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" by simp

    with H4 H5 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>" by (simp add: staticEvalState_to_state_let_fst)
  next
    case (SND x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)

    assume 
      H3: "b = (Snd x\<^sub>p)" and
      H4: "\<rho> x\<^sub>p = Some (VClsr (atom.Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and
      H5: "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" by simp

    with H4 H5 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>" by (simp add: staticEvalState_to_state_let_snd)
  qed
qed

theorem staticEvalStatePreservedDynamicEval_under_step_up :
  "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>;
    callEval (b, \<rho>) (e', \<rho>')
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; (Ctn x e \<rho>) # \<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>" and
    H2: "callEval (b, \<rho>) (e', \<rho>')"

  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; (Ctn x e \<rho>) # \<kappa>\<rangle>" 
  proof cases
    case (CaseLft xs xl' envl vl xl xr er)
    then show ?thesis
      using H1 staticEvalState_to_state_CaseLft by blast
    next
      case (CaseRht xs xr' envr vr xl el xr)
      then show ?thesis
        using H1 staticEvalState_to_state_CaseRht by blast
    next
      case (App f fp xp envl xa va)
      then show ?thesis
        using H1 staticEvalState.intros staticEvalState_to_env_App staticEvalState_to_tm_App staticEvalState_to_stack_App by auto
    qed
qed

theorem staticEvalStatePreservedDynamicEval_under_step_down :
  "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>; 
    \<rho> x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" and
    H2: "\<rho> x = Some \<omega>"

  from H1 H2
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>" by (auto simp: staticEvalState_to_state_result)
qed

lemma staticEvalPool_to_tm_let:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Bind x b e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Bind x b e; \<rho>; \<kappa>\<rangle>)" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>" by (simp add: staticEvalPool.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e " by (blast intro: staticEvalState_to_tm_let)
qed


lemma staticEvalPool_let_sync_send_values_relate:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c)) \<Longrightarrow>
  {^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "{|(VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)|} \<subseteq> \<V> x\<^sub>s\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" by (blast intro: staticEvalEnv.cases)+

  from `{|(VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)|} \<subseteq> \<V> x\<^sub>s\<^sub>e`
  have "^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: staticEvalVal.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))`
  have "{|(VChn (Ch \<pi>\<^sub>c x\<^sub>c))|} \<subseteq> \<V> x\<^sub>s\<^sub>c" by (blast intro: staticEvalEnv.cases) then
  have "{^Chan x\<^sub>c} \<subseteq> \<V> x\<^sub>s\<^sub>c" by simp then
  have "^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c" by auto
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s`
  show "{^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c"
  proof cases
    case BindSync
    assume "\<forall>x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c. ^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e \<longrightarrow> ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow> {^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c"
    with `^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e` and `^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c`
    show "{^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" by blast
  qed

qed

lemma staticEvalPool_let_sync_send_message_relate:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  {|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: staticEvalState.simps)
  with `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" by (blast intro: staticEvalEnv.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: staticEvalVal.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
  show "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" by (blast intro: staticEvalEnv.cases)
qed

lemma staticEvalPool_to_env_let_sync_send:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)
"
proof
  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)"
  and  "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: staticEvalState.simps)+

  have "{^Unt} \<subseteq> \<V> x\<^sub>s"
  proof (cases c)
    case (Ch \<pi> x\<^sub>c)
    assume "c = Ch \<pi> x\<^sub>c" 
    with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)`
    and  `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
    show "{^Unt} \<subseteq> \<V> x\<^sub>s" using staticEvalPool_let_sync_send_values_relate by simp
  qed
  
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt" by (simp add: Unit)
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>s" then
    have "\<rho>\<^sub>s x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
  }
  with \<open>{^Unt} \<subseteq> \<V> x\<^sub>s\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt\<close> 
  show "\<forall>x \<omega>. (\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by simp
qed


lemma staticEvalPool_let_sync_recv_values_relate:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c)) \<Longrightarrow>
  \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: staticEvalState.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
  have "{|(VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)|} \<subseteq> \<V> x\<^sub>r\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)" by (blast intro: staticEvalEnv.cases)+

  from `{|(VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)|} \<subseteq> \<V> x\<^sub>r\<^sub>e`
  have "^RecvEvt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r\<^sub>e" by (blast intro: staticEvalVal.cases)
  with `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))`
  have "{|(VChn (Ch \<pi>\<^sub>c x\<^sub>c))|} \<subseteq> \<V> x\<^sub>r\<^sub>c" by (blast intro: staticEvalEnv.cases) then
  have "{^Chan x\<^sub>c} \<subseteq> \<V> x\<^sub>r\<^sub>c" by simp then
  have "^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c" by auto
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r`
  show "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r"
  proof cases
    case BindSync
    assume "\<forall>x\<^sub>r\<^sub>c x\<^sub>c. ^RecvEvt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r"
    with `^RecvEvt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e` and `^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c`
    show "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" by blast
  qed
qed


lemma staticEvalPool_to_stack_let:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Bind x b e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Bind x b e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e; \<rho>; \<kappa>\<rangle>" by (simp add: staticEvalPool.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: staticEvalState_to_stack_let)
qed

lemma staticEvalPool_to_env_let_sync_recv:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow> 
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m" then
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" using staticEvalPool_let_sync_send_message_relate by auto

  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: staticEvalState.simps)+


  have "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r"
  proof (cases c)
    case (Ch \<pi>\<^sub>c x\<^sub>c)
    assume "c = Ch \<pi>\<^sub>c x\<^sub>c" 

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
    have "\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" using \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)\<close> staticEvalPool_let_sync_send_values_relate by blast

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
    and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
    have "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" using  staticEvalPool_let_sync_recv_values_relate by auto

    from `\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c` and `\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r`
    show "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m` and `\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r`
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r" by blast

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: staticEvalState.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho>\<^sub>r x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
  }
  with `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m`
  show "\<forall>x \<omega>. (\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto
qed


lemma staticEvalPreservedDynamicEval_under_sync:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)"


  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s" by (blast intro: staticEvalPool_to_tm_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)" by (blast intro: staticEvalPool_to_env_let_sync_send)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s" by (blast intro: staticEvalPool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>" by (blast intro: staticEvalState.intros)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (blast intro: staticEvalPool_to_tm_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
  and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)\<close> 
  and \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)\<close>
  and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  and \<open>\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)\<close> \<open>\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)" by (blast intro: staticEvalPool_to_env_let_sync_recv)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r" by (blast intro: staticEvalPool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>" by (blast intro: staticEvalState.intros)

  {
    fix \<pi> \<sigma>
    assume  "\<pi> \<noteq> \<pi>\<^sub>s @ [LNxt x\<^sub>s]" and "\<pi> \<noteq> \<pi>\<^sub>r @ [LNxt x\<^sub>r]"
    and "(\<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma>" then
    have "\<E> \<pi> = Some \<sigma>" by simp
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (blast intro: staticEvalPool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r (x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s (x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>`
  show "\<forall>\<pi> \<sigma>. (\<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by simp

qed


lemma staticEvalPool_to_env_let_chan:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChn (Ch \<pi> x)))
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>" by (blast intro: staticEvalPool.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x MkChn e" by (blast intro: staticEvalState.cases) then
  have "{^Chan x} \<subseteq> \<V> x"  by (blast intro: staticEval.cases)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VChn (Ch \<pi> x))" by (simp add: Chan)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>` 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> (VChn (Ch \<pi> x)))) x' = Some \<omega>'" and "x \<noteq> x'"then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: staticEvalEnv.simps)
  } with `{^Chan x} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VChn (Ch \<pi> x))`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> (VChn (Ch \<pi> x)))) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma staticEvalPreservedDynamicEval_under_chan:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e; \<rho>(x \<mapsto> (VChn (Ch \<pi> x))); \<kappa>\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: staticEvalPool_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChn (Ch \<pi> x)))" by (blast intro: staticEvalPool_to_env_let_chan )

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Bind x MkChn e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: staticEvalPool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChn (Ch \<pi> x)))` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>" by (blast intro: staticEvalState.intros)
  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some \<sigma>'" 
    and "\<pi>' \<noteq> \<pi> @ [LNxt x]" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: staticEvalPool.simps)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


lemma staticEvalPool_to_env_let_spawn:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Spwn e\<^sub>c) e" by (blast intro: staticEvalState.cases) then
  have "{^Unt} \<subseteq> \<V> x"  by (blast intro: staticEval.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt" by (simp add: Unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>'" and "x \<noteq> x'" then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (blast intro: staticEvalEnv.cases)
  } with `{^Unt} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed

lemma staticEvalPreservedSpawn:
  "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e; \<rho>(x \<mapsto> VUnt); \<kappa>\<rangle>, \<pi>@ [LSpwn x] \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: staticEvalPool_to_tm_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)" by (blast intro: staticEvalPool_to_env_let_spawn)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: staticEvalPool_to_stack_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<close>
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>" by (simp add: staticEvalState.intros)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>" by (simp add: staticEvalPool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Spwn e\<^sub>c) e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Bind x (Spwn e\<^sub>c) e`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c" by (blast intro: staticEval.cases)

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []" by (simp add: staticEval_stack.Empty)
  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>" by (simp add: staticEvalState.intros)

  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>, \<pi> @ [LSpwn x] \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>'"
    and "\<pi>' \<noteq> \<pi> @ [LNxt x]" and " \<pi>' \<noteq> \<pi> @ [LSpwn x]" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (blast intro: staticEvalPool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>, \<pi> @ [LSpwn x] \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


theorem staticEvalPreservedDynamicEval :
  "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    (\<E>, H) \<rightarrow> (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and
    H2: "(\<E>, H) \<rightarrow> (\<E>', H')"

  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    have L1H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LRtn x] \<mapsto> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>);\<kappa>\<rangle>)"
      using H1 local.Seq_Step_Down(4) local.Seq_Step_Down(5) staticEvalPool.simps staticEvalState_to_state_result by fastforce

    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H1 local.Seq_Step_Down(1))
  next
    case (Seq_Step \<pi> x b e \<rho> \<kappa> \<omega>)

    have L1H7:"(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Bind x b e;\<rho>;\<kappa>\<rangle>"
      using H1 local.Seq_Step(4) staticEvalPool.simps by auto

    have L1H8: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>"
      using L1H7 local.Seq_Step(5) staticEvalStatePreservedDynamicEval_under_step by blast

    have L1H9: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>)"
      using H1 L1H8 staticEvalPool.simps by auto

    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H9 local.Seq_Step(1))
  next
    case (Seq_Step_Up \<pi> x b e \<rho> \<kappa> e' \<rho>')
    have L1H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LCall x] \<mapsto> \<langle>e';\<rho>';(Ctn x e \<rho>) # \<kappa>\<rangle>)"
      using H1 local.Seq_Step_Up(4) local.Seq_Step_Up(5) staticEvalPool.simps staticEvalStatePreservedDynamicEval_under_step_up by fastforce
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H1 local.Seq_Step_Up(1))
  next
    case (BindMkChn \<pi> x e \<rho> \<kappa>)
    show ?thesis
      by (simp add: H1 local.BindMkChn(1) local.BindMkChn(4) staticEvalPreservedDynamicEval_under_chan)
  next
    case (BindSpawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    show ?thesis
      by (simp add: H1 local.BindSpawn(1) local.BindSpawn(4) staticEvalPreservedSpawn)
  next
    case (BindSync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)
    have L1H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)" 
      by (simp add: H1 local.BindSync(10) local.BindSync(11) local.BindSync(4) local.BindSync(5) local.BindSync(7) local.BindSync(8) local.BindSync(9) staticEvalPreservedDynamicEval_under_sync)
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H1 local.BindSync(1))
  qed
qed


theorem staticEvalPreserved :
"
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;  
    star dynamicEval (\<E>, H) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and 
    H2: "star dynamicEval (\<E>, H) (\<E>', H')"

  obtain X X' where H3: "X = (\<E>, H)" and H4: "X' = (\<E>', H')" by simp
  
  from H2 H3 H4 have H5: "star dynamicEval X X'" by simp
 
  from H5 have 
    H6: "\<forall> \<E> H \<E>' H' . X = (\<E>, H) \<longrightarrow> X' = (\<E>', H') \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
  proof (induction rule: star.induct)
    case (refl X0)
    show ?case by simp
  next
    case (step X Xm X')

    {
      fix \<E> H \<E>' H' 
      assume 
        L1H1: "X = (\<E>, H)" and 
        L1H2: "X' = (\<E>', H')" and 
        L1H3: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"

      from L1H1 L1H2 L1H3 
      have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (metis eq_fst_iff staticEvalPreservedDynamicEval step.IH step.hyps(1))
    }
    
    then show ?case by blast
  qed 

  from H1 H3 H4 H6
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
qed


theorem staticEvalPoolSoundSnapshot :
  "
  \<rho> x = Some \<omega> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho> x = Some \<omega>"

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)" then

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>" by (simp add: staticEvalPool.simps) then

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: staticEvalState.simps) 
  with `\<rho> x = Some \<omega>`

  show "{|\<omega>|} \<subseteq> \<V> x" by (simp add: staticEvalEnv.simps)
qed


theorem staticEvalPoolSound :
  "
  \<rho>' x = Some \<omega> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> 
  star dynamicEval (\<E>, H) (\<E>', H') \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume 
    H1: "\<rho>' x = Some \<omega>" and
    H2: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and 
    H3: "star dynamicEval (\<E>, H) (\<E>', H')" and 
    H4: "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)"

  from H2 H3
  have H5: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by (blast intro: staticEvalPreserved)

  from H1 H4 H5
  show "{|\<omega>|} \<subseteq> \<V> x" using staticEvalPoolSoundSnapshot by auto
qed


lemma staticEval_to_pool:
"
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e"

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty" by (simp add: staticEvalVal_staticEvalEnv.Intro)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []" by (simp add: staticEval_stack.Empty)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>" by (simp add: staticEvalState.intros)

  have "[[] \<mapsto> \<langle>e; empty; []\<rangle>] [] = Some (\<langle>e; empty; []\<rangle>)" by simp
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: staticEvalPool.intros)
qed

theorem staticEvalSound :
"
  \<rho>' x = Some \<omega> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> \<langle>e; empty; []\<rangle>], H) (\<E>', H') \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume 
    H1: "\<rho>' x = Some \<omega>" and
    H2: "(\<V>, \<C>) \<Turnstile>\<^sub>e e" and 
    H3: "star dynamicEval ([[] \<mapsto> \<langle>e; empty; []\<rangle>], H) (\<E>', H')" and 
    H4: "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)"

  from H2 have 
    H5: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: staticEval_to_pool)

  from H1 H3 H4 H5
  show " {|\<omega>|} \<subseteq> \<V> x" using staticEvalPoolSound by blast
qed



inductive staticReachableForward :: "tm \<Rightarrow> tm \<Rightarrow> bool"  where
  Refl :
  "
    staticReachableForward e0 e0
  " 
|  BindSpawn_Child:
  "
    staticReachableForward e0 (Bind x (Spwn e\<^sub>c) e\<^sub>n) \<Longrightarrow>
    staticReachableForward e0 e\<^sub>c
  "
| CaseLft:
  "
    staticReachableForward e0 (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) \<Longrightarrow>
    staticReachableForward e0 e\<^sub>l
  "
| CaseRht:
  "
    staticReachableForward e0 (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) \<Longrightarrow>
    staticReachableForward e0 e\<^sub>r
  "
| BindFun:
  "
    staticReachableForward e0 (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e\<^sub>n) \<Longrightarrow>
    staticReachableForward e0 e\<^sub>b
  " 
| Bind:
  "
    staticReachableForward e0 (Bind x b e\<^sub>n) \<Longrightarrow>
    staticReachableForward e0 e\<^sub>n
  "

lemma staticReachable_trans:
  "
  staticReachable e\<^sub>z e\<^sub>y \<Longrightarrow> staticReachable e\<^sub>y e\<^sub>x \<Longrightarrow> staticReachable e\<^sub>z e\<^sub>x
"
proof -
  assume "staticReachable e\<^sub>y e\<^sub>x "
  assume "staticReachable e\<^sub>z e\<^sub>y" then
  have "(\<forall> e\<^sub>x . staticReachable e\<^sub>y e\<^sub>x \<longrightarrow> staticReachable e\<^sub>z e\<^sub>x)"
  proof (induction rule: staticReachable.induct)
    case (Refl e)
    show "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e e\<^sub>x" by simp
  next
    case (Bind e\<^sub>n e x b)
    assume "staticReachable e\<^sub>n e" "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>n e\<^sub>x"

    have "\<forall>e\<^sub>x. staticReachable e\<^sub>n e\<^sub>x \<longrightarrow> staticReachable (Bind x b e\<^sub>n) e\<^sub>x" by (simp add: staticReachable.Bind) 
    with `\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>n e\<^sub>x`
    show "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable (Bind x b e\<^sub>n) e\<^sub>x" by blast
  next
    case (BindSpawn_Child e\<^sub>c e x e\<^sub>n)
    assume "staticReachable e\<^sub>c e" "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>c e\<^sub>x"

    have "\<forall>e\<^sub>x. staticReachable e\<^sub>c e\<^sub>x \<longrightarrow> staticReachable (Bind x (Spwn e\<^sub>c) e\<^sub>n) e\<^sub>x" by (simp add: staticReachable.BindSpawn_Child)
    with `\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>c e\<^sub>x`
    show "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable (Bind x (Spwn e\<^sub>c) e\<^sub>n) e\<^sub>x"by blast
  next
    case (CaseLft e\<^sub>l e x x\<^sub>s x\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    assume "staticReachable e\<^sub>l e" "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>l e\<^sub>x"

    have "\<forall>e\<^sub>x. staticReachable e\<^sub>l e\<^sub>x \<longrightarrow> staticReachable (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by (simp add: staticReachable.CaseLft)
    with `\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>l e\<^sub>x`
    show "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by blast
  next
    case (CaseRht e\<^sub>r e x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>n)
    assume "staticReachable e\<^sub>r e" "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>r e\<^sub>x"

    have "\<forall>e\<^sub>x. staticReachable e\<^sub>r e\<^sub>x \<longrightarrow> staticReachable (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by (simp add: staticReachable.CaseRht)
    with `\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>r e\<^sub>x`
    show "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by blast
  next
    case (BindFun e\<^sub>b e x f x\<^sub>p e\<^sub>n)
    assume "staticReachable e\<^sub>b e" "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>b e\<^sub>x"

    have "\<forall>e\<^sub>x. staticReachable e\<^sub>b e\<^sub>x \<longrightarrow> staticReachable (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e\<^sub>n) e\<^sub>x" by (simp add: staticReachable.BindFun)
    with `\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable e\<^sub>b e\<^sub>x`
    show "\<forall>e\<^sub>x. staticReachable e e\<^sub>x \<longrightarrow> staticReachable (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e\<^sub>n) e\<^sub>x" by blast
  qed 
  with `staticReachable e\<^sub>y e\<^sub>x`
  show "staticReachable e\<^sub>z e\<^sub>x" by blast
qed


lemma staticReachableForward_implies_staticReachable:
  "
  staticReachableForward e e' \<Longrightarrow> staticReachable e e'
"
proof -
  assume "staticReachableForward e e'"
  
  then show "staticReachable e e'"
  proof induction
    case (Refl e0)
    show 
      "staticReachable e0 e0" by (simp add: staticReachable.Refl)
  next
    case (BindSpawn_Child e0 x e\<^sub>c e\<^sub>n)
    from BindSpawn_Child.IH show 
      "staticReachable e0 e\<^sub>c"
    using staticReachable.BindSpawn_Child staticReachable.Refl staticReachable_trans by blast
  next
    case (CaseLft e0 x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    from CaseLft.IH show
      "staticReachable e0 e\<^sub>l"
    using staticReachable.CaseLft staticReachable.Refl staticReachable_trans by blast
  next
    case (CaseRht e0 x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    from CaseRht.IH show 
      "staticReachable e0 e\<^sub>r"
    using staticReachable.CaseRht staticReachable.Refl staticReachable_trans by blast
  next
    case (BindFun e0 x f x\<^sub>p e\<^sub>b e\<^sub>n)
    from BindFun.IH show 
      "staticReachable e0 e\<^sub>b"
    using staticReachable.BindFun staticReachable.Refl staticReachable_trans by blast
  next
    case (Bind e0 x b e\<^sub>n)
    from Bind.IH show
      "staticReachable e0 e\<^sub>n"
    using staticReachable.Bind staticReachable.Refl staticReachable_trans by blast
  qed
qed


inductive staticReachableAtom :: "tm \<Rightarrow> atom \<Rightarrow> bool" where
  SendEvt:
  "
    staticReachableAtom e0 (SendEvt xC xM)
  "
| RecvEvt:
  "
    staticReachableAtom e0 (RecvEvt xC)
  "
| Pair:
  "
    staticReachableAtom e0 (Pair x1 x2)
  "
| Lft:
  "
    staticReachableAtom e0 (Lft x)
  "
| Rht:
  "
    staticReachableAtom e0 (Rht x)
  "
| Fun:
  "
    staticReachableForward e0 e\<^sub>b \<Longrightarrow>
    staticReachableAtom e0 (Fun f\<^sub>p x\<^sub>p e\<^sub>b)
  " 

inductive 
  staticReachableEnv :: "tm \<Rightarrow> env \<Rightarrow> bool" and
  staticReachableVal :: "tm \<Rightarrow> val \<Rightarrow> bool"
where
  VUnt:
  "
    staticReachableVal e0 VUnt
  "
| VChn:
  "
    staticReachableVal e0 (VChn c)
  "
| VClsr:
  "
    staticReachableAtom e0 p \<Longrightarrow>
    staticReachableEnv e0 \<rho>' \<Longrightarrow>
    staticReachableVal e0 (VClsr p \<rho>')
  "
| Intro:
  "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow> staticReachableVal e0 \<omega> \<Longrightarrow>
    staticReachableEnv e0 \<rho>
  "

inductive staticReachableStack :: "tm \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty:
  "
    staticReachableStack e0 []
  "
| Nonempty:
  "
    staticReachableForward e0 e\<^sub>\<kappa> \<Longrightarrow>
    staticReachableEnv e0 \<rho>\<^sub>\<kappa> \<Longrightarrow>
    staticReachableStack e0 \<kappa> \<Longrightarrow>
    staticReachableStack e0 ((Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>)
  "

inductive staticReachablePool :: "tm \<Rightarrow> trace_pool \<Rightarrow> bool" where
  Intro:
  "
    (\<forall>\<pi> e \<rho> \<kappa> . E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> 
      staticReachableForward e0 e \<and>
      staticReachableEnv e0 \<rho> \<and>
      staticReachableStack e0 \<kappa>) \<Longrightarrow>
    staticReachablePool e0 E
  "

lemma staticReachablePoolPreservedDynamicEval:
  "
  dynamicEval (env, H) (env', H') \<Longrightarrow>
  staticReachablePool e0 env \<Longrightarrow>
  staticReachablePool e0 env'
"
proof -
  assume
    H1: "staticReachablePool e0 env" and
    H3: "dynamicEval (env, H) (env', H')"

  from H3 show "staticReachablePool e0 env'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    then have 
      L1H2: "staticReachableEnv e0 \<rho>" and 
      L1H3: "staticReachableStack e0 ((Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>)"
      using H1 local.Seq_Step_Down(4) staticReachablePool.cases by blast+

   have 
      L1H4: "staticReachableForward e0 e\<^sub>\<kappa>" and 
      L1H5: "staticReachableEnv e0 \<rho>\<^sub>\<kappa>" and 
      L1H6: "staticReachableStack e0 \<kappa>"
     by (metis L1H3 contin.inject list.inject list.simps(3) staticReachableStack.simps)+

    from L1H2 L1H5 local.Seq_Step_Down(5) have L1H7: "staticReachableEnv e0 (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>))"
    using staticReachableEnv.simps by auto

    show ?thesis
      using H1 L1H4 L1H6 L1H7 local.Seq_Step_Down(1) staticReachablePool.simps by auto
  next
    case (Seq_Step \<pi> x b el \<rho>l \<kappa>l \<omega>)

    have 
      L1H2: "staticReachableForward e0 (Bind x b el)" and
      L1H3: "staticReachableEnv e0 \<rho>l" and
      L1H4: "staticReachableStack e0 \<kappa>l"
      using H1 local.Seq_Step(4) staticReachablePool.cases by blast+

    from L1H2 have L1H5: "staticReachableForward e0 el" by (blast dest: staticReachableForward.Bind)

    from local.Seq_Step(5) have 
      "staticReachableVal e0 \<omega>"
    proof cases
      case UNIT
      then show "staticReachableVal e0 \<omega>" by (simp add: VUnt)
    next
      case (PRIM p)

      have L2H1: "staticReachableAtom e0 p"
      proof (cases p)
        case (SendEvt x11 x12)
        then show "staticReachableAtom e0 p" by (simp add: staticReachableAtom.SendEvt)
      next
        case (RecvEvt x2)
        then show "staticReachableAtom e0 p" by (simp add: staticReachableAtom.RecvEvt)
      next
        case (Pair x31 x32)
        then show "staticReachableAtom e0 p" by (simp add: staticReachableAtom.Pair)
      next
        case (Lft x4)
        then show "staticReachableAtom e0 p" by (simp add: staticReachableAtom.Lft)
      next
        case (Rht x5)
        then show "staticReachableAtom e0 p" by (simp add: staticReachableAtom.Rht)
      next
        case (Fun x61 x62 x63)

        with L1H2 local.PRIM(1) local.Fun
        show "staticReachableAtom e0 p" by (smt staticReachableForward.BindFun staticReachableAtom.Fun )
      qed

      have L2H3: "staticReachableEnv e0 \<rho>l" by (simp add: L1H3)

      with L2H1 have "staticReachableVal e0 (VClsr p \<rho>l)" by (simp add: VClsr)

      with local.PRIM(2) show "staticReachableVal e0 \<omega>" by simp
    next
      case (FST x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)
      then show "staticReachableVal e0 \<omega>"
        by (metis L1H3 staticReachableEnv.cases staticReachableVal.cases val.distinct(3) val.distinct(5) val.inject(2))
    next
      case (SND x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)
      then show "staticReachableVal e0 \<omega>"
        by (metis L1H3 staticReachableEnv.cases staticReachableVal.cases val.distinct(3) val.distinct(5) val.inject(2))
    qed
    
    with L1H3 have L1H6: "staticReachableEnv e0 (\<rho>l(x \<mapsto> \<omega>))"
      by (smt staticReachableEnv.cases staticReachableEnv_staticReachableVal.Intro map_upd_Some_unfold)

    show ?thesis
      using H1 L1H4 L1H5 L1H6 local.Seq_Step(1) staticReachablePool.simps by auto
  next
    case (Seq_Step_Up \<pi> x b el \<rho>l \<kappa>l el' \<rho>l')
    
    have 
      L1H2: "staticReachableForward e0 (Bind x b el)" and
      L1H3: "staticReachableEnv e0 \<rho>l" and
      L1H4: "staticReachableStack e0 \<kappa>l"
      using H1 local.Seq_Step_Up(4) staticReachablePool.cases by blast+

    from L1H2 have 
      L1H5: "staticReachableForward e0 el" by (blast dest: staticReachableForward.Bind)

    from L1H3 L1H4 L1H5 have 
      L1H6: "staticReachableStack e0 ((Ctn x el \<rho>l) # \<kappa>l)" 
        by (simp add: staticReachableStack.Nonempty)

    from local.Seq_Step_Up(5)
    have 
      L1H7: "staticReachableForward e0 el' \<and> staticReachableEnv e0 \<rho>l'"
    proof cases
      case (CaseLft x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)

      from L1H2 local.CaseLft(1) have 
        L2H1: "staticReachableForward e0 el'" by (blast dest: staticReachableForward.CaseLft)

      from L1H3 local.CaseLft(3) have 
        "staticReachableVal e0 (VClsr (atom.Lft x\<^sub>l') \<rho>\<^sub>l)"
        by (blast dest: staticReachableEnv.cases)

      then have "staticReachableEnv e0 \<rho>\<^sub>l" by (blast dest: staticReachableVal.cases)

      with local.CaseLft(4) have "staticReachableVal e0 \<omega>\<^sub>l" by (blast dest: staticReachableEnv.cases)

      with L1H3 have "staticReachableEnv e0 (\<rho>l(x\<^sub>l \<mapsto> \<omega>\<^sub>l))"
        by (smt staticReachableEnv.cases staticReachableEnv_staticReachableVal.Intro map_upd_Some_unfold)

      with local.CaseLft(2) have 
        L2H2: "staticReachableEnv e0 \<rho>l'" by simp

      show ?thesis by (simp add: L2H1 L2H2)
    next
      case (CaseRht x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)

      from L1H2 local.CaseRht(1) have 
        L2H1: "staticReachableForward e0 el'"
          by (blast dest: staticReachableForward.CaseRht)

      from L1H3 local.CaseRht(3)
      have "staticReachableVal e0 (VClsr (atom.Rht x\<^sub>r') \<rho>\<^sub>r)"
        by (blast dest: staticReachableEnv.cases)

      then have "staticReachableEnv e0 \<rho>\<^sub>r" by (blast dest: staticReachableVal.cases)

      with L1H3 local.CaseRht(2) local.CaseRht(4) have 
        L2H2: "staticReachableEnv e0 \<rho>l'"
          by (auto simp: staticReachableEnv.simps)

      with L2H1 show "staticReachableForward e0 el' \<and> staticReachableEnv e0 \<rho>l'" by simp
    next
      case (App f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a)

      from L1H3 local.App(3) have
        L2H1: "staticReachableVal e0 (VClsr (Fun f\<^sub>l x\<^sub>l el') \<rho>\<^sub>l)" by (blast dest: staticReachableEnv.cases)

      then have 
        "staticReachableAtom e0 (Fun f\<^sub>l x\<^sub>l el')" by (blast dest: staticReachableVal.cases)

      then have L2H2: "staticReachableForward e0 el'" by (blast dest: staticReachableAtom.cases)

      from L2H1 have L2H3: "staticReachableEnv e0 \<rho>\<^sub>l" by (blast dest: staticReachableVal.cases)

      with L1H3 local.App(4) have
        L2H1: "staticReachableVal e0 \<omega>\<^sub>a" by (blast dest: staticReachableEnv.cases)

      with L1H3 L2H3 local.App(2) local.App(3) have 
        L2H4: "staticReachableEnv e0 \<rho>l'" by (auto simp: staticReachableEnv.simps)

       with L2H2 show "staticReachableForward e0 el' \<and> staticReachableEnv e0 \<rho>l'" by simp
    qed

    show ?thesis using H1 L1H6 L1H7 local.Seq_Step_Up(1) staticReachablePool.simps by auto
  next
    case (BindMkChn \<pi> x e \<rho> \<kappa>)

    have
      L1H1: "staticReachableForward e0 (Bind x MkChn e)" and
      L1H2: "staticReachableEnv e0 \<rho>" and
      L1H3: "staticReachableStack e0 \<kappa>"
      using H1 local.BindMkChn(4) staticReachablePool.cases by blast+

    from L1H1 have
      L1H4: "staticReachableForward e0 e" using staticReachableForward.Bind by blast

    from L1H2 have
      L1H5: "staticReachableEnv e0 (\<rho>(x \<mapsto> VChn (Ch \<pi> x)))" using VChn staticReachableEnv.simps by auto

    show ?thesis using H1 L1H3 L1H4 L1H5 local.BindMkChn(1) staticReachablePool.simps by auto
  next
    case (BindSpawn \<pi> x e\<^sub>c e \<rho> \<kappa>)

    have
      L1H1: "staticReachableForward e0 (Bind x (Spwn e\<^sub>c) e)" and
      L1H2: "staticReachableEnv e0 \<rho>" and
      L1H3: "staticReachableStack e0 \<kappa>"
      using H1 local.BindSpawn(4) staticReachablePool.cases by blast+

    have
      L1H4: "staticReachableForward e0 e\<^sub>c" using H1 local.BindSpawn(4)
      using L1H1 staticReachableForward.BindSpawn_Child by blast

    have
      L1H5: "staticReachableForward e0 e"
      using L1H1 staticReachableForward.Bind by blast

    have
      L1H7: "staticReachableVal e0 VUnt" by (simp add: VUnt)

    have
      L1H9: "staticReachableEnv e0 (\<rho>(x \<mapsto> VUnt))" using L1H2 L1H7
      by (simp add: staticReachableEnv.simps)

    show ?thesis
      using H1 L1H2 L1H3 L1H4 L1H5 L1H9 local.BindSpawn(1) staticReachablePool.simps staticReachableStack.Empty by auto

  next
    case (BindSync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    have 
      L1H1: "staticReachableForward e0 (Bind x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r)" and
      L1H2: "staticReachableEnv e0 \<rho>\<^sub>r" and
      L1H3: "staticReachableStack e0 \<kappa>\<^sub>r"
      using H1 local.BindSync(7) staticReachablePool.cases by blast+

    have 
      L1H4: "staticReachableForward e0 e\<^sub>r"
      using L1H1 staticReachableForward.Bind by blast

    have 
      L1H5: "staticReachableForward e0 (Bind x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s)" and
      L1H6: "staticReachableEnv e0 \<rho>\<^sub>s" and
      L1H7: "staticReachableStack e0 \<kappa>\<^sub>s" 
      using H1 local.BindSync(4) staticReachablePool.cases by blast+

    from L1H6 local.BindSync(5) have 
      L1H8: "staticReachableVal e0 (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" using staticReachableEnv.cases by auto

    then have 
      L1H9: "staticReachableEnv e0 \<rho>\<^sub>s\<^sub>e"  using staticReachableVal.cases by blast

    from L1H9 local.BindSync(11) have 
      L1H10: "staticReachableVal e0 \<omega>\<^sub>m" using staticReachableEnv.cases by auto

    from L1H5 have 
      L1H11: "staticReachableForward e0 e\<^sub>s" using staticReachableForward.Bind by blast

    have 
      L1H12: "staticReachableVal e0 VUnt" by (simp add: VUnt)

    have 
      L1H13: "staticReachableEnv e0 (\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m))"
      using L1H2 L1H9 local.BindSync(11) staticReachableEnv.simps by auto

    have
      L1H14: "staticReachableEnv e0 (\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt))" using L1H6 L1H12
      by (simp add: staticReachableEnv.simps)

    show ?thesis
      using H1 L1H11 L1H13 L1H14 L1H4 local.BindSync(1) local.BindSync(4) local.BindSync(7) staticReachablePool.simps by auto
  qed
qed

lemma staticReachablePoolSound:
  "
  star dynamicEval (\<E>0, H0) (\<E>', H') \<Longrightarrow>
  \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<Longrightarrow>
  staticReachablePool e\<^sub>0 \<E>'
"
proof -
  assume 
    H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
    H3: "star dynamicEval (\<E>0, H0) (\<E>', H')"

  obtain X0 X' where
    H4: "X0 = (\<E>0, H0)" and 
    H5: "X' = (\<E>', H')" by simp

  from H3 H4 H5 have 
    H6: "star_left (op \<rightarrow>) X0 X'" by (simp add: star_implies_star_left)

  then have 
    H7:
  "
      \<forall> \<E>0 H0 \<E>' H' \<pi>' \<sigma>' .
      X0 = (\<E>0, H0) \<longrightarrow> X' = (\<E>', H') \<longrightarrow>
      \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
      staticReachablePool e\<^sub>0 \<E>'
    " 
  proof (induction)
    case (refl z)

    {
      fix \<E>0 H0 \<E>' H' \<pi>' \<sigma>'
      assume 
        L1H0: "z = (\<E>0, H0)" "z = (\<E>', H')" and
        L1H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]"
  
      have 
        L1H3: "staticReachableForward e\<^sub>0 e\<^sub>0" by (simp add: staticReachableForward.Refl)
      have 
        L1H4: "staticReachableEnv e\<^sub>0 Map.empty" by (simp add: staticReachableEnv_staticReachableVal.Intro)
      have 
        L1H5: "staticReachableStack e\<^sub>0 []" by (simp add: staticReachableStack.Empty)

      have
        "staticReachablePool e\<^sub>0 \<E>0"
       by (simp add: L1H1 L1H3 L1H4 L1H5 staticReachablePool.intros)
    }

    then show ?case by blast
  next
    case (step x y z)
    {
      fix \<E>0 H0 \<E>' H' \<pi>'
      assume 
        L1H0: "x = (\<E>0, H0)" "z = (\<E>', H')" and 
        L2H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]"


      obtain \<E> H where L2H3: "y = (\<E>, H)" by (meson surj_pair)
      from L1H0(1) L2H1 L2H3 step.IH have 
        L2H4: "staticReachablePool e\<^sub>0 \<E>" by blast

      have 
        "staticReachablePool e\<^sub>0 \<E>'"
        using L1H0(2) L2H3 L2H4 staticReachablePoolPreservedDynamicEval step.hyps(2) by blast

    } 

    then show ?case by blast
  qed

  show ?thesis by (simp add: H1 H4 H5 H7)
qed


theorem staticReachableSound:
"
      star dynamicEval ([[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
      \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
      staticReachable e\<^sub>0 e'
"
proof -
  assume 
    L1H1: "star dynamicEval ([[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>], {}) (\<E>', H')" and
    L1H2: "\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"

   show "staticReachable e\<^sub>0 e'" 
    using L1H1 L1H2
    using staticReachablePoolSound staticReachableForward_implies_staticReachable staticReachablePool.simps by auto
qed

end
