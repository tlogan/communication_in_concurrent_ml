theory Sound_Semantics
  imports Main Syntax Dynamic_Semantics Static_Semantics
    "~~/src/HOL/Library/List"
begin

inductive 
  static_eval_value :: "abstract_env \<times> abstract_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55) and  
  static_eval_env :: "abstract_env \<times> abstract_env \<Rightarrow> env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt
  " |

  Chan: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VChn c
  " |

  SendEvt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt _ _) \<rho>)
  " |

  RecvEvt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (RecvEvt _) \<rho>)
  " |

  Lft: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Lft _) \<rho>)
  " |

  Rght: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Rght _) \<rho>)
  " |

  Abs: "
    {^Abs f x e} \<subseteq> \<V> f \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Abs f x e) \<rho>)
  " |

  Pair: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Pair _ _) \<rho>)
  " |

  Intro: " 
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive static_eval_stack :: "abstract_env \<times> abstract_env \<Rightarrow> abstract_value set \<Rightarrow> contin list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> ((Ctn x e \<rho>) # \<kappa>)
  "


inductive static_eval_state :: "abstract_env \<times> abstract_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Intro: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive static_eval_pool :: "abstract_env \<times> abstract_env \<Rightarrow> trace_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Intro: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>) \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
  "

lemma static_eval_state_to_exp_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x;\<rho>;(Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>
"
proof -
  assume 
    "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x;\<rho>;(Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" 
  then have 
    "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>" by (simp add: static_eval_state.simps) then
  show 
    "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (rule static_eval_stack.cases; auto)
qed


lemma static_eval_state_to_exp_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l
"
proof -
  assume 
    H1: "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" and
    H2: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>"


  from H2 have 
    H3: "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" and
    H4: "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" using static_eval_state.cases by blast+

  from H4 have H5: "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" using static_eval_env.simps by auto

  from H1 H5 have 
    H6: "^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s" by fastforce

  from H3 show 
    "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l"
  proof cases
    case Let_Case 

    from H6 local.Let_Case(1) show 
      "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" by auto
  qed
qed


lemma static_eval_state_to_exp_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r
"
proof -
  assume "\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e"
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" 
    by (simp add: static_eval_state.simps)+ then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: static_eval_env.simps)
  with `\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)`
  have "^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s" by fastforce
  with `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r"
  proof cases
    case Let_Case 
    with 
      `\<forall>x\<^sub>r'. ^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r`  
      `^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by blast
  qed
qed


lemma static_eval_state_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x b e" by (simp add: static_eval_state.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (rule static_eval.cases; auto)
qed


lemma static_eval_state_to_exp_let_app: "
 (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
 \<rho> f = Some (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>') \<Longrightarrow>
 (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b
"

proof -
  assume "\<rho> f = Some (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>')"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps) then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: static_eval_env.simps)
  with `\<rho> f = Some (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>')`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>')" by simp then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b" by (rule static_eval_value.cases; auto)
qed

lemma static_eval_state_to_env_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
"
proof
 assume "\<rho> x = Some \<omega> "

 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (rule static_eval_state.cases; auto)+

 from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x = Some \<omega>`
 have "{|\<omega>|} \<subseteq> \<V> x" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: static_eval_env.simps)+

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
       
       show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)+
     qed
   } then

   show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
 qed
qed


lemma static_eval_state_to_stack_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "\<rho> x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>" by (simp add: static_eval_state.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (rule static_eval_stack.cases; auto)
qed


lemma static_eval_state_to_state_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "\<rho> x = Some \<omega>" "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)" by (blast intro: static_eval_state_to_env_result)

  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (blast intro: static_eval_state_to_exp_result)

  with `\<rho> x = Some \<omega>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Rslt x; \<rho>; (Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: static_eval_state_to_stack_result)
qed


lemma static_eval_state_to_env_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x Unt e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+ 

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x Unt e`
  have "{^Unt} \<subseteq> \<V> x" by (rule static_eval.cases; auto)+
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

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
    qed

  }
  with `{^Unt} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma static_eval_state_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
by (erule static_eval_state.cases; auto)

lemma static_eval_state_to_state_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> VUnt); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)" by (auto simp: static_eval_state_to_env_let_unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: static_eval_state_to_stack_let)

qed

lemma static_eval_to_value_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Prim p) e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr p \<rho>)
"
by (erule static_eval.cases; auto; rule; auto)

lemma static_eval_state_to_env_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VClsr p \<rho>))
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle> " then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Prim p) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+ then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr p \<rho>)" by (simp add: static_eval_to_value_let_prim)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Prim p) e`
  have "{^p} \<subseteq> \<V> x" by (rule static_eval.cases; auto)+
 
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
  
      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
    qed

  } then

  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> (VClsr p \<rho>))) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma static_eval_state_to_state_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> (VClsr p \<rho>)); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: static_eval_state_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VClsr p \<rho>))" by (auto simp: static_eval_state_to_env_let_prim)

qed


lemma static_eval_state_to_env_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
"

proof
  assume "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" by (blast intro: static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (blast intro: static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l" by (blast intro: static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)`
  have " | (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) | \<in> \<V> x\<^sub>s" by (blast intro: static_eval_env.cases) then
  have "^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  have "\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l"
  proof cases
    case Let_Case
    from `\<forall>x\<^sub>l'. ^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l`
    and `^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l" by simp
  qed

  from `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'` `\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l` 
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
   
  }
  with `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma static_eval_state_to_stack_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: static_eval_state.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)`
  have " | (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) | \<in> \<V> x\<^sub>s" by (blast intro: static_eval_env.cases) then
  have "^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  show "\<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x" 
  proof cases
    case Let_Case
    assume "\<forall>x\<^sub>l'. ^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l"
    with `^prim.Lft x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "\<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x" by blast
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: static_eval_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: static_eval_state_to_stack_let)
  
qed


lemma static_eval_state_to_state_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); (Ctn x e \<rho>) # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" by (simp add: static_eval_state_to_exp_let_case_left)

  assume "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)" by (simp add: static_eval_state_to_env_let_case_left)

  from `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>`
  and `\<rho> x\<^sub>s = Some (VClsr (Lft x\<^sub>l') \<rho>\<^sub>l)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>" by (simp add: static_eval_state_to_stack_let_case_left)
qed


lemma static_eval_state_to_env_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
"

proof
  assume "\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)" by (blast intro: static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (blast intro: static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r" by (blast intro: static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)`
  have " | (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r) | \<in> \<V> x\<^sub>s" by (blast intro: static_eval_env.cases) then
  have "^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  have "\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r"
  proof cases
    case Let_Case
    from `\<forall>x\<^sub>r'. ^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r`
    and `^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'` `\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r` 
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
   
  }
  with `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma static_eval_state_to_stack_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: static_eval_state.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)`
  have " | (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r) | \<in> \<V> x\<^sub>s" by (blast intro: static_eval_env.cases) then
  have "^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e`
  show "\<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x" 
  proof cases
    case Let_Case
    assume "\<forall>x\<^sub>r'. ^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r"
    with `^prim.Rght x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "\<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x" by blast
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: static_eval_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: static_eval_state_to_stack_let)
  
qed

lemma static_eval_state_to_state_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); (Ctn x e \<rho>) # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (simp add: static_eval_state_to_exp_let_case_right)

  assume "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)" by (simp add: static_eval_state_to_env_let_case_right)

  from `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e; \<rho>; \<kappa>\<rangle>`
  and `\<rho> x\<^sub>s = Some (VClsr (Rght x\<^sub>r') \<rho>\<^sub>r)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>" by (simp add: static_eval_state_to_stack_let_case_right)
qed


lemma static_eval_state_to_env_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
proof
  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Fst x\<^sub>p) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" by (blast intro: static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>1" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have " | (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) | \<in> \<V> x\<^sub>p" by (blast intro: static_eval_env.cases) then
  have "^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Fst x\<^sub>p) e`
  have "\<V> x\<^sub>1 \<subseteq> \<V> x"
  proof cases
    case Let_Fst
    from `\<forall>x\<^sub>1 x\<^sub>2. ^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x`
    and `^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p`
    show "\<V> x\<^sub>1 \<subseteq> \<V> x" by blast
  qed

  from `{|\<omega>|} \<subseteq> \<V> x\<^sub>1` `\<V> x\<^sub>1 \<subseteq> \<V> x` 
  have "{|\<omega>|} \<subseteq> \<V> x" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>'" "x' \<noteq> x" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
  }
  with `{|\<omega>|} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed



lemma static_eval_state_to_state_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: static_eval_state_to_exp_let)

  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)"  by (simp add: static_eval_state_to_env_let_fst)

  from `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)` and `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: static_eval_state_to_stack_let)
qed

lemma "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>"
sorry

lemma static_eval_state_to_env_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>) 
"
proof
  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Snd x\<^sub>p) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" by (blast intro: static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>2" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have " | (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) | \<in> \<V> x\<^sub>p" by (blast intro: static_eval_env.cases) then
  have "^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Snd x\<^sub>p) e`
  have "\<V> x\<^sub>2 \<subseteq> \<V> x"
  proof cases
    case Let_Snd
    from `\<forall>x\<^sub>1 x\<^sub>2. ^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x`
    and `^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p`
    show "\<V> x\<^sub>2 \<subseteq> \<V> x" by blast
  qed


  from `{|\<omega>|} \<subseteq> \<V> x\<^sub>2` `\<V> x\<^sub>2 \<subseteq> \<V> x` 
  have "{|\<omega>|} \<subseteq> \<V> x" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>'" "x' \<noteq> x" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
  }
  with \<open>{|\<omega>|} \<subseteq> \<V> x\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<close> 
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma static_eval_state_to_state_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: static_eval_state_to_exp_let)

  assume "\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)" by (simp add: static_eval_state_to_env_let_snd)

  from `\<rho> x\<^sub>p = Some (VClsr (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)` and `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: static_eval_state_to_stack_let)
qed


lemma static_eval_state_to_env_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l) \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)
"
proof
  assume "\<rho> f = Some (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)" "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (App f x\<^sub>a) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x\<^sub>a = Some \<omega>\<^sub>a`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a" by (blast intro: static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)`
  have "{|(VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)" by (blast intro: static_eval_env.cases)+

  from `{|(VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f`
  have "^Abs f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)`
  have "{|(VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f\<^sub>l" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (rule static_eval_value.cases; auto)+


  with `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (App f x\<^sub>a) e`
  have "\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l"
  proof cases
    case let_app
    assume "\<forall>f' x' e'. ^Abs f' x' e' \<in> \<V> f \<longrightarrow> \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x"
    with `^Abs f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f`
    show "\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l" by blast
  qed

  from `{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a` `\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l" by blast


  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" "x' \<noteq> f\<^sub>l" then
    have "\<rho>\<^sub>l x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
  }
  with \<open>{|(VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f\<^sub>l\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a\<close> \<open>{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l\<close>
  show "\<forall>x \<omega>. (\<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClsr (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto

qed

lemma static_eval_state_to_stack_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>') \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<Rrightarrow> (Ctn x e \<rho>) # \<kappa>
"
proof
  assume "\<rho> f = Some (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>')" and "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (App f x\<^sub>a) e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: static_eval_state.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some (VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>')`
  have " {|(VClsr (Abs f' x\<^sub>p e\<^sub>b) \<rho>')|} \<subseteq> \<V> f" by (blast intro: static_eval_env.cases) then
  have " ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (App f x\<^sub>a) e`
  show " \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> \<V> x"
  proof cases
    case let_app
    assume "\<forall>f' x' e'. ^Abs f' x' e' \<in> \<V> f \<longrightarrow> \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x"
    with `^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f`
    show " \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> \<V> x" by simp
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: static_eval_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (App f x\<^sub>a) e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: static_eval_state_to_stack_let)
qed


theorem static_eval_state_preserved_under_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>; 
    seq_step (b, \<rho>) \<omega>
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>" and
    H2: "seq_step (b, \<rho>) \<omega>"
    
  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>"
  proof cases
    case Let_Unit
    
    assume
      H3: "b = Unt" and
      H4: "\<omega> = VUnt"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x Unt e; \<rho>; \<kappa>\<rangle>" by simp

    then have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho> ++ [x \<mapsto> VUnt]; \<kappa>\<rangle>" by (simp add: static_eval_state_to_state_let_unit)
    
    with H4 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by simp
  next
    case (Let_Prim p)

    assume
      H3: "b = Prim p" and
      H4: "\<omega> = VClsr p \<rho>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Prim p) e; \<rho>; \<kappa>\<rangle>" by simp

    then have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho> ++ [x \<mapsto> VClsr p \<rho>]; \<kappa>\<rangle>" by (simp add: static_eval_state_to_state_let_prim)
    
    with H4 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by simp
  next
    case (Let_Fst x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)

    assume 
      H3: "b = (Fst x\<^sub>p)" and
      H4: "\<rho> x\<^sub>p = Some (VClsr (prim.Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and
      H5: "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Fst x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" by simp

    with H4 H5 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>" by (simp add: static_eval_state_to_state_let_fst)
  next
    case (Let_Snd x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)

    assume 
      H3: "b = (Snd x\<^sub>p)" and
      H4: "\<rho> x\<^sub>p = Some (VClsr (prim.Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and
      H5: "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Snd x\<^sub>p) e; \<rho>; \<kappa>\<rangle>" by simp

    with H4 H5 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>" by (simp add: static_eval_state_to_state_let_snd)
  qed
qed

theorem static_eval_state_preserved_under_step_up : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>;
    seq_step_up (b, \<rho>) (e', \<rho>')
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; (Ctn x e \<rho>) # \<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>" and
    H2: "seq_step_up (b, \<rho>) (e', \<rho>')"

  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; (Ctn x e \<rho>) # \<kappa>\<rangle>" 
  proof cases
    case (let_case_left xs xl' envl vl xl xr er)
    then show ?thesis
      using H1 static_eval_state_to_state_let_case_left by blast
    next
      case (let_case_right xs xr' envr vr xl el xr)
      then show ?thesis
        using H1 static_eval_state_to_state_let_case_right by blast
    next
      case (let_app f fp xp envl xa va)
      then show ?thesis
        using H1 static_eval_state.intros static_eval_state_to_env_let_app static_eval_state_to_exp_let_app static_eval_state_to_stack_let_app by auto
    qed
qed

theorem static_eval_state_preserved_under_step_down : "
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
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>" by (auto simp: static_eval_state_to_state_result)
qed

lemma static_eval_pool_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Let x b e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Let x b e; \<rho>; \<kappa>\<rangle>)" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>" by (simp add: static_eval_pool.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e " by (blast intro: static_eval_state_to_exp_let)
qed


lemma static_eval_pool_let_sync_send_values_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c)) \<Longrightarrow>
  {^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "{|(VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)|} \<subseteq> \<V> x\<^sub>s\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" by (blast intro: static_eval_env.cases)+

  from `{|(VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)|} \<subseteq> \<V> x\<^sub>s\<^sub>e`
  have "^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: static_eval_value.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))`
  have "{|(VChn (Ch \<pi>\<^sub>c x\<^sub>c))|} \<subseteq> \<V> x\<^sub>s\<^sub>c" by (blast intro: static_eval_env.cases) then
  have "{^Chan x\<^sub>c} \<subseteq> \<V> x\<^sub>s\<^sub>c" by simp then
  have "^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c" by auto
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s`
  show "{^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c"
  proof cases
    case Let_Sync
    assume "\<forall>x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c. ^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e \<longrightarrow> ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow> {^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c"
    with `^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e` and `^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c`
    show "{^Unt} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" by blast
  qed

qed

lemma static_eval_pool_let_sync_send_message_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  {|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: static_eval_state.simps)
  with `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" by (blast intro: static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: static_eval_value.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
  show "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" by (blast intro: static_eval_env.cases)
qed

lemma static_eval_pool_to_env_let_sync_send: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)
"
proof
  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)"
  and  "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: static_eval_state.simps)+

  have "{^Unt} \<subseteq> \<V> x\<^sub>s"
  proof (cases c)
    case (Ch \<pi> x\<^sub>c)
    assume "c = Ch \<pi> x\<^sub>c" 
    with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)`
    and  `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
    show "{^Unt} \<subseteq> \<V> x\<^sub>s" using static_eval_pool_let_sync_send_values_relate by simp
  qed
  
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt" by (simp add: Unit)
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>s" then
    have "\<rho>\<^sub>s x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
  }
  with \<open>{^Unt} \<subseteq> \<V> x\<^sub>s\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt\<close> 
  show "\<forall>x \<omega>. (\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by simp
qed


lemma static_eval_pool_let_sync_recv_values_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c)) \<Longrightarrow>
  \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
  have "{|(VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)|} \<subseteq> \<V> x\<^sub>r\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)" by (blast intro: static_eval_env.cases)+

  from `{|(VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)|} \<subseteq> \<V> x\<^sub>r\<^sub>e`
  have "^RecvEvt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r\<^sub>e" by (blast intro: static_eval_value.cases)
  with `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn (Ch \<pi>\<^sub>c x\<^sub>c))`
  have "{|(VChn (Ch \<pi>\<^sub>c x\<^sub>c))|} \<subseteq> \<V> x\<^sub>r\<^sub>c" by (blast intro: static_eval_env.cases) then
  have "{^Chan x\<^sub>c} \<subseteq> \<V> x\<^sub>r\<^sub>c" by simp then
  have "^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c" by auto
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r`
  show "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r"
  proof cases
    case Let_Sync
    assume "\<forall>x\<^sub>r\<^sub>c x\<^sub>c. ^RecvEvt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r"
    with `^RecvEvt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e` and `^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c`
    show "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" by blast
  qed
qed


lemma static_eval_pool_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Let x b e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Let x b e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e; \<rho>; \<kappa>\<rangle>" by (simp add: static_eval_pool.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: static_eval_state_to_stack_let)
qed

lemma static_eval_pool_to_env_let_sync_recv: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow> 
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m" then
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" using static_eval_pool_let_sync_send_message_relate by auto

  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: static_eval_state.simps)+


  have "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r"
  proof (cases c)
    case (Ch \<pi>\<^sub>c x\<^sub>c)
    assume "c = Ch \<pi>\<^sub>c x\<^sub>c" 

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
    have "\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" using \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)\<close> static_eval_pool_let_sync_send_values_relate by blast

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
    and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
    have "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" using  static_eval_pool_let_sync_recv_values_relate by auto

    from `\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c` and `\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r`
    show "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m` and `\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r`
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r" by blast

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: static_eval_state.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho>\<^sub>r x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
  }
  with `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m`
  show "\<forall>x \<omega>. (\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto
qed


lemma static_eval_preserved_under_sync: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)"


  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s" by (blast intro: static_eval_pool_to_exp_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)" by (blast intro: static_eval_pool_to_env_let_sync_send)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s" by (blast intro: static_eval_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>" by (blast intro: static_eval_state.intros)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (blast intro: static_eval_pool_to_exp_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
  and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)\<close> 
  and \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChn c)\<close>
  and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  and \<open>\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClsr (RecvEvt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)\<close> \<open>\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChn c)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)" by (blast intro: static_eval_pool_to_env_let_sync_recv)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r" by (blast intro: static_eval_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>" by (blast intro: static_eval_state.intros)

  {
    fix \<pi> \<sigma>
    assume  "\<pi> \<noteq> \<pi>\<^sub>s @ [LNxt x\<^sub>s]" and "\<pi> \<noteq> \<pi>\<^sub>r @ [LNxt x\<^sub>r]"
    and "(\<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma>" then
    have "\<E> \<pi> = Some \<sigma>" by simp
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (blast intro: static_eval_pool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r (x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s (x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>`
  show "\<forall>\<pi> \<sigma>. (\<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by simp

qed


lemma static_eval_pool_to_env_let_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChn (Ch \<pi> x)))
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>" by (blast intro: static_eval_pool.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x MkChn e" by (blast intro: static_eval_state.cases) then
  have "{^Chan x} \<subseteq> \<V> x"  by (blast intro: static_eval.cases)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VChn (Ch \<pi> x))" by (simp add: Chan)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>` 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> (VChn (Ch \<pi> x)))) x' = Some \<omega>'" and "x \<noteq> x'"then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: static_eval_env.simps)
  } with `{^Chan x} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VChn (Ch \<pi> x))`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> (VChn (Ch \<pi> x)))) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma static_eval_preserved_under_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e; \<rho>(x \<mapsto> (VChn (Ch \<pi> x))); \<kappa>\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: static_eval_pool_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChn (Ch \<pi> x)))" by (blast intro: static_eval_pool_to_env_let_chan )

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Let x MkChn e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: static_eval_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChn (Ch \<pi> x)))` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>" by (blast intro: static_eval_state.intros)
  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some \<sigma>'" 
    and "\<pi>' \<noteq> \<pi> @ [LNxt x]" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: static_eval_pool.simps)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChn (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


lemma static_eval_pool_to_env_let_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Spwn e\<^sub>c) e" by (blast intro: static_eval_state.cases) then
  have "{^Unt} \<subseteq> \<V> x"  by (blast intro: static_eval.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt" by (simp add: Unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>'" and "x \<noteq> x'" then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (blast intro: static_eval_env.cases)
  } with `{^Unt} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnt`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> VUnt)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed

lemma static_eval_preserved_under_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e; \<rho>(x \<mapsto> VUnt); \<kappa>\<rangle>, \<pi>@ [LSpawn x] \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: static_eval_pool_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)" by (blast intro: static_eval_pool_to_env_let_spawn)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: static_eval_pool_to_stack_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnt)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<close>
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>" by (simp add: static_eval_state.intros)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x (Spwn e\<^sub>c) e; \<rho>; \<kappa>\<rangle>" by (simp add: static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Spwn e\<^sub>c) e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e Let x (Spwn e\<^sub>c) e`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c" by (blast intro: static_eval.cases)

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []" by (simp add: static_eval_stack.Empty)
  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>" by (simp add: static_eval_state.intros)

  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>, \<pi> @ [LSpawn x] \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>'"
    and "\<pi>' \<noteq> \<pi> @ [LNxt x]" and " \<pi>' \<noteq> \<pi> @ [LSpawn x]" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (blast intro: static_eval_pool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>, \<pi> @ [LSpawn x] \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


theorem static_eval_preserved_under_concur_step : "
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

    have L1H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LRtn x\<^sub>\<kappa>] \<mapsto> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>);\<kappa>\<rangle>)"
      using H1 local.Seq_Step_Down(4) local.Seq_Step_Down(5) static_eval_pool.simps static_eval_state_to_state_result by fastforce

    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H1 local.Seq_Step_Down(1))
  next
    case (Seq_Step \<pi> x b e \<rho> \<kappa> \<omega>)

    have L1H7:"(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>Let x b e;\<rho>;\<kappa>\<rangle>"
      using H1 local.Seq_Step(4) static_eval_pool.simps by auto

    have L1H8: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>"
      using L1H7 local.Seq_Step(5) static_eval_state_preserved_under_step by blast

    have L1H9: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LNxt x] \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>)"
      using H1 L1H8 static_eval_pool.simps by auto

    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H9 local.Seq_Step(1))
  next
    case (Seq_Step_Up \<pi> x b e \<rho> \<kappa> e' \<rho>')
    have L1H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> @ [LCall x] \<mapsto> \<langle>e';\<rho>';(Ctn x e \<rho>) # \<kappa>\<rangle>)"
      using H1 local.Seq_Step_Up(4) local.Seq_Step_Up(5) static_eval_pool.simps static_eval_state_preserved_under_step_up by fastforce
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H1 local.Seq_Step_Up(1))
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)
    show ?thesis
      by (simp add: H1 local.Let_Chan(1) local.Let_Chan(4) static_eval_preserved_under_chan)
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    show ?thesis
      by (simp add: H1 local.Let_Spawn(1) local.Let_Spawn(4) static_eval_preserved_under_spawn)
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)
    have L1H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s @ [LNxt x\<^sub>s] \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r @ [LNxt x\<^sub>r] \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)" 
      by (simp add: H1 local.Let_Sync(10) local.Let_Sync(11) local.Let_Sync(4) local.Let_Sync(5) local.Let_Sync(7) local.Let_Sync(8) local.Let_Sync(9) static_eval_preserved_under_sync)
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
      by (simp add: L1H1 local.Let_Sync(1))
  qed
qed


theorem static_eval_preserved_under_concur_step_star : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;  
    star concur_step (\<E>, H) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and 
    H2: "star concur_step (\<E>, H) (\<E>', H')"

  obtain X X' where H3: "X = (\<E>, H)" and H4: "X' = (\<E>', H')" by simp
  
  from H2 H3 H4 have H5: "star concur_step X X'" by simp
 
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
      by (metis eq_fst_iff static_eval_preserved_under_concur_step step.IH step.hyps(1))
    }
    
    then show ?case by blast
  qed 

  from H1 H3 H4 H6
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
qed


theorem trace_pool_snapshot_not_static_bound_sound : "
  \<rho> x = Some \<omega> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>  
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho> x = Some \<omega>"

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)" then

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>" by (simp add: static_eval_pool.simps) then

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: static_eval_state.simps) 
  with `\<rho> x = Some \<omega>`

  show "{|\<omega>|} \<subseteq> \<V> x" by (simp add: static_eval_env.simps)
qed

theorem trace_pool_always_not_static_bound_sound : "
  \<rho>' x = Some \<omega> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> 
  star concur_step (\<E>, H) (\<E>', H') \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume 
    H1: "\<rho>' x = Some \<omega>" and
    H2: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and 
    H3: "star concur_step (\<E>, H) (\<E>', H')" and 
    H4: "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)"

  from H2 H3
  have H5: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by (blast intro: static_eval_preserved_under_concur_step_star)

  from H1 H4 H5
  show "{|\<omega>|} \<subseteq> \<V> x" using trace_pool_snapshot_not_static_bound_sound by auto
qed


lemma static_eval_to_pool: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e"

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty" by (simp add: static_eval_value_static_eval_env.Intro)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []" by (simp add: static_eval_stack.Empty)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>" by (simp add: static_eval_state.intros)

  have "[[] \<mapsto> \<langle>e; empty; []\<rangle>] [] = Some (\<langle>e; empty; []\<rangle>)" by simp
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: static_eval_pool.intros)
qed



inductive static_reachable_left :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  Refl : "
    static_reachable_left e0 e0
  " | 
  Let_Spawn_Child: "
    static_reachable_left e0 (Let x (Spwn e\<^sub>c) e\<^sub>n) \<Longrightarrow>
    static_reachable_left e0 e\<^sub>c
  " |
  let_case_left: "
    static_reachable_left e0 (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) \<Longrightarrow>
    static_reachable_left e0 e\<^sub>l
  " |
  let_case_right: "
    static_reachable_left e0 (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) \<Longrightarrow>
    static_reachable_left e0 e\<^sub>r
  " |
  Let_Abs_Body: "
    static_reachable_left e0 (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e\<^sub>n) \<Longrightarrow>
    static_reachable_left e0 e\<^sub>b
  " | 
  Let: "
    static_reachable_left e0 (Let x b e\<^sub>n) \<Longrightarrow>
    static_reachable_left e0 e\<^sub>n
  "


lemma static_reachable_trans: "
  static_reachable e\<^sub>z e\<^sub>y \<Longrightarrow> static_reachable e\<^sub>y e\<^sub>x \<Longrightarrow> static_reachable e\<^sub>z e\<^sub>x
"
proof -
  assume "static_reachable e\<^sub>y e\<^sub>x "
  assume "static_reachable e\<^sub>z e\<^sub>y" then
  have "(\<forall> e\<^sub>x . static_reachable e\<^sub>y e\<^sub>x \<longrightarrow> static_reachable e\<^sub>z e\<^sub>x)"
  proof (induction rule: static_reachable.induct)
    case (Refl e)
    show "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e e\<^sub>x" by simp
  next
    case (Let e\<^sub>n e x b)
    assume "static_reachable e\<^sub>n e" "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>n e\<^sub>x"

    have "\<forall>e\<^sub>x. static_reachable e\<^sub>n e\<^sub>x \<longrightarrow> static_reachable (Let x b e\<^sub>n) e\<^sub>x" by (simp add: static_reachable.Let) 
    with `\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>n e\<^sub>x`
    show "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable (Let x b e\<^sub>n) e\<^sub>x" by blast
  next
    case (Let_Spawn_Child e\<^sub>c e x e\<^sub>n)
    assume "static_reachable e\<^sub>c e" "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>c e\<^sub>x"

    have "\<forall>e\<^sub>x. static_reachable e\<^sub>c e\<^sub>x \<longrightarrow> static_reachable (Let x (Spwn e\<^sub>c) e\<^sub>n) e\<^sub>x" by (simp add: static_reachable.Let_Spawn_Child)
    with `\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>c e\<^sub>x`
    show "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable (Let x (Spwn e\<^sub>c) e\<^sub>n) e\<^sub>x"by blast
  next
    case (let_case_left e\<^sub>l e x x\<^sub>s x\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    assume "static_reachable e\<^sub>l e" "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>l e\<^sub>x"

    have "\<forall>e\<^sub>x. static_reachable e\<^sub>l e\<^sub>x \<longrightarrow> static_reachable (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by (simp add: static_reachable.let_case_left)
    with `\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>l e\<^sub>x`
    show "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by blast
  next
    case (let_case_right e\<^sub>r e x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>n)
    assume "static_reachable e\<^sub>r e" "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>r e\<^sub>x"

    have "\<forall>e\<^sub>x. static_reachable e\<^sub>r e\<^sub>x \<longrightarrow> static_reachable (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by (simp add: static_reachable.let_case_right)
    with `\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>r e\<^sub>x`
    show "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e\<^sub>x" by blast
  next
    case (Let_Abs_Body e\<^sub>b e x f x\<^sub>p e\<^sub>n)
    assume "static_reachable e\<^sub>b e" "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>b e\<^sub>x"

    have "\<forall>e\<^sub>x. static_reachable e\<^sub>b e\<^sub>x \<longrightarrow> static_reachable (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e\<^sub>n) e\<^sub>x" by (simp add: static_reachable.Let_Abs_Body)
    with `\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable e\<^sub>b e\<^sub>x`
    show "\<forall>e\<^sub>x. static_reachable e e\<^sub>x \<longrightarrow> static_reachable (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e\<^sub>n) e\<^sub>x" by blast
  qed 
  with `static_reachable e\<^sub>y e\<^sub>x`
  show "static_reachable e\<^sub>z e\<^sub>x" by blast
qed


lemma static_reachable_left_implies_static_reachable: "
  static_reachable_left e e' \<Longrightarrow> static_reachable e e'
"
proof -
  assume "static_reachable_left e e'"
  
  then show "static_reachable e e'"
  proof induction
    case (Refl e0)
    show 
      "static_reachable e0 e0" by (simp add: static_reachable.Refl)
  next
    case (Let_Spawn_Child e0 x e\<^sub>c e\<^sub>n)
    from Let_Spawn_Child.IH show 
      "static_reachable e0 e\<^sub>c"
    using static_reachable.Let_Spawn_Child static_reachable.Refl static_reachable_trans by blast
  next
    case (let_case_left e0 x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    from let_case_left.IH show
      "static_reachable e0 e\<^sub>l"
    using static_reachable.let_case_left static_reachable.Refl static_reachable_trans by blast
  next
    case (let_case_right e0 x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    from let_case_right.IH show 
      "static_reachable e0 e\<^sub>r"
    using static_reachable.let_case_right static_reachable.Refl static_reachable_trans by blast
  next
    case (Let_Abs_Body e0 x f x\<^sub>p e\<^sub>b e\<^sub>n)
    from Let_Abs_Body.IH show 
      "static_reachable e0 e\<^sub>b"
    using static_reachable.Let_Abs_Body static_reachable.Refl static_reachable_trans by blast
  next
    case (Let e0 x b e\<^sub>n)
    from Let.IH show
      "static_reachable e0 e\<^sub>n"
    using static_reachable.Let static_reachable.Refl static_reachable_trans by blast
  qed
qed


inductive static_reachable_over_prim :: "exp \<Rightarrow> prim \<Rightarrow> bool" where
  SendEvt: "
    static_reachable_over_prim e0 (SendEvt xC xM)
  " |
  RecvEvt: "
    static_reachable_over_prim e0 (RecvEvt xC)
  " |
  Pair: "
    static_reachable_over_prim e0 (Pair x1 x2)
  " |
  Lft: "
    static_reachable_over_prim e0 (Lft x)
  " |
  Rght: "
    static_reachable_over_prim e0 (Rght x)
  " |
  Abs: "
    static_reachable_left e0 e\<^sub>b \<Longrightarrow>
    static_reachable_over_prim e0 (Abs f\<^sub>p x\<^sub>p e\<^sub>b)
  " 

inductive 
  static_reachable_over_env :: "exp \<Rightarrow> env \<Rightarrow> bool" and
  static_reachable_over_val :: "exp \<Rightarrow> val \<Rightarrow> bool"
where
  VUnt: "
    static_reachable_over_val e0 VUnt
  " |
  VChn: "
    static_reachable_over_val e0 (VChn c)
  " |
  VClsr: "
    static_reachable_over_prim e0 p \<Longrightarrow>
    static_reachable_over_env e0 \<rho>' \<Longrightarrow>
    static_reachable_over_val e0 (VClsr p \<rho>')
  " |

  Intro: "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow> static_reachable_over_val e0 \<omega> \<Longrightarrow>
    static_reachable_over_env e0 \<rho>
  "

inductive static_reachable_over_stack :: "exp \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty: "
    static_reachable_over_stack e0 []
  " |
  Nonempty: "
    static_reachable_left e0 e\<^sub>\<kappa> \<Longrightarrow>
    static_reachable_over_env e0 \<rho>\<^sub>\<kappa> \<Longrightarrow>
    static_reachable_over_stack e0 \<kappa> \<Longrightarrow>
    static_reachable_over_stack e0 ((Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>)
  "

inductive static_reachable_over_state :: "exp \<Rightarrow> state \<Rightarrow> bool" where
  Intro: "
    static_reachable_left e0 e \<Longrightarrow>
    static_reachable_over_env e0 \<rho> \<Longrightarrow>
    static_reachable_over_stack e0 \<kappa> \<Longrightarrow>
    static_reachable_over_state e0 (\<langle>e;\<rho>;\<kappa>\<rangle>)
  "

lemma static_reachable_over_state_preserved: "
  concur_step (E, H) (E', H') \<Longrightarrow>
  \<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> static_reachable_over_state e\<^sub>0 \<sigma> \<Longrightarrow>
  E' \<pi>' = Some \<sigma>' \<Longrightarrow>
  static_reachable_over_state e\<^sub>0 \<sigma>'
"
proof -
  assume
    H1: "\<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> static_reachable_over_state e\<^sub>0 \<sigma>" and
    H2: "E' \<pi>' = Some \<sigma>'" and
    H3: "concur_step (E, H) (E', H')"

  from H3 show "static_reachable_over_state e\<^sub>0 \<sigma>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    from H1 local.Seq_Step_Down(4)
    have L1H1: "static_reachable_over_state e\<^sub>0 (\<langle>Rslt x;\<rho>;(Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>\<rangle>)" by blast

    then have 
      L1H2: "static_reachable_over_env e\<^sub>0 \<rho>" and 
      L1H3: "static_reachable_over_stack e\<^sub>0 ((Ctn x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa>) # \<kappa>)" by (blast dest: static_reachable_over_state.cases)+

    then have 
      L1H4: "static_reachable_left e\<^sub>0 e\<^sub>\<kappa>" and 
      L1H5: "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>\<kappa>" and 
      L1H6: "static_reachable_over_stack e\<^sub>0 \<kappa>" by (blast dest: static_reachable_over_stack.cases)+

    from L1H2 L1H5 local.Seq_Step_Down(5) have L1H7: "static_reachable_over_env e\<^sub>0 (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>))"
      by (smt static_reachable_over_env.cases static_reachable_over_env_static_reachable_over_val.Intro map_upd_Some_unfold)

    with L1H4 L1H6 L1H7 have L1H8: "static_reachable_over_state e\<^sub>0 (\<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>);\<kappa>\<rangle>)"
      by (simp add: static_reachable_over_state.intros)

    with H1 H2 local.Seq_Step_Down(1) show "static_reachable_over_state e\<^sub>0 \<sigma>'"
      by (metis map_upd_Some_unfold)
  next
    case (Seq_Step \<pi> x b el \<rho>l \<kappa>l \<omega>)

    from H1 local.Seq_Step(4) 
    have L1H1: "static_reachable_over_state e\<^sub>0 (\<langle>Let x b el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      L1H2: "static_reachable_left e\<^sub>0 (Let x b el)" and
      L1H3: "static_reachable_over_env e\<^sub>0 \<rho>l" and
      L1H4: "static_reachable_over_stack e\<^sub>0 \<kappa>l" by (blast dest: static_reachable_over_state.cases)+

    from L1H2 have L1H5: "static_reachable_left e\<^sub>0 el" by (blast dest: static_reachable_left.Let)

    from local.Seq_Step(5) have 
      "static_reachable_over_val e\<^sub>0 \<omega>"
    proof cases
      case Let_Unit
      then show "static_reachable_over_val e\<^sub>0 \<omega>" by (simp add: VUnt)
    next
      case (Let_Prim p)

      have L2H1: "static_reachable_over_prim e\<^sub>0 p"
      proof (cases p)
        case (SendEvt x11 x12)
        then show "static_reachable_over_prim e\<^sub>0 p" by (simp add: static_reachable_over_prim.SendEvt)
      next
        case (RecvEvt x2)
        then show "static_reachable_over_prim e\<^sub>0 p" by (simp add: static_reachable_over_prim.RecvEvt)
      next
        case (Pair x31 x32)
        then show "static_reachable_over_prim e\<^sub>0 p" by (simp add: static_reachable_over_prim.Pair)
      next
        case (Lft x4)
        then show "static_reachable_over_prim e\<^sub>0 p" by (simp add: static_reachable_over_prim.Lft)
      next
        case (Rght x5)
        then show "static_reachable_over_prim e\<^sub>0 p" by (simp add: static_reachable_over_prim.Rght)
      next
        case (Abs x61 x62 x63)

        with L1H2 local.Let_Prim(1) local.Abs
        show "static_reachable_over_prim e\<^sub>0 p" by (smt static_reachable_left.Let_Abs_Body static_reachable_over_prim.Abs )
      qed

      have L2H3: "static_reachable_over_env e\<^sub>0 \<rho>l" by (simp add: L1H3)

      with L2H1 have "static_reachable_over_val e\<^sub>0 (VClsr p \<rho>l)" by (simp add: VClsr)

      with local.Let_Prim(2) show "static_reachable_over_val e\<^sub>0 \<omega>" by simp
    next
      case (Let_Fst x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)
      then show "static_reachable_over_val e\<^sub>0 \<omega>"
        by (metis L1H3 static_reachable_over_env.cases static_reachable_over_val.cases val.distinct(3) val.distinct(5) val.inject(2))
    next
      case (Let_Snd x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)
      then show "static_reachable_over_val e\<^sub>0 \<omega>"
        by (metis L1H3 static_reachable_over_env.cases static_reachable_over_val.cases val.distinct(3) val.distinct(5) val.inject(2))
    qed
    
    with L1H3 have L1H6: "static_reachable_over_env e\<^sub>0 (\<rho>l(x \<mapsto> \<omega>))"
      by (smt static_reachable_over_env.cases static_reachable_over_env_static_reachable_over_val.Intro map_upd_Some_unfold)

    with L1H4 L1H5 have L1H7: "static_reachable_over_state e\<^sub>0 (\<langle>el;\<rho>l(x \<mapsto> \<omega>);\<kappa>l\<rangle>)" by (simp add: static_reachable_over_state.intros)
   
    with H1 H2 local.Seq_Step(1) show "static_reachable_over_state e\<^sub>0 \<sigma>'"
      by (metis map_upd_Some_unfold)
  next
    case (Seq_Step_Up \<pi> x b el \<rho>l \<kappa>l el' \<rho>l')

    from H1 local.Seq_Step_Up(4) have 
      L1H1: "static_reachable_over_state e\<^sub>0 (\<langle>Let x b el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      L1H2: "static_reachable_left e\<^sub>0 (Let x b el)" and
      L1H3: "static_reachable_over_env e\<^sub>0 \<rho>l" and
      L1H4: "static_reachable_over_stack e\<^sub>0 \<kappa>l" by (blast dest: static_reachable_over_state.cases)+

    from L1H2 have 
      L1H5: "static_reachable_left e\<^sub>0 el" by (blast dest: static_reachable_left.Let)

    from L1H3 L1H4 L1H5 have 
      L1H6: "static_reachable_over_stack e\<^sub>0 ((Ctn x el \<rho>l) # \<kappa>l)" 
        by (simp add: static_reachable_over_stack.Nonempty)

    from local.Seq_Step_Up(5)
    have 
      L1H7: "static_reachable_left e\<^sub>0 el' \<and> static_reachable_over_env e\<^sub>0 \<rho>l'"
    proof cases
      case (let_case_left x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)

      from L1H2 local.let_case_left(1) have 
        L2H1: "static_reachable_left e\<^sub>0 el'" by (blast dest: static_reachable_left.let_case_left)

      from L1H3 local.let_case_left(3) have 
        "static_reachable_over_val e\<^sub>0 (VClsr (prim.Lft x\<^sub>l') \<rho>\<^sub>l)"
        by (blast dest: static_reachable_over_env.cases)

      then have "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>l" by (blast dest: static_reachable_over_val.cases)

      with local.let_case_left(4) have "static_reachable_over_val e\<^sub>0 \<omega>\<^sub>l" by (blast dest: static_reachable_over_env.cases)

      with L1H3 have "static_reachable_over_env e\<^sub>0 (\<rho>l(x\<^sub>l \<mapsto> \<omega>\<^sub>l))"
        by (smt static_reachable_over_env.cases static_reachable_over_env_static_reachable_over_val.Intro map_upd_Some_unfold)

      with local.let_case_left(2) have 
        L2H2: "static_reachable_over_env e\<^sub>0 \<rho>l'" by simp

      with L2H1 show "static_reachable_left e\<^sub>0 el' \<and> static_reachable_over_env e\<^sub>0 \<rho>l'" by simp
    next
      case (let_case_right x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)

      from L1H2 local.let_case_right(1) have 
        L2H1: "static_reachable_left e\<^sub>0 el'"
          by (blast dest: static_reachable_left.let_case_right)

      from L1H3 local.let_case_right(3)
      have "static_reachable_over_val e\<^sub>0 (VClsr (prim.Rght x\<^sub>r') \<rho>\<^sub>r)"
        by (blast dest: static_reachable_over_env.cases)

      then have "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>r" by (blast dest: static_reachable_over_val.cases)

      with L1H3 local.let_case_right(2) local.let_case_right(4) have 
        L2H2: "static_reachable_over_env e\<^sub>0 \<rho>l'"
          by (auto simp: static_reachable_over_env.simps)

      with L2H1 show "static_reachable_left e\<^sub>0 el' \<and> static_reachable_over_env e\<^sub>0 \<rho>l'" by simp
    next
      case (let_app f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a)

      from L1H3 local.let_app(3) have
        L2H1: "static_reachable_over_val e\<^sub>0 (VClsr (Abs f\<^sub>l x\<^sub>l el') \<rho>\<^sub>l)" by (blast dest: static_reachable_over_env.cases)

      then have 
        "static_reachable_over_prim e\<^sub>0 (Abs f\<^sub>l x\<^sub>l el')" by (blast dest: static_reachable_over_val.cases)

      then have L2H2: "static_reachable_left e\<^sub>0 el'" by (blast dest: static_reachable_over_prim.cases)

      from L2H1 have L2H3: "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>l" by (blast dest: static_reachable_over_val.cases)

      with L1H3 local.let_app(4) have
        L2H1: "static_reachable_over_val e\<^sub>0 \<omega>\<^sub>a" by (blast dest: static_reachable_over_env.cases)

      with L1H3 L2H3 local.let_app(2) local.let_app(3) have 
        L2H4: "static_reachable_over_env e\<^sub>0 \<rho>l'" by (auto simp: static_reachable_over_env.simps)

       with L2H2 show "static_reachable_left e\<^sub>0 el' \<and> static_reachable_over_env e\<^sub>0 \<rho>l'" by simp
    qed

    with L1H6 have "static_reachable_over_state e\<^sub>0 (\<langle>el';\<rho>l';(Ctn x el \<rho>l) # \<kappa>l\<rangle>)" by (simp add: static_reachable_over_state.intros)

    with H1 H2 local.Seq_Step_Up(1) show 
      "static_reachable_over_state e\<^sub>0 \<sigma>'"
      by (metis fun_upd_apply option.sel)
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)

    from H1 local.Let_Chan(4) have 
      "static_reachable_over_state e\<^sub>0 (\<langle>Let x MkChn e;\<rho>;\<kappa>\<rangle>)" by simp

    then have
      L1H1: "static_reachable_left e\<^sub>0 (Let x MkChn e)" and
      L1H2: "static_reachable_over_env e\<^sub>0 \<rho>" and
      L1H3: "static_reachable_over_stack e\<^sub>0 \<kappa>" using static_reachable_over_state.cases by blast+

    from L1H1 have
      L1H4: "static_reachable_left e\<^sub>0 e" using static_reachable_left.Let by blast

    from L1H2 have
      L1H5: "static_reachable_over_env e\<^sub>0 (\<rho>(x \<mapsto> VChn (Ch \<pi> x)))" using VChn static_reachable_over_env.simps by auto

    from L1H4 L1H5 L1H3 have
      "static_reachable_over_state e\<^sub>0 (\<langle>e;\<rho> ++ [x \<mapsto> VChn (Ch \<pi> x)];\<kappa>\<rangle>)" using static_reachable_over_state.intros by simp

    with H1 H2 local.Let_Chan(1) show
      "static_reachable_over_state e\<^sub>0 \<sigma>'" by (metis fun_upd_other fun_upd_same map_add_empty map_add_upd option.sel)
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)

    from H1 local.Let_Spawn(4) have
      "static_reachable_over_state e\<^sub>0 (\<langle>Let x (Spwn e\<^sub>c) e;\<rho>;\<kappa>\<rangle>)" by blast

    then have
      L1H1: "static_reachable_left e\<^sub>0 (Let x (Spwn e\<^sub>c) e)" and
      L1H2: "static_reachable_over_env e\<^sub>0 \<rho>" and
      L1H3: "static_reachable_over_stack e\<^sub>0 \<kappa>" using static_reachable_over_state.cases by blast+

    from L1H1 have
      L1H4: "static_reachable_left e\<^sub>0 e\<^sub>c" using static_reachable_left.Let_Spawn_Child by blast

    from L1H1 have
      L1H5: "static_reachable_left e\<^sub>0 e" using static_reachable_left.Let by blast

    from L1H2 L1H4 have
      L1H6: "static_reachable_over_state e\<^sub>0 (\<langle>e\<^sub>c;\<rho>;[]\<rangle>)" by (simp add: static_reachable_over_stack.Empty static_reachable_over_state.intros)

    have
      L1H7: "static_reachable_over_val e\<^sub>0 VUnt" by (simp add: VUnt)

    from L1H2 L1H3 L1H5 L1H7 have
      L1H8: "static_reachable_over_state e\<^sub>0 (\<langle>e;\<rho>(x \<mapsto> VUnt);\<kappa>\<rangle>)" by (simp add:static_reachable_over_env.simps static_reachable_over_state.intros)
   
    from H1 H2 L1H6 L1H8 local.Let_Spawn(1) show
      "static_reachable_over_state e\<^sub>0 \<sigma>'" by (smt fun_upd_apply map_add_empty map_add_upd option.sel)

  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    from H1 local.Let_Sync(7) have 
      "static_reachable_over_state e\<^sub>0 (\<langle>Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)" by blast

    then have 
      L1H1: "static_reachable_left e\<^sub>0 (Let x\<^sub>r (Sync x\<^sub>r\<^sub>e) e\<^sub>r)" and
      L1H2: "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>r" and
      L1H3: "static_reachable_over_stack e\<^sub>0 \<kappa>\<^sub>r" using static_reachable_over_state.cases by blast+

    have 
      L1H4: "static_reachable_left e\<^sub>0 e\<^sub>r"
      using L1H1 static_reachable_left.Let by blast

    from H1 local.Let_Sync(4) have 
      "static_reachable_over_state e\<^sub>0 (\<langle>Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)" by blast

    then have 
      L1H5: "static_reachable_left e\<^sub>0 (Let x\<^sub>s (Sync x\<^sub>s\<^sub>e) e\<^sub>s)" and
      L1H6: "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>s" and
      L1H7: "static_reachable_over_stack e\<^sub>0 \<kappa>\<^sub>s" using static_reachable_over_state.cases by blast+

    from L1H6 local.Let_Sync(5) have 
      L1H8: "static_reachable_over_val e\<^sub>0 (VClsr (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" using static_reachable_over_env.cases by auto

    then have 
      L1H9: "static_reachable_over_env e\<^sub>0 \<rho>\<^sub>s\<^sub>e"  using static_reachable_over_val.cases by blast

    from L1H9 local.Let_Sync(11) have 
      L1H10: "static_reachable_over_val e\<^sub>0 \<omega>\<^sub>m" using static_reachable_over_env.cases by auto

    from L1H5 have 
      L1H11: "static_reachable_left e\<^sub>0 e\<^sub>s" using static_reachable_left.Let by blast

    have 
      L1H12: "static_reachable_over_val e\<^sub>0 VUnt" by (simp add: VUnt)

    from L1H2 L1H3 L1H4 L1H10 L1H12 have 
      L1H13: "static_reachable_over_state e\<^sub>0 (\<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)" by (simp add: static_reachable_over_env.simps static_reachable_over_state.intros)

    from L1H6 L1H7 L1H11 L1H12 have 
      L1H14: "static_reachable_over_state e\<^sub>0 (\<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnt);\<kappa>\<^sub>s\<rangle>)" by (simp add: static_reachable_over_env.simps static_reachable_over_state.intros)

    from H1 H2 L1H13 L1H14 local.Let_Sync(1) show 
      "static_reachable_over_state e\<^sub>0 \<sigma>'" by (smt fun_upd_apply map_add_empty map_add_upd option.sel)

  qed
qed

lemma state_always_exp_not_static_reachable_sound: "
  star concur_step (\<E>0, H0) (\<E>', H') \<Longrightarrow>
  \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<Longrightarrow>
  \<E>' \<pi>' = Some \<sigma>' \<Longrightarrow>
  static_reachable_over_state e\<^sub>0 \<sigma>'
"
proof -
  assume 
    H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and 
    H2: "\<E>' \<pi>' = Some \<sigma>'" and
    H3: "star concur_step (\<E>0, H0) (\<E>', H')"

  obtain X0 X' where
    H4: "X0 = (\<E>0, H0)" and 
    H5: "X' = (\<E>', H')" by simp

  from H3 H4 H5 have 
    H6: "star_left (op \<rightarrow>) X0 X'" by (simp add: star_implies_star_left)

  then have 
    H7: "
      \<forall> \<E>0 H0 \<E>' H' \<pi>' \<sigma>' .
      X0 = (\<E>0, H0) \<longrightarrow> X' = (\<E>', H') \<longrightarrow>
      \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
      \<E>' \<pi>' = Some \<sigma>' \<longrightarrow>
      static_reachable_over_state e\<^sub>0 \<sigma>'
    " 
  proof (induction)
    case (refl z)

    {
      fix \<E>0 H0 \<E>' H' \<pi>' \<sigma>'
      assume 
        L1H0: "z = (\<E>0, H0)" "z = (\<E>', H')" and
        L1H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
        L1H2:  "\<E>0 \<pi>' = Some \<sigma>'"
  
      have 
        L1H3: "static_reachable_left e\<^sub>0 e\<^sub>0" by (simp add: static_reachable_left.Refl)
      have 
        L1H4: "static_reachable_over_env e\<^sub>0 Map.empty" by (simp add: static_reachable_over_env_static_reachable_over_val.Intro)
      have 
        L1H5: "static_reachable_over_stack e\<^sub>0 []" by (simp add: static_reachable_over_stack.Empty)

      from L1H3 L1H4 L1H5 have 
        L1H6: "static_reachable_over_state e\<^sub>0 (\<langle>e\<^sub>0;Map.empty;[]\<rangle>)" by (simp add: static_reachable_over_state.intros)

     from L1H1 L1H2 L1H6 have
        "static_reachable_over_state e\<^sub>0 \<sigma>'" by (metis fun_upd_apply option.distinct(1) option.sel)
    }

    then show ?case by blast
  next
    case (step x y z)
    {
      fix \<E>0 H0 \<E>' H' \<pi>' \<sigma>'
      assume 
        L1H0: "x = (\<E>0, H0)" "z = (\<E>', H')" and 
        L2H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
        L2H2: "\<E>' \<pi>' = Some \<sigma>'"


      obtain \<E> H where L2H3: "y = (\<E>, H)" by (meson surj_pair)
      from L1H0(1) L2H1 L2H3 step.IH have 
        L2H4: "\<forall>\<pi> \<sigma>. \<E> \<pi> = Some \<sigma> \<longrightarrow> static_reachable_over_state e\<^sub>0 \<sigma>" by blast

      from L1H0(2) L2H2 L2H3 L2H4 step.hyps(2) have 
        "static_reachable_over_state e\<^sub>0 \<sigma>'" using static_reachable_over_state_preserved by blast

    } 

    then show ?case by blast
  qed

  from H1 H2 H4 H5 H7 show 
    "static_reachable_over_state e\<^sub>0 \<sigma>'" by blast
qed

interpretation semantics_sound
proof 
  fix \<rho>' x \<omega> \<V> \<C> e H \<E>' H' \<pi> e' \<kappa>'
  assume 
    H1: "\<rho>' x = Some \<omega>" and
    H2: "(\<V>, \<C>) \<Turnstile>\<^sub>e e" and 
    H3: "star concur_step ([[] \<mapsto> \<langle>e; empty; []\<rangle>], H) (\<E>', H')" and 
    H4: "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)"

  from H2 have 
    H5: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: static_eval_to_pool)

  from H1 H3 H4 H5
  show " {|\<omega>|} \<subseteq> \<V> x" using trace_pool_always_not_static_bound_sound by blast
next
  fix e\<^sub>0 \<E>' H' \<pi>' e' \<rho>' \<kappa>'
  assume 
    L1H1: "star concur_step ([[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>], {}) (\<E>', H')" and
    L1H2: "\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"

   show "static_reachable e\<^sub>0 e'" 
    using L1H1 L1H2 
      static_reachable_left_implies_static_reachable 
      static_reachable_over_state.simps 
      state_always_exp_not_static_reachable_sound
    by fastforce
qed

end