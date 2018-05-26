theory Sound_Semantics
  imports Main Syntax Dynamic_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|VUnit| = ^\<lparr>\<rparr>" |
  "|VChan (Ch \<pi> x)| = ^Chan x" |
  "|VClosure p \<rho>| = ^p"


inductive may_be_static_eval_value :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  may_be_static_eval_env :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit
  " |

  Chan: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VChan c
  " |

  Send_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Send_Evt _ _) \<rho>)
  " |

  Recv_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Recv_Evt _) \<rho>)
  " |

  Left: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Left _) \<rho>)
  " |

  Right: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Right _) \<rho>)
  " |

  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Abs f x e) \<rho>)
  " |

  Pair: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Pair _ _) \<rho>)
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive may_be_static_eval_stack :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive may_be_static_eval_state :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive may_be_static_eval_pool :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> trace_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
  "

lemma may_be_static_eval_state_to_exp_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" by (simp add: may_be_static_eval_state.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (rule may_be_static_eval_stack.cases; auto)
qed


lemma may_be_static_eval_state_to_exp_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l
"
proof -
  assume "\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e"  
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>"
  by (simp add: may_be_static_eval_state.simps)+ then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: may_be_static_eval_env.simps)
  with `\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)`
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


lemma may_be_static_eval_state_to_exp_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r
"
proof -
  assume "\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e"  
  and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" 
    by (simp add: may_be_static_eval_state.simps)+ then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: may_be_static_eval_env.simps)
  with `\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)`
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


lemma may_be_static_eval_state_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = b in e" by (simp add: may_be_static_eval_state.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (rule may_be_static_eval.cases; auto)
qed


lemma may_be_static_eval_state_to_exp_let_app: "
 (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
 \<rho> f = Some (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>') \<Longrightarrow>
 (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b
"

proof -
  assume "\<rho> f = Some (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>')"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps) then
  have "\<forall>x \<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: may_be_static_eval_env.simps)
  with `\<rho> f = Some (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>')`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>')" by simp then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b" by (rule may_be_static_eval_value.cases; auto)
qed

lemma may_be_static_eval_state_to_env_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
"
proof
 assume "\<rho> x = Some \<omega> "

 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (rule may_be_static_eval_state.cases; auto)+

 from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x = Some \<omega>`
 have "{|\<omega>|} \<subseteq> \<V> x" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: may_be_static_eval_env.simps)+

 from `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>`
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
       
       show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)+
     qed
   } then

   show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
 qed
qed


lemma may_be_static_eval_state_to_stack_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "\<rho> x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" by (simp add: may_be_static_eval_state.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (rule may_be_static_eval_stack.cases; auto)
qed


lemma may_be_static_eval_state_to_state_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "\<rho> x = Some \<omega>" "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)" by (blast intro: may_be_static_eval_state_to_env_result)

  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (blast intro: may_be_static_eval_state_to_exp_result)

  with `\<rho> x = Some \<omega>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: may_be_static_eval_state_to_stack_result)
qed


lemma may_be_static_eval_state_to_env_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnit)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+ 

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e`
  have "{^\<lparr>\<rparr>} \<subseteq> \<V> x" by (rule may_be_static_eval.cases; auto)+
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit" by (simp add: Unit)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> VUnit)) x' = Some \<omega>'" 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
    proof cases
      assume "x' = x" 
      with `(\<rho>(x \<mapsto> VUnit)) x' = Some \<omega>'` 
      and `{^\<lparr>\<rparr>} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
    next 
      assume "x' \<noteq> x"  with `(\<rho>(x \<mapsto> VUnit)) x' = Some \<omega>'` 

      have "\<rho> x' = Some \<omega>'" by simp

      from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x' = Some \<omega>'`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
    qed

  }
  with `{^\<lparr>\<rparr>} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> VUnit)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma may_be_static_eval_state_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
by (erule may_be_static_eval_state.cases; auto)

lemma may_be_static_eval_state_to_state_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> VUnit); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: may_be_static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnit)" by (auto simp: may_be_static_eval_state_to_env_let_unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: may_be_static_eval_state_to_stack_let)

qed

lemma may_be_static_eval_to_value_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = Prim p in e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure p \<rho>)
"
by (erule may_be_static_eval.cases; auto; rule; auto)

lemma may_be_static_eval_state_to_env_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VClosure p \<rho>))
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> " then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = Prim p in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+ then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure p \<rho>)" by (simp add: may_be_static_eval_to_value_let_prim)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = Prim p in e`
  have "{^p} \<subseteq> \<V> x" by (rule may_be_static_eval.cases; auto)+
 
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> (VClosure p \<rho>))) x' = Some \<omega>'" 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
    proof cases
      assume "x' = x" with \<open>(\<rho>(x \<mapsto> (VClosure p \<rho>))) x' = Some \<omega>'\<close>
      and `{^p} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure p \<rho>)`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
    next
      assume  "x' \<noteq> x"  with \<open>(\<rho>(x \<mapsto> (VClosure p \<rho>))) x' = Some \<omega>'\<close>

      have "\<rho> x' = Some \<omega>'" by simp
      with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
  
      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
    qed

  } then

  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> (VClosure p \<rho>))) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma may_be_static_eval_state_to_state_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> (VClosure p \<rho>)); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: may_be_static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: may_be_static_eval_state_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VClosure p \<rho>))" by (auto simp: may_be_static_eval_state_to_env_let_prim)

qed


lemma may_be_static_eval_state_to_env_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
"

proof
  assume "\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)" by (blast intro: may_be_static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (blast intro: may_be_static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l" by (blast intro: may_be_static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)`
  have " | (VClosure (Left x\<^sub>l') \<rho>\<^sub>l) | \<in> \<V> x\<^sub>s" by (blast intro: may_be_static_eval_env.cases) then
  have "^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e`
  have "\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l"
  proof cases
    case Let_Case
    from `\<forall>x\<^sub>l'. ^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l`
    and `^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l" by simp
  qed

  from `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'` `\<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l` 
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
   
  }
  with `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma may_be_static_eval_state_to_stack_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: may_be_static_eval_state.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)`
  have " | (VClosure (Left x\<^sub>l') \<rho>\<^sub>l) | \<in> \<V> x\<^sub>s" by (blast intro: may_be_static_eval_env.cases) then
  have "^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e`
  show "\<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x" 
  proof cases
    case Let_Case
    assume "\<forall>x\<^sub>l'. ^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l"
    with `^prim.Left x\<^sub>l' \<in> \<V> x\<^sub>s`
    show "\<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x" by blast
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: may_be_static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: may_be_static_eval_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: may_be_static_eval_state_to_stack_let)
  
qed


lemma may_be_static_eval_state_to_state_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l) \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" by (simp add: may_be_static_eval_state_to_exp_let_case_left)

  assume "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)" by (simp add: may_be_static_eval_state_to_env_let_case_left)

  from `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` 
  and `\<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>" by (simp add: may_be_static_eval_state_to_stack_let_case_left)
qed


lemma may_be_static_eval_state_to_env_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
"

proof
  assume "\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)" by (blast intro: may_be_static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (blast intro: may_be_static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r" by (blast intro: may_be_static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)`
  have " | (VClosure (Right x\<^sub>r') \<rho>\<^sub>r) | \<in> \<V> x\<^sub>s" by (blast intro: may_be_static_eval_env.cases) then
  have "^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e`
  have "\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r"
  proof cases
    case Let_Case
    from `\<forall>x\<^sub>r'. ^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r`
    and `^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'` `\<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r` 
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r" by blast

  {
    fix x' \<omega>'
    assume "(\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho> x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
   
  }
  with `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma may_be_static_eval_state_to_stack_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: may_be_static_eval_state.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)`
  have " | (VClosure (Right x\<^sub>r') \<rho>\<^sub>r) | \<in> \<V> x\<^sub>s" by (blast intro: may_be_static_eval_env.cases) then
  have "^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e`
  show "\<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x" 
  proof cases
    case Let_Case
    assume "\<forall>x\<^sub>r'. ^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow> \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r"
    with `^prim.Right x\<^sub>r' \<in> \<V> x\<^sub>s`
    show "\<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x" by blast
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: may_be_static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: may_be_static_eval_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: may_be_static_eval_state_to_stack_let)
  
qed

lemma may_be_static_eval_state_to_state_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (simp add: may_be_static_eval_state_to_exp_let_case_right)

  assume "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)" by (simp add: may_be_static_eval_state_to_env_let_case_right)

  from `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` 
  and `\<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r)` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>" by (simp add: may_be_static_eval_state_to_stack_let_case_right)
qed


lemma may_be_static_eval_state_to_env_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
proof
  assume "\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+

  thm may_be_static_eval_state.simps

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" by (blast intro: may_be_static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: may_be_static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>1" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: may_be_static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have " | (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) | \<in> \<V> x\<^sub>p" by (blast intro: may_be_static_eval_env.cases) then
  have "^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e`
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
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
  }
  with `{|\<omega>|} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed



lemma may_be_static_eval_state_to_state_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: may_be_static_eval_state_to_exp_let)

  assume "\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)"  by (simp add: may_be_static_eval_state_to_env_let_fst)

  from `\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)` and `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: may_be_static_eval_state_to_stack_let)
qed


lemma may_be_static_eval_state_to_env_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
proof
  assume "\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" by (blast intro: may_be_static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: may_be_static_eval_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>2" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: may_be_static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)`
  have " | (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) | \<in> \<V> x\<^sub>p" by (blast intro: may_be_static_eval_env.cases) then
  have "^prim.Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p" by simp

  from  `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e`
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
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
  }
  with \<open>{|\<omega>|} \<subseteq> \<V> x\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<close> 
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma may_be_static_eval_state_to_state_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p) \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: may_be_static_eval_state_to_exp_let)

  assume "\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)" by (simp add: may_be_static_eval_state_to_env_let_snd)

  from `\<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)` and `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: may_be_static_eval_state_to_stack_let)
qed


lemma may_be_static_eval_state_to_env_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l) \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)
"
proof
  assume "\<rho> f = Some (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)" "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x\<^sub>a = Some \<omega>\<^sub>a`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a" by (blast intro: may_be_static_eval_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)`
  have "{|(VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)" by (blast intro: may_be_static_eval_env.cases)+

  from `{|(VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f`
  have "^Abs f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)`
  have "{|(VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f\<^sub>l" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (rule may_be_static_eval_value.cases; auto)+


  with `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e`
  have "\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l"
  proof cases
    case Let_App
    assume "\<forall>f' x' e'. ^Abs f' x' e' \<in> \<V> f \<longrightarrow> \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x"
    with `^Abs f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f`
    show "\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l" by blast
  qed

  from `{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a` `\<V> x\<^sub>a \<subseteq> \<V> x\<^sub>l`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l" by blast


  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" "x' \<noteq> f\<^sub>l" then
    have "\<rho>\<^sub>l x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
  }
  with \<open>{|(VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)|} \<subseteq> \<V> f\<^sub>l\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a\<close> \<open>{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l\<close>
  show "\<forall>x \<omega>. (\<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto

qed

lemma may_be_static_eval_state_to_stack_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>') \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
proof
  assume "\<rho> f = Some (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>')" and "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e"  "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: may_be_static_eval_state.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some (VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>')`
  have " {|(VClosure (Abs f' x\<^sub>p e\<^sub>b) \<rho>')|} \<subseteq> \<V> f" by (blast intro: may_be_static_eval_env.cases) then
  have " ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e`
  show " \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> \<V> x"
  proof cases
    case Let_App
    assume "\<forall>f' x' e'. ^Abs f' x' e' \<in> \<V> f \<longrightarrow> \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x"
    with `^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f`
    show " \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> \<V> x" by simp
  qed

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: may_be_static_eval_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: may_be_static_eval_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: may_be_static_eval_state_to_stack_let)
qed


theorem may_be_static_eval_state_preserved_under_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>; 
    seq_step (b, \<rho>) \<omega>
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" and
    H2: "seq_step (b, \<rho>) \<omega>"
    
  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>"
  proof cases
    case Let_Unit
    
    assume
      H3: "b = \<lparr>\<rparr>" and
      H4: "\<omega> = VUnit"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" by simp

    then have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho> ++ [x \<mapsto> VUnit]; \<kappa>\<rangle>" by (simp add: may_be_static_eval_state_to_state_let_unit)
    
    with H4 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by simp
  next
    case (Let_Prim p)

    assume
      H3: "b = Prim p" and
      H4: "\<omega> = VClosure p \<rho>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>" by simp

    then have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho> ++ [x \<mapsto> VClosure p \<rho>]; \<kappa>\<rangle>" by (simp add: may_be_static_eval_state_to_state_let_prim)
    
    with H4 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by simp
  next
    case (Let_Fst x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)

    assume 
      H3: "b = FST x\<^sub>p" and
      H4: "\<rho> x\<^sub>p = Some (VClosure (prim.Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and
      H5: "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" by simp

    with H4 H5 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>" by (simp add: may_be_static_eval_state_to_state_let_fst)
  next
    case (Let_Snd x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)

    assume 
      H3: "b = SND x\<^sub>p" and
      H4: "\<rho> x\<^sub>p = Some (VClosure (prim.Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p)" and
      H5: "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"

    from H1 H3 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" by simp

    with H4 H5 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>" by (simp add: may_be_static_eval_state_to_state_let_snd)
  qed
qed

theorem may_be_static_eval_state_preserved_under_step_up : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>;
    seq_step_up (b, \<rho>) (e', \<rho>')
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" and
    H2: "seq_step_up (b, \<rho>) (e', \<rho>')"

  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>" 
  proof cases
    case (Let_Case_Left x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)

    assume 
      H3: "b = CASE x\<^sub>s LEFT x\<^sub>l |> e' RIGHT x\<^sub>r |> e\<^sub>r" and
      H4: "\<rho>' = \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)" and
      H5: "\<rho> x\<^sub>s = Some (VClosure (prim.Left x\<^sub>l') \<rho>\<^sub>l)" and
      H6: "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"

    from H1 H3 H4 H5 H6
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>" by (simp add: may_be_static_eval_state_to_state_let_case_left)
  next
    case (Let_Case_Right x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)

    assume 
      H3: "b = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e'" and
      H4: "\<rho>' = \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)" and
      H5: "\<rho> x\<^sub>s = Some (VClosure (prim.Right x\<^sub>r') \<rho>\<^sub>r)" and
      H6: "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"

    from H1 H3 H4 H5 H6
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>" by (simp add: may_be_static_eval_state_to_state_let_case_right)
  next
    case (Let_App f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>l)
    assume
      H3: "b = APP f x\<^sub>a" and
      H4: "\<rho>' = \<rho>\<^sub>l(f\<^sub>l \<mapsto> VClosure (Abs f\<^sub>l x\<^sub>l e') \<rho>\<^sub>l, x\<^sub>l \<mapsto> \<omega>\<^sub>l)" and
      H5: "\<rho> f = Some (VClosure (Abs f\<^sub>l x\<^sub>l e') \<rho>\<^sub>l)" and
      H6: "\<rho> x\<^sub>a = Some \<omega>\<^sub>l"

    have H7: "(\<V>, \<C>) \<Turnstile>\<^sub>e e'" using H1 H3 H5 may_be_static_eval_state_to_exp_let_app by auto
  
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> (VClosure (Abs f\<^sub>l x\<^sub>l e') \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>l)" using H1 H3 H5 H6 may_be_static_eval_state_to_env_let_app by auto

    with H4 have H8: "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>'" by simp
  
    have H9: "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e'\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>"  using H1 H3 H5 H6 may_be_static_eval_state_to_stack_let_app by auto
  
    from H7 H8 H9
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e'; \<rho>'; \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>" by (simp add: may_be_static_eval_state.intros)
  qed
qed

theorem may_be_static_eval_state_preserved_under_step_down : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>; 
    \<rho> x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" and
    H2: "\<rho> x = Some \<omega>"

  from H1 H2
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>" by (auto simp: may_be_static_eval_state_to_state_result)
qed

(*
lemma may_be_static_eval_preserved_under_seq_step_down: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;;(LReturn x\<^sub>\<kappa>) \<mapsto> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>)
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps)
  
  assume "\<rho> x = Some \<omega>" with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>" 
    using may_be_static_eval_state_to_state_result by auto

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>\<close>
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;;(LReturn x\<^sub>\<kappa>) \<mapsto> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>)" using may_be_static_eval_pool.simps by auto
qed
*)

(*
lemma may_be_static_eval_preserved_under_seq_step_up: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<up>\<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>;;(LCall x) \<mapsto> \<sigma>')
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps)

  assume "\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<up>\<hookrightarrow> \<sigma>'" with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: may_be_static_eval_state_preserved_under_step_up)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'\<close>
  show "\<forall>\<pi>' \<sigma>. (\<E>(\<pi> ;;(LCall x) \<mapsto> \<sigma>')) \<pi>' = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (simp add: may_be_static_eval_pool.simps)
qed
*)
(*
lemma may_be_static_eval_preserved_under_seq_step: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  seq_step (LET x = b in e) \<rho> \<rho>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;;(LNext x) \<mapsto> \<langle>e; \<rho>'; \<kappa>\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps)

  assume "\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>'" with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: may_be_static_eval_state_preserved_under_step)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'\<close>
  show "\<forall>\<pi>' \<sigma>. (\<E>(\<pi> ;;(LNext x) \<mapsto> \<sigma>')) \<pi>' = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (simp add: may_be_static_eval_pool.simps)
qed
*)

lemma may_be_static_eval_pool_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e " by (blast intro: may_be_static_eval_state_to_exp_let)
qed


lemma may_be_static_eval_pool_let_sync_send_values_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>\<^sub>c x\<^sub>c)) \<Longrightarrow>
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>\<^sub>c x\<^sub>c))"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: may_be_static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "{|(VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)|} \<subseteq> \<V> x\<^sub>s\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" by (blast intro: may_be_static_eval_env.cases)+

  from `{|(VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)|} \<subseteq> \<V> x\<^sub>s\<^sub>e`
  have "^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: may_be_static_eval_value.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>\<^sub>c x\<^sub>c))`
  have "{|(VChan (Ch \<pi>\<^sub>c x\<^sub>c))|} \<subseteq> \<V> x\<^sub>s\<^sub>c" by (blast intro: may_be_static_eval_env.cases) then
  have "{^Chan x\<^sub>c} \<subseteq> \<V> x\<^sub>s\<^sub>c" by simp then
  have "^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c" by auto
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s`
  show "{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c"
  proof cases
    case Let_Sync
    assume "\<forall>x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c. ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e \<longrightarrow> ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow> {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c"
    with `^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e` and `^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c`
    show "{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" by blast
  qed

qed

lemma may_be_static_eval_pool_let_sync_send_message_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  {|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: may_be_static_eval_state.simps)
  with `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" by (blast intro: may_be_static_eval_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: may_be_static_eval_value.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
  show "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" by (blast intro: may_be_static_eval_env.cases)
qed

lemma may_be_static_eval_pool_to_env_let_sync_send: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)
"
proof
  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)"
  and  "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: may_be_static_eval_state.simps)+

  have "{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s"
  proof (cases c)
    case (Ch \<pi> x\<^sub>c)
    assume "c = Ch \<pi> x\<^sub>c" 
    with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)`
    and  `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
    show "{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s" using may_be_static_eval_pool_let_sync_send_values_relate by simp
  qed
  
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit" by (simp add: Unit)
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>s" then
    have "\<rho>\<^sub>s x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
  }
  with \<open>{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit\<close> 
  show "\<forall>x \<omega>. (\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by simp
qed


lemma may_be_static_eval_pool_let_sync_recv_values_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi>\<^sub>c x\<^sub>c)) \<Longrightarrow>
  \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi>\<^sub>c x\<^sub>c))"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: may_be_static_eval_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
  have "{|(VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)|} \<subseteq> \<V> x\<^sub>r\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)" by (blast intro: may_be_static_eval_env.cases)+

  from `{|(VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)|} \<subseteq> \<V> x\<^sub>r\<^sub>e`
  have "^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r\<^sub>e" by (blast intro: may_be_static_eval_value.cases)
  with `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan (Ch \<pi>\<^sub>c x\<^sub>c))`
  have "{|(VChan (Ch \<pi>\<^sub>c x\<^sub>c))|} \<subseteq> \<V> x\<^sub>r\<^sub>c" by (blast intro: may_be_static_eval_env.cases) then
  have "{^Chan x\<^sub>c} \<subseteq> \<V> x\<^sub>r\<^sub>c" by simp then
  have "^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c" by auto
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r`
  show "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r"
  proof cases
    case Let_Sync
    assume "\<forall>x\<^sub>r\<^sub>c x\<^sub>c. ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r"
    with `^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e` and `^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c`
    show "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" by blast
  qed
qed


lemma may_be_static_eval_pool_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: may_be_static_eval_state_to_stack_let)
qed

lemma may_be_static_eval_pool_to_env_let_sync_recv: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow> 
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m" then
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" using may_be_static_eval_pool_let_sync_send_message_relate by auto

  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: may_be_static_eval_state.simps)+


  have "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r"
  proof (cases c)
    case (Ch \<pi>\<^sub>c x\<^sub>c)
    assume "c = Ch \<pi>\<^sub>c x\<^sub>c" 

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
    have "\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" using \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)\<close> may_be_static_eval_pool_let_sync_send_values_relate by blast

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c)`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
    and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)`
    have "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" using  may_be_static_eval_pool_let_sync_recv_values_relate by auto

    from `\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c` and `\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r`
    show "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m` and `\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r`
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r" by blast

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: may_be_static_eval_state.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho>\<^sub>r x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
  }
  with `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m`
  show "\<forall>x \<omega>. (\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto
qed


lemma may_be_static_eval_preserved_under_sync: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c) \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;;(LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;;(LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c)"


  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s" by (blast intro: may_be_static_eval_pool_to_exp_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)" by (blast intro: may_be_static_eval_pool_to_env_let_sync_send)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s" by (blast intro: may_be_static_eval_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>" by (blast intro: may_be_static_eval_state.intros)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (blast intro: may_be_static_eval_pool_to_exp_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
  and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)\<close> 
  and \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)\<close>
  and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close> 
  and \<open>\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)\<close> \<open>\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)" by (blast intro: may_be_static_eval_pool_to_env_let_sync_recv)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r" by (blast intro: may_be_static_eval_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>" by (blast intro: may_be_static_eval_state.intros)

  {
    fix \<pi> \<sigma>
    assume  "\<pi> \<noteq> \<pi>\<^sub>s ;;(LNext x\<^sub>s)" and "\<pi> \<noteq> \<pi>\<^sub>r ;; (LNext x\<^sub>r)"
    and "(\<E>(\<pi>\<^sub>s ;;(LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma>" then
    have "\<E> \<pi> = Some \<sigma>" by simp
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (blast intro: may_be_static_eval_pool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r (x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s (x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>`
  show "\<forall>\<pi> \<sigma>. (\<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;;(LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by simp

qed


lemma may_be_static_eval_pool_to_env_let_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChan (Ch \<pi> x)))
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" by (blast intro: may_be_static_eval_pool.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e" by (blast intro: may_be_static_eval_state.cases) then
  have "{^Chan x} \<subseteq> \<V> x"  by (blast intro: may_be_static_eval.cases)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VChan (Ch \<pi> x))" by (simp add: Chan)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>` 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> (VChan (Ch \<pi> x)))) x' = Some \<omega>'" and "x \<noteq> x'"then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: may_be_static_eval_env.simps)
  } with `{^Chan x} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> (VChan (Ch \<pi> x))`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> (VChan (Ch \<pi> x)))) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma may_be_static_eval_preserved_under_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;;(LNext x) \<mapsto> \<langle>e; \<rho>(x \<mapsto> (VChan (Ch \<pi> x))); \<kappa>\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: may_be_static_eval_pool_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChan (Ch \<pi> x)))" by (blast intro: may_be_static_eval_pool_to_env_let_chan )

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: may_be_static_eval_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> (VChan (Ch \<pi> x)))` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> (VChan (Ch \<pi> x)));\<kappa>\<rangle>" by (blast intro: may_be_static_eval_state.intros)
  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> ;;(LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChan (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some \<sigma>'" 
    and "\<pi>' \<noteq> \<pi> ;;(LNext x)" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: may_be_static_eval_pool.simps)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> (VChan (Ch \<pi> x)));\<kappa>\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> ;;(LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> (VChan (Ch \<pi> x)));\<kappa>\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


lemma may_be_static_eval_pool_to_env_let_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnit)"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e" by (blast intro: may_be_static_eval_state.cases) then
  have "{^\<lparr>\<rparr>} \<subseteq> \<V> x"  by (blast intro: may_be_static_eval.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit" by (simp add: Unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>` 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> VUnit)) x' = Some \<omega>'" and "x \<noteq> x'" then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (blast intro: may_be_static_eval_env.cases)
  } with `{^\<lparr>\<rparr>} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> VUnit`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> VUnit)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed

lemma may_be_static_eval_preserved_under_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;;(LNext x) \<mapsto> \<langle>e; \<rho>(x \<mapsto> VUnit); \<kappa>\<rangle>, \<pi>;;(LSpawn x) \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: may_be_static_eval_pool_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnit)" by (blast intro: may_be_static_eval_pool_to_env_let_spawn)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: may_be_static_eval_pool_to_stack_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> VUnit)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<close>
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> VUnit);\<kappa>\<rangle>" by (simp add: may_be_static_eval_state.intros)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c" by (blast intro: may_be_static_eval.cases)

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []" by (simp add: may_be_static_eval_stack.Empty)
  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>" by (simp add: may_be_static_eval_state.intros)

  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> ;;(LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnit);\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>'"
    and "\<pi>' \<noteq> \<pi> ;; (LNext x)" and " \<pi>' \<noteq> \<pi> ;; (LSpawn x)" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (blast intro: may_be_static_eval_pool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> VUnit);\<kappa>\<rangle>` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> VUnit);\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


theorem may_be_static_eval_preserved_under_concur_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
proof -
  assume 
    H1: "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and
    H2: "\<E> \<rightarrow> \<E>'"

  from H2 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    assume 
      H3: "\<E>' = \<E> ++ [\<pi> ;; LReturn x\<^sub>\<kappa> \<mapsto> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>]" and
      H4: "leaf \<E> \<pi>" and 
      H5: "\<E> \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" and 
      H6: "\<rho> x = Some \<omega>"

    from H1 H5 H6
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; LReturn x\<^sub>\<kappa> \<mapsto> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>)" using may_be_static_eval_pool.simps may_be_static_eval_state_to_state_result by fastforce

    with H3 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Seq_Step \<pi> x b e \<rho> \<kappa> \<omega>)
    assume 
      H3: "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>]" and
      H4: "leaf \<E> \<pi>" and 
      H5: "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)" and 
      H6: "seq_step (b, \<rho>) \<omega>"

    from H1 H5 have H7:"(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>" by (auto simp: may_be_static_eval_pool.simps)

    with H6 have H8: "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>" by (auto simp: may_be_static_eval_state_preserved_under_step)

    with H1 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<omega>);\<kappa>\<rangle>)" by (auto simp: may_be_static_eval_pool.simps)

    with H3 show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Seq_Step_Up \<pi> x b e \<rho> \<kappa> e' \<rho>')
    assume "\<E>' = \<E> ++ [\<pi> ;; (LCall x) \<mapsto> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)"
    and "seq_step_up (b, \<rho>) (e', \<rho>')"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LCall) x \<mapsto> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)"
      using may_be_static_eval_pool.simps may_be_static_eval_state_preserved_under_step_up by fastforce
    with \<open>\<E>' = \<E> ++ [\<pi> ;; (LCall x) \<mapsto> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)
    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))];\<kappa>\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))];\<kappa>\<rangle>)" by (simp add: may_be_static_eval_preserved_under_chan)
    with \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))];\<kappa>\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    assume "\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)" by (simp add: may_be_static_eval_preserved_under_spawn)
    with \<open>\<E>' = \<E> ++ [\<pi> ;; (LNext x) \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; (LSpawn x) \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)
    assume "\<E>' = \<E> ++ [\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]"

    assume "leaf \<E> \<pi>\<^sub>s"
    and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
    and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)"
    and "leaf \<E> \<pi>\<^sub>r"
    and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"
    and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e)"
    and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)"
    and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c)"
    and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>)" by (simp add: may_be_static_eval_preserved_under_sync)
    with \<open>\<E>' = \<E> ++ [\<pi>\<^sub>s ;; (LNext x\<^sub>s) \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; (LNext x\<^sub>r) \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  qed
qed


theorem may_be_static_eval_preserved_under_concur_step_star : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;  
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  assume "\<E> \<rightarrow>* \<E>'" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
  proof (induction rule: star.induct)
    case (refl \<E>)
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" by simp
  next
    case (step \<E> \<E>\<^sub>m \<E>')
    assume " \<E> \<rightarrow> \<E>\<^sub>m"
    and "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<^sub>m \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" then
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by (blast intro: may_be_static_eval_preserved_under_concur_step)
  qed with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by blast
qed

theorem may_be_static_eval_env_to_precise : "
  \<rho> x = Some \<omega> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho> x = Some \<omega>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" then
  show "{|\<omega>|} \<subseteq> \<V> x" by (simp add: may_be_static_eval_env.simps)
qed

theorem may_be_static_eval_pool_to_precise : "
  \<rho> x = Some \<omega> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho> x = Some \<omega>"

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)" then

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>" by (simp add: may_be_static_eval_pool.simps) then

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: may_be_static_eval_state.simps) 
  with `\<rho> x = Some \<omega>`

  show "{|\<omega>|} \<subseteq> \<V> x" by (simp add: may_be_static_eval_env.simps)
qed

theorem values_not_bound_pool_sound : "
  \<rho>' x = Some \<omega> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> 
  \<E> \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho>' x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<rightarrow>* \<E>'" and "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by (blast intro: may_be_static_eval_preserved_under_concur_step_star)
  with \<open>\<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> and `\<rho>' x = Some \<omega>`
  show "{|\<omega>|} \<subseteq> \<V> x" using may_be_static_eval_pool_to_precise by auto
qed


lemma may_be_static_eval_to_pool: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e"

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty" by (simp add: may_be_static_eval_value_may_be_static_eval_env.Any)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []" by (simp add: may_be_static_eval_stack.Empty)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>" by (simp add: may_be_static_eval_state.intros)

  have "[[] \<mapsto> \<langle>e; empty; []\<rangle>] [] = Some (\<langle>e; empty; []\<rangle>)" by simp
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: may_be_static_eval_pool.intros)
qed


theorem values_not_bound_sound : "
  \<rho>' x = Some \<omega> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho>' x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e" and "[[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'"
  and "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: may_be_static_eval_to_pool)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]\<close> 
  and \<open>[[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'\<close> 
  and \<open>\<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
  and `\<rho>' x = Some \<omega> `

  show " {|\<omega>|} \<subseteq> \<V> x" using values_not_bound_pool_sound by blast
qed

end
