theory Sound_Semantics
  imports Main Syntax Dynamic_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|\<lbrace>\<rbrace>| = ^\<lparr>\<rparr>" |
  "|\<lbrace>Ch \<pi> x\<rbrace>| = ^Chan x" |
  "|\<lbrace>p, \<rho>\<rbrace>| = ^p"


definition env_to_abstract_value_env :: "(var \<rightharpoonup> val) \<Rightarrow> abstract_value_env" ("\<parallel>_\<parallel>" [0]61) where
  "\<parallel>\<rho>\<parallel> = (\<lambda> x . (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {|\<omega>|} |
    None \<Rightarrow> {}
  ))"

inductive accept_value :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  accept_val_env :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>
  " |

  Chan: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>c\<rbrace>
  " |

  Send_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |

  Recv_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |

  Left: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Left _, \<rho>\<rbrace>
  " |

  Right: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Right _, \<rho>\<rbrace>
  " |

  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |

  Pair: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive accept_stack :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
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


inductive accept_state :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive accept_state_pool :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
  "

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
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (rule accept_state.cases; auto)+

 from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x = Some \<omega>`
 have "{|\<omega>|} \<subseteq> \<V> x" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (simp add: accept_val_env.simps)+

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
       
       show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)+
     qed
   } then

   show "\<forall>x \<omega>'. (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) x = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
 qed
qed


lemma accept_state_to_stack_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "\<rho> x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> x \<Rrightarrow> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>" by (simp add: accept_state.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (rule accept_stack.cases; auto)
qed


lemma accept_state_to_state_result: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "\<rho> x = Some \<omega>" "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)" by (blast intro: accept_state_to_env_result)

  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>\<kappa>" by (blast intro: accept_state_to_exp_result)

  with `\<rho> x = Some \<omega>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: accept_state_to_stack_result)
qed


lemma accept_state_to_env_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+ 

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e`
  have "{^\<lparr>\<rparr>} \<subseteq> \<V> x" by (rule accept_exp.cases; auto)+
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" by (simp add: Unit)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>'" 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
    proof cases
      assume "x' = x" 
      with `(\<rho>(x \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>'` 
      and `{^\<lparr>\<rparr>} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
    next 
      assume "x' \<noteq> x"  with `(\<rho>(x \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>'` 

      have "\<rho> x' = Some \<omega>'" by simp

      from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x' = Some \<omega>'`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
    qed

  }
  with `{^\<lparr>\<rparr>} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma accept_state_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
by (erule accept_state.cases; auto)

lemma accept_state_to_state_let_unit: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: accept_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)" by (auto simp: accept_state_to_env_let_unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: accept_state_to_stack_let)

qed

lemma accept_exp_to_value_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = Prim p in e \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>p, \<rho>\<rbrace>
"
by (erule accept_exp.cases; auto; rule; auto)

lemma accept_state_to_env_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> " then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = Prim p in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+ then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>p, \<rho>\<rbrace>" by (simp add: accept_exp_to_value_let_prim)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = Prim p in e`
  have "{^p} \<subseteq> \<V> x" by (rule accept_exp.cases; auto)+
 
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)) x' = Some \<omega>'" 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'"
    proof cases
      assume "x' = x" with \<open>(\<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)) x' = Some \<omega>'\<close>
      and `{^p} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>p, \<rho>\<rbrace>`

      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
    next
      assume  "x' \<noteq> x"  with \<open>(\<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)) x' = Some \<omega>'\<close>

      have "\<rho> x' = Some \<omega>'" by simp
      with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` 
  
      show "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
    qed

  } then

  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma accept_state_to_state_let_prim: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (auto simp: accept_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (auto simp: accept_state_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)" by (auto simp: accept_state_to_env_let_prim)

qed


lemma accept_state_to_env_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
"

proof
  assume "\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>" by (blast intro: accept_val_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (blast intro: accept_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`
  have "{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l" by (blast intro: accept_val_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>`
  have " | \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> | \<in> \<V> x\<^sub>s" by (blast intro: accept_val_env.cases) then
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
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
   
  }
  with `{|\<omega>\<^sub>l|} \<subseteq> \<V> x\<^sub>l` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>l`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed


lemma accept_state_to_stack_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>" "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: accept_state.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>`
  have " | \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> | \<in> \<V> x\<^sub>s" by (blast intro: accept_val_env.cases) then
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
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: accept_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: accept_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: accept_state_to_stack_let)
  
qed


lemma accept_state_to_state_let_case_left: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l" by (simp add: accept_state_to_exp_let_case_left)

  assume "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)" by (simp add: accept_state_to_env_let_case_left)

  from `\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` 
  and `\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>" by (simp add: accept_state_to_stack_let_case_left)
qed


lemma accept_state_to_env_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
"

proof
  assume "\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" then 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>" by (blast intro: accept_val_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (blast intro: accept_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`
  have "{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r'" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r" by (blast intro: accept_val_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>`
  have " | \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> | \<in> \<V> x\<^sub>s" by (blast intro: accept_val_env.cases) then
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
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
   
  }
  with `{|\<omega>\<^sub>r|} \<subseteq> \<V> x\<^sub>r` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>r`
  show "\<forall>x' \<omega>'. (\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed

lemma accept_state_to_stack_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>"
  assume "\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>" "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: accept_state.cases)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>`
  have " | \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> | \<in> \<V> x\<^sub>s" by (blast intro: accept_val_env.cases) then
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
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: accept_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: accept_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: accept_state_to_stack_let)
  
qed

lemma accept_state_to_state_let_case_right: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>" and "\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (simp add: accept_state_to_exp_let_case_right)

  assume "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` and `\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)" by (simp add: accept_state_to_env_let_case_right)

  from `\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r`  
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle>` 
  and `\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>` 
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>" by (simp add: accept_state_to_stack_let_case_right)
qed


lemma accept_state_to_env_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
proof
  assume "\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+

  thm accept_state.simps

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" by (blast intro: accept_val_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: accept_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>1" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: accept_val_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>`
  have " | \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> | \<in> \<V> x\<^sub>p" by (blast intro: accept_val_env.cases) then
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
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
  }
  with `{|\<omega>|} \<subseteq> \<V> x` `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by auto
qed



lemma accept_state_to_state_let_fst: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: accept_state_to_exp_let)

  assume "\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)"  by (simp add: accept_state_to_env_let_fst)

  from `\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>` and `\<rho>\<^sub>p x\<^sub>1 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: accept_state_to_stack_let)
qed


lemma accept_state_to_env_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
"
proof
  assume "\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" by (blast intro: accept_val_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p" by (blast intro: accept_value.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>p` `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  have "{|\<omega>|} \<subseteq> \<V> x\<^sub>2" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by (blast intro: accept_val_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` `\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>`
  have " | \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> | \<in> \<V> x\<^sub>p" by (blast intro: accept_val_env.cases) then
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
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
  }
  with \<open>{|\<omega>|} \<subseteq> \<V> x\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<close> 
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<omega>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma accept_state_to_state_let_snd: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (simp add: accept_state_to_exp_let)

  assume "\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)" by (simp add: accept_state_to_env_let_snd)

  from `\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>` and `\<rho>\<^sub>p x\<^sub>2 = Some \<omega>`
  and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: accept_state_to_stack_let)
qed


lemma accept_state_to_env_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a)
"
proof
  assume "\<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>" "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> x\<^sub>a = Some \<omega>\<^sub>a`
  have "{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>a" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a" by (blast intro: accept_val_env.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>`
  have "{|\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>|} \<subseteq> \<V> f" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>" by (blast intro: accept_val_env.cases)+

  from `{|\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>|} \<subseteq> \<V> f`
  have "^Abs f\<^sub>l x\<^sub>l e\<^sub>l \<in> \<V> f" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>`
  have "{|\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>|} \<subseteq> \<V> f\<^sub>l" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l" by (rule accept_value.cases; auto)+


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
    assume "(\<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>l" "x' \<noteq> f\<^sub>l" then
    have "\<rho>\<^sub>l x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
  }
  with \<open>{|\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>|} \<subseteq> \<V> f\<^sub>l\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>a\<close> \<open>{|\<omega>\<^sub>a|} \<subseteq> \<V> x\<^sub>l\<close>
  show "\<forall>x \<omega>. (\<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto

qed

lemma accept_state_to_stack_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
proof
  assume "\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>" and "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e"  "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: accept_state.cases)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>` and `\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>`
  have " {|\<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>|} \<subseteq> \<V> f" by (blast intro: accept_val_env.cases) then
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
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: accept_state_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (blast intro: accept_state.cases)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: accept_state_to_stack_let)
qed


lemma accept_state_to_state_let_app: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>b; \<rho>'(f' \<mapsto> \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>, x\<^sub>p \<mapsto> \<omega>\<^sub>a); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>" and "\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>b" by (blast intro: accept_state_to_exp_let_app)

  assume "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>` and `\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>'(f' \<mapsto> \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>, x\<^sub>p \<mapsto> \<omega>\<^sub>a)" by (blast intro: accept_state_to_env_let_app)

  from `\<rho> x\<^sub>a = Some \<omega>\<^sub>a` and  `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle>` and `\<rho> f = Some \<lbrace>Abs f' x\<^sub>p e\<^sub>b, \<rho>'\<rbrace>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>b\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>" by (blast intro: accept_state_to_stack_let_app)
qed

theorem accept_state_preserved_under_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>; 
    \<sigma> \<hookrightarrow> \<sigma>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>"
  assume "\<sigma> \<hookrightarrow> \<sigma>'" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'"
  proof cases
    case (Result \<rho> x \<omega> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa>)
    assume "\<sigma> = \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" and "\<sigma>' = \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>" and "\<rho> x = Some \<omega>" 
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_result)
  next
    case (Let_Unit x e \<rho> \<kappa>)
    assume "\<sigma> = \<langle>LET x = \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>" and "\<sigma>' = \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_unit)
  next
    case (Let_Prim x p e \<rho> \<kappa>)
    assume "\<sigma> = \<langle>LET x = Prim p in e;\<rho>;\<kappa>\<rangle>" and "\<sigma>' = \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>p, \<rho>\<rbrace>];\<kappa>\<rangle>"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_prim)
  next
    case (Let_Fst \<rho> x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p \<omega> x e \<kappa>)
    assume "\<sigma> = \<langle>LET x = FST x\<^sub>p in e;\<rho>;\<kappa>\<rangle>"
    and "\<sigma>' = \<langle>e;\<rho> ++ [x \<mapsto> \<omega>];\<kappa>\<rangle>"
    and "\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" and "\<rho>\<^sub>p x\<^sub>1 = Some \<omega>"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_fst)
  next
    case (Let_Snd \<rho> x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p \<omega> x e \<kappa>)
    assume "\<sigma> = \<langle>LET x = SND x\<^sub>p in e;\<rho>;\<kappa>\<rangle>"
    and "\<sigma>' = \<langle>e;\<rho> ++ [x \<mapsto> \<omega>];\<kappa>\<rangle>"
    and "\<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>" and "\<rho>\<^sub>p x\<^sub>2 = Some \<omega>"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_snd)
  next
    case (Let_Case_Left \<rho> x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e \<kappa>)

    assume "\<sigma> = \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>"
    and "\<sigma>' = \<langle>e\<^sub>l;\<rho> ++ [x\<^sub>l \<mapsto> \<omega>\<^sub>l];\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>"
    and "\<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>" and "\<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_case_left)
  next
    case (Let_Case_Right \<rho> x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e \<kappa>)
    assume "\<sigma> = \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e;\<rho>;\<kappa>\<rangle>"
    and "\<sigma>' = \<langle>e\<^sub>r;\<rho> ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>r];\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>"
    and "\<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>"
    and "\<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_case_right)
  next
    case (Let_App \<rho> f f\<^sub>l x\<^sub>l e\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a x e \<kappa>)
    assume "\<sigma> = \<langle>LET x = APP f x\<^sub>a in e;\<rho>;\<kappa>\<rangle>"
    and "\<sigma>' = \<langle>e\<^sub>l;\<rho>\<^sub>l ++ [f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a];\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>"
    and "\<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"
    and "\<rho> x\<^sub>a = Some \<omega>\<^sub>a"
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_to_state_let_app)
  qed

qed

lemma accept_preserved_under_seq_step_down: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>')
"
proof
  
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>" by (simp add: accept_state_pool.simps)
  
  assume "\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'" with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_preserved_under_step)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'\<close>
  show "\<forall>\<pi>' \<sigma>. (\<E>(\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>')) \<pi>' = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (simp add: accept_state_pool.simps)

qed


lemma accept_preserved_under_seq_step_up: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>;;\<upharpoonleft>x \<mapsto> \<sigma>')
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps)

  assume "\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>'" with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_preserved_under_step)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'\<close>
  show "\<forall>\<pi>' \<sigma>. (\<E>(\<pi> ;; \<upharpoonleft>x \<mapsto> \<sigma>')) \<pi>' = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (simp add: accept_state_pool.simps)
qed


lemma accept_preserved_under_seq_step: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<sigma>')
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps)

  assume "\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>'" with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_preserved_under_step)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'\<close>
  show "\<forall>\<pi>' \<sigma>. (\<E>(\<pi> ;; `x \<mapsto> \<sigma>')) \<pi>' = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (simp add: accept_state_pool.simps)
qed

lemma accept_pool_to_exp_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>e e
"
proof -
 assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
 have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps) then
 show "(\<V>, \<C>) \<Turnstile>\<^sub>e e " by (blast intro: accept_state_to_exp_let)
qed


lemma accept_pool_let_sync_send_values_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace> \<Longrightarrow>
  {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace>"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: accept_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>`
  have "{|\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>|} \<subseteq> \<V> x\<^sub>s\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>" by (blast intro: accept_val_env.cases)+

  from `{|\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>|} \<subseteq> \<V> x\<^sub>s\<^sub>e`
  have "^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: accept_value.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace>`
  have "{|\<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace>|} \<subseteq> \<V> x\<^sub>s\<^sub>c" by (blast intro: accept_val_env.cases) then
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

lemma accept_pool_let_sync_send_message_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  {|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: accept_state.simps)
  with `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>" by (blast intro: accept_val_env.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s\<^sub>e" by (blast intro: accept_value.cases)
  with `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
  show "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" by (blast intro: accept_val_env.cases)
qed

lemma accept_pool_to_env_let_sync_send: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)
"
proof
  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>"
  and  "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: accept_state.simps)+

  have "{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s"
  proof (cases c)
    case (Ch \<pi> x\<^sub>c)
    assume "c = Ch \<pi> x\<^sub>c" 
    with `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>`
    and  `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>`
    show "{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s" using accept_pool_let_sync_send_values_relate by simp
  qed
  
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" by (simp add: Unit)
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>s" then
    have "\<rho>\<^sub>s x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
  }
  with \<open>{^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>s\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>\<close> 
  show "\<forall>x \<omega>. (\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by simp
qed


lemma accept_pool_let_sync_recv_values_relate: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace> \<Longrightarrow>
  \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace>"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r" "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: accept_state.simps)+

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>`
  have "{|\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>|} \<subseteq> \<V> x\<^sub>r\<^sub>e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>" by (blast intro: accept_val_env.cases)+

  from `{|\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>|} \<subseteq> \<V> x\<^sub>r\<^sub>e`
  have "^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e" by simp

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r\<^sub>e" by (blast intro: accept_value.cases)
  with `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace>`
  have "{|\<lbrace>Ch \<pi>\<^sub>c x\<^sub>c\<rbrace>|} \<subseteq> \<V> x\<^sub>r\<^sub>c" by (blast intro: accept_val_env.cases) then
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


lemma accept_pool_to_stack_let: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps) then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (simp add: accept_state_to_stack_let)
qed

lemma accept_pool_to_env_let_sync_recv: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m" then
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m" "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m" using accept_pool_let_sync_send_message_relate by auto

  assume "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r" by (simp add: accept_state.simps)+


  have "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r"
  proof (cases c)
    case (Ch \<pi>\<^sub>c x\<^sub>c)
    assume "c = Ch \<pi>\<^sub>c x\<^sub>c" 

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>`
    and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
    and `\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m`
    have "\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c" using \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>\<close> accept_pool_let_sync_send_values_relate by blast

    with `c = Ch \<pi>\<^sub>c x\<^sub>c`
    and `\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>`
    and `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    and `\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)`
    and `\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>`
    have "\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" using  accept_pool_let_sync_recv_values_relate by auto

    from `\<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c` and `\<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r`
    show "\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r" by simp
  qed

  from `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>m` and `\<V> x\<^sub>m \<subseteq> \<V> x\<^sub>r`
  have "{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r" by blast

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s" by (simp add: accept_state.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x' = Some \<omega>'" "x' \<noteq> x\<^sub>r" then
    have "\<rho>\<^sub>r x' = Some \<omega>'" by simp
    with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r` 
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
  }
  with `{|\<omega>\<^sub>m|} \<subseteq> \<V> x\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>\<^sub>m`
  show "\<forall>x \<omega>. (\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)) x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>" by auto
qed


lemma accept_preserved_under_sync: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
  and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>"
  and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"
  and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"
  and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"
  and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>"


  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s" by (blast intro: accept_pool_to_exp_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)" by (blast intro: accept_pool_to_env_let_sync_send)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s" by (blast intro: accept_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>s` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>" by (blast intro: accept_state.intros)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r" by (blast intro: accept_pool_to_exp_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> 
  and \<open>\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)\<close> 
  and \<open>\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>\<close> 
  and \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m\<close> \<open>\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>\<close>
  and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close> 
  and \<open>\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>\<close> \<open>\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)" by (blast intro: accept_pool_to_env_let_sync_recv)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close> and \<open>\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)\<close>
  have  "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r" by (blast intro: accept_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>" by (blast intro: accept_state.intros)

  {
    fix \<pi> \<sigma>
    assume  "\<pi> \<noteq> \<pi>\<^sub>s ;; `x\<^sub>s" and "\<pi> \<noteq> \<pi>\<^sub>r ;; `x\<^sub>r"
    and "(\<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma>" then
    have "\<E> \<pi> = Some \<sigma>" by simp
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by (blast intro: accept_state_pool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>r;\<rho>\<^sub>r (x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>` `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>s;\<rho>\<^sub>s (x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>`
  show "\<forall>\<pi> \<sigma>. (\<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)) \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>" by simp

qed


lemma accept_pool_to_env_let_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>" by (blast intro: accept_state_pool.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e" by (blast intro: accept_state.cases) then
  have "{^Chan x} \<subseteq> \<V> x"  by (blast intro: accept_exp.cases)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Ch \<pi> x\<rbrace>" by (simp add: Chan)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>` 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+
  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)) x' = Some \<omega>'" and "x \<noteq> x'"then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (simp add: accept_val_env.simps)
  } with `{^Chan x} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Ch \<pi> x\<rbrace>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed


lemma accept_preserved_under_chan: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>)
"
proof
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: accept_pool_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)" by (blast intro: accept_pool_to_env_let_chan )

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: accept_pool_to_stack_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>);\<kappa>\<rangle>" by (blast intro: accept_state.intros)
  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> ;; `x \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>);\<kappa>\<rangle>)) \<pi>' = Some \<sigma>'" 
    and "\<pi>' \<noteq> \<pi> ;; `x" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (simp add: accept_state_pool.simps)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>);\<kappa>\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> ;; `x \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>);\<kappa>\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


lemma accept_pool_to_env_let_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e" by (blast intro: accept_state.cases) then
  have "{^\<lparr>\<rparr>} \<subseteq> \<V> x"  by (blast intro: accept_exp.cases) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" by (simp add: Unit)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>` 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)

  {
    fix x' \<omega>'
    assume "(\<rho>(x \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>'" and "x \<noteq> x'" then
    have "\<rho> x' = Some \<omega>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "{|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by (blast intro: accept_val_env.cases)
  } with `{^\<lparr>\<rparr>} \<subseteq> \<V> x` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>`
  show "\<forall>x' \<omega>'. (\<rho>(x \<mapsto> \<lbrace>\<rbrace>)) x' = Some \<omega>' \<longrightarrow> {|\<omega>'|} \<subseteq> \<V> x' \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>'" by simp
qed

lemma accept_preserved_under_spawn: "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
"
proof

  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e" by (blast intro: accept_pool_to_exp_let)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)" by (blast intro: accept_pool_to_env_let_spawn)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>" by (blast intro: accept_pool_to_stack_let)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<close>
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<rangle>" by (simp add: accept_state.intros)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>` and `\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e" and "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps)+
  
  from `(\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c" by (blast intro: accept_exp.cases)

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []" by (simp add: accept_stack.Empty)
  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>\<close> \<open>(\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c\<close> 
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>" by (simp add: accept_state.intros)

  {
    fix \<pi>' \<sigma>'
    assume "(\<E>(\<pi> ;; `x \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<rangle>, \<pi> ;; .x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>'"
    and "\<pi>' \<noteq> \<pi> ;; `x" and " \<pi>' \<noteq> \<pi> ;; .x" then
    have "\<E> \<pi>' = Some \<sigma>'" by simp with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by (blast intro: accept_state_pool.cases)
  } with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e;\<rho>(x \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<rangle>` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e\<^sub>c;\<rho>;[]\<rangle>`
  show "\<forall>\<pi>' \<sigma>'. (\<E>(\<pi> ;; `x \<mapsto> \<langle>e;\<rho>(x \<mapsto> \<lbrace>\<rbrace>);\<kappa>\<rangle>, \<pi> ;; .x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)) \<pi>' = Some \<sigma>' \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>'" by simp
qed


theorem accept_preserved_under_concur_step : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>"
  assume "\<E> \<rightarrow> \<E>'" then
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<sigma>')
    assume "\<E>' = \<E> ++ [\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>']"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)"
    and "\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>')" by (simp add:  accept_preserved_under_seq_step_down)
    with `\<E>' = \<E> ++ [\<pi> ;; \<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>']`
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Seq_Step \<pi> x b e \<rho> \<kappa> e' \<rho>')
    assume "\<E>' = \<E> ++ [\<pi> ;; `x \<mapsto> \<langle>e';\<rho>';\<kappa>\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)"
    and "\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e';\<rho>';\<kappa>\<rangle>"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e';\<rho>';\<kappa>\<rangle>)" by (simp add: accept_preserved_under_seq_step)
    with \<open>\<E>' = \<E> ++ [\<pi> ;; `x \<mapsto> \<langle>e';\<rho>';\<kappa>\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Seq_Step_Up \<pi> x b e \<rho> \<kappa> e' \<rho>')
    assume "\<E>' = \<E> ++ [\<pi> ;; \<upharpoonleft>x \<mapsto> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>)"
    and "\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle> \<hookrightarrow> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; \<upharpoonleft>x \<mapsto> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>)" by (simp add: accept_preserved_under_seq_step_up)
    with \<open>\<E>' = \<E> ++ [\<pi> ;; \<upharpoonleft>x \<mapsto> \<langle>e';\<rho>';\<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)
    assume "\<E>' = \<E> ++ [\<pi> ;; `x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>];\<kappa>\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>];\<kappa>\<rangle>)" by (simp add: accept_preserved_under_chan)
    with \<open>\<E>' = \<E> ++ [\<pi> ;; `x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>];\<kappa>\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    assume "\<E>' = \<E> ++ [\<pi> ;; `x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>, \<pi> ;; .x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]"
    assume "leaf \<E> \<pi>" and "\<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; `x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>, \<pi> ;; .x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>)" by (simp add: accept_preserved_under_spawn)
    with \<open>\<E>' = \<E> ++ [\<pi> ;; `x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<rangle>, \<pi> ;; .x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)
    assume "\<E>' = \<E> ++ [\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]"

    assume "leaf \<E> \<pi>\<^sub>s"
    and "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"
    and "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"
    and "leaf \<E> \<pi>\<^sub>r"
    and "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)"
    and "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"
    and "\<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>"
    and "\<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>"
    and "\<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m"
    with \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>\<close>
    have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>)" by (simp add: accept_preserved_under_sync)
    with \<open>\<E>' = \<E> ++ [\<pi>\<^sub>s ;; `x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; `x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]\<close>
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by simp
  qed
qed


theorem accept_preserved_under_concur_step_star : "
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
    show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by (blast intro: accept_preserved_under_concur_step)
  qed with `(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by blast
qed

theorem accept_env_to_precise : "
  (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>"
  {
    fix x
    from `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>`
    have "\<forall>\<omega>. \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x" by (simp add: accept_val_env.simps) then
    have "(case \<rho> x of None \<Rightarrow> {} | Some \<omega> \<Rightarrow> {|\<omega>|}) \<subseteq> \<V> x"  by (simp add: option.case_eq_if) then
    have "(\<parallel>\<rho>\<parallel>) x \<subseteq> \<V> x" by (simp add: env_to_abstract_value_env_def)
  } then
  show "\<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>" by (simp add: abstract_value_env_precision_def)
qed

theorem accept_pool_to_precise : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>;
    \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)
  \<rbrakk>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>" by (simp add: accept_state_pool.simps) then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>" by (simp add: accept_state.simps) then
  show "\<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>"  by (simp add: accept_env_to_precise)
qed

theorem accept_pool_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>" and "\<E> \<rightarrow>* \<E>'" and "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)" then
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>'" by (blast intro: accept_preserved_under_concur_step_star)
  with \<open>\<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
  show "\<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>" by (blast intro: accept_pool_to_precise)
qed


lemma accept_exp_to_pool: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e"

  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty" by (simp add: accept_value_accept_val_env.Any)
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []" by (simp add: accept_stack.Empty)

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<rho> empty` and `(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> []`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>" by (simp add: accept_state.intros)

  have "[[] \<mapsto> \<langle>e; empty; []\<rangle>] [] = Some (\<langle>e; empty; []\<rangle>)" by simp
  with `(\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; empty; []\<rangle>`
  show "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: accept_state_pool.intros)
qed


theorem isnt_abstract_value_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e; 
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
proof -
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e" and "[[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>'"
  and "\<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)"

  from `(\<V>, \<C>) \<Turnstile>\<^sub>e e`
  have "(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]" by (simp add: accept_exp_to_pool)

  from \<open>(\<V>, \<C>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]\<close> \<open>[[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'\<close> \<open>\<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close>
  show "\<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>" by (simp add: accept_pool_sound)
qed


corollary abstracted_value_exists: "
  \<lbrakk>
    \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>;
    \<rho>' x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>" and "\<rho>' x = Some \<omega>"

  from `\<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>`
  have "(\<parallel>\<rho>'\<parallel>) x \<subseteq> \<V> x" by (simp add: abstract_value_env_precision_def)
  with `\<rho>' x = Some \<omega>`
  show "{|\<omega>|} \<subseteq> \<V> x" by (simp add: env_to_abstract_value_env_def)
qed

corollary isnt_abstract_value_sound_coro: "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile>\<^sub>e e ;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
    \<rho>' x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
proof -
  assume "\<rho>' x = Some \<omega>"
  assume "(\<V>, \<C>) \<Turnstile>\<^sub>e e"
  and "[[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'"
  and "\<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" then
  have "\<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>" by (simp add: isnt_abstract_value_sound)
  with `\<rho>' x = Some \<omega>`
  show "{|\<omega>|} \<subseteq> \<V> x" using abstracted_value_exists by blast
qed

end
