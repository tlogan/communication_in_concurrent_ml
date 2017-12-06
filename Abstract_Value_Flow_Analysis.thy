theory Abstract_Value_Flow_Analysis
  imports Main Syntax Semantics
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^_" [61] 61 )

type_synonym abstract_env = "var \<Rightarrow> abstract_value set"

fun result_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>RESULT x\<rfloor> = x" |
  "\<lfloor>LET _ = _ in e\<rfloor> = \<lfloor>e\<rfloor>"

inductive flow :: "abstract_env \<times> abstract_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
  Result: "
    (\<V>, \<C>) \<Turnstile> RESULT x
  " |
  Let_Unit: "
    \<lbrakk> {^\<lparr>\<rparr>} \<subseteq> \<V> x; (\<V>, \<C>) \<Turnstile> e \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk> 
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>) \<Turnstile> e';
      {^Abs f' x' e'} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk> 
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk> 
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk> 
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = RIGHT x\<^sub>p in e
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      \<forall> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> 
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>l
      ;
      \<forall> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>r
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk> 
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk>
      \<forall> x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c . 
        ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>e \<longrightarrow> 
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow>
        {^\<lparr>\<rparr>} \<subseteq> \<V> x \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
      ;
      \<forall> x\<^sub>r\<^sub>c x\<^sub>c . 
        ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>e \<longrightarrow>
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow>
        \<C> x\<^sub>c \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn_Parent: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e\<^sub>c;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = SPAWN e\<^sub>c in e
  "

fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|\<lbrace>Ch \<pi> x\<rbrace>| = ^Chan x" |
  "|\<lbrace>p, \<rho>\<rbrace>| = ^p" |
  "|\<lbrace>\<rbrace>| = ^\<lparr>\<rparr>"

definition env_to_abstract_env :: "(var \<rightharpoonup> val) \<Rightarrow> abstract_env" ("\<parallel>_\<parallel>" [0]61) where
  "\<parallel>\<rho>\<parallel>= (\<lambda> x . (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {|\<omega>|} |
    None \<Rightarrow> {}
  ))"


definition abstract_more_precise :: "abstract_env \<Rightarrow> abstract_env \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "\<V> \<sqsubseteq> \<V>' \<equiv> (\<forall> x . \<V> x \<subseteq> \<V>' x)"


inductive flow_over_value :: "abstract_env \<times> abstract_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<parallel>>" 55)
and  flow_over_env :: "abstract_env \<times> abstract_env \<Rightarrow> (var \<rightharpoonup> val) \<Rightarrow> bool" (infix "\<parallel>\<approx>" 55) 
where
  Unit: "(\<V>, \<C>) \<parallel>> \<lbrace>\<rbrace>" |
  Chan: "(\<V>, \<C>) \<parallel>> \<lbrace>c\<rbrace>" |
  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |
  Pair: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |
  Always_Evt: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<parallel>> \<omega>
      );
      (\<forall> x \<pi> x\<^sub>c . \<rho> x = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace> \<longrightarrow>
        {^Chan x\<^sub>c} \<subseteq> \<C> x\<^sub>c
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
  "

inductive flow_over_stack :: "abstract_env \<times> abstract_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile> _ \<Rrightarrow> _" [56, 0, 56] 55) where
  Empty: "(\<V>, \<C>) \<Turnstile> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> \<W> \<Rrightarrow> \<langle>x, e, \<rho>\<rangle> # \<kappa>
  "


inductive flow_over_state :: "abstract_env \<times> abstract_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e; 
      (\<V>, \<C>) \<parallel>\<approx> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<TTurnstile> <<e, \<rho>, \<kappa>>>
  "

inductive flow_over_pool :: "abstract_env \<times> abstract_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<parallel>\<lless>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<TTurnstile> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<parallel>\<lless> \<E>
  "

lemma flow_state_to_flow_exp: "
  (\<V>, \<C>) \<TTurnstile> <<RESULT x,\<rho>,\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>>> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e\<^sub>\<kappa>
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_stack.cases, auto)
done

lemma flow_over_state_to_env: "
  (\<V>, \<C>) \<TTurnstile> <<RESULT x,\<rho>,\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>>> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
      apply (erule flow_over_state.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (erule flow_over_stack.cases, auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow_over_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x]; auto)
     apply (erule flow_over_stack.cases; auto)+
    apply (erule flow_over_env.cases; auto)+
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
   apply (drule spec[of _ x]; auto)
    apply (erule flow_over_stack.cases; auto)+
   apply (erule flow_over_env.cases; auto)+

  apply (rename_tac x' \<omega>')
  apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (rename_tac x' \<omega>')
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
 apply (drule spec[of _ x]; auto)
  apply (erule flow_over_stack.cases; auto)+
 apply (erule flow_over_env.cases; auto)+
done

lemma flow_over_state_to_stack: "
  (\<V>, \<C>) \<TTurnstile> <<RESULT x,\<rho>,\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>>> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
 apply (drule spec)+
 apply (erule impE, auto)
 apply (erule flow_over_stack.cases, auto)+
done

lemma flow_over_state_1: "
  (\<V>, \<C>) \<TTurnstile> <<RESULT x,\<rho>,\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>>> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<TTurnstile> <<e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>),\<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp, auto)
   apply (erule flow_over_state_to_env, auto)
  apply (erule flow_over_state_to_stack, auto)
done

lemma flow_state_to_flow_exp_2: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = \<lparr>\<rparr> in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_over_state_to_env_2: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = \<lparr>\<rparr> in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow.cases, auto)
    apply (rule flow_over_value_flow_over_env.Unit)
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
  apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_over_state_to_stack_2: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = \<lparr>\<rparr> in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_state_2: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = \<lparr>\<rparr> in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<TTurnstile> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp_2)
   apply (erule flow_over_state_to_env_2)
  apply (erule flow_over_state_to_stack_2)
done

lemma flow_over_state_to_exp_3: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = Prim p in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e
"
 apply (erule flow_over_state.cases, auto)  
 apply (erule flow.cases, auto)
done

lemma flow_over_state_to_env_3: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = Prim p in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow.cases, auto)
    apply (erule flow_over_state.cases, auto)
    apply ((erule flow.cases, auto); rule, auto)
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
   apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
  apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_over_state_to_stack_3: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = Prim p in e,\<rho>,\<kappa>>> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_state_3: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = Prim p in e,\<rho>,\<kappa>>> \<Longrightarrow>  (\<V>, \<C>) \<TTurnstile> <<e,\<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>),\<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_over_state_to_exp_3)
   apply (erule flow_over_state_to_env_3)
  apply (erule flow_over_state_to_stack_3)
done

lemma flow_state_to_flow_exp_4: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e\<^sub>l
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
 apply (erule flow_over_env.cases, auto)
 apply ((drule spec)+, auto)
done

lemma flow_state_to_flow_env_4: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
      apply (erule flow_over_state.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>s]; auto)
      apply (erule flow_over_value.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>l']; auto)
      apply (erule flow.cases, auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow_over_env.cases, auto)
     apply (drule spec[of _ x\<^sub>s]; auto)
     apply (erule flow_over_value.cases, auto)
     apply (erule flow_over_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
  apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
  apply (drule spec[of _ x\<^sub>s]; auto)
  apply (erule flow_over_value.cases; auto)
  apply (erule flow_over_env.cases; auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_state_to_flow_stack_4: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
 apply (rule flow_over_stack.Nonempty)
    apply (erule flow_over_state.cases, auto, rename_tac \<omega>)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x\<^sub>s]; auto)
    apply (erule flow.cases, auto)
   apply (erule flow_over_state.cases, auto)
   apply (erule flow.cases, auto)
  apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_state_4: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> (\<V>, \<C>) \<TTurnstile> <<e\<^sub>l,\<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l),\<langle>x,e,\<rho>\<rangle> # \<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp_4, simp, auto)
   apply (erule flow_state_to_flow_env_4, simp, auto)
  apply (erule flow_state_to_flow_stack_4, simp, auto)
done

lemma flow_state_to_flow_exp_5: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e\<^sub>r
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
 apply (erule flow_over_env.cases, auto)
 apply ((drule spec)+, auto)
done

lemma flow_state_to_flow_env_5: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
      apply (erule flow_over_state.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>s]; auto)
      apply (erule flow_over_value.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>r']; auto)
      apply (erule flow.cases, auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow_over_env.cases, auto)
     apply (drule spec[of _ x\<^sub>s]; auto)
     apply (erule flow_over_value.cases, auto)
     apply (erule flow_over_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
  apply (rename_tac x' \<omega>')
  apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
  apply (drule spec[of _ x\<^sub>s]; auto)
  apply (erule flow_over_value.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (rename_tac x' \<omega>')
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_state_to_flow_stack_5: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
 apply (rule flow_over_stack.Nonempty)
    apply (erule flow_over_state.cases, auto, rename_tac \<omega>)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x\<^sub>s]; auto)
    apply (erule flow.cases, auto)
   apply (erule flow_over_state.cases, auto)
   apply (erule flow.cases, auto)
  apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_state_5: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<TTurnstile> <<e\<^sub>r,\<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r),\<langle>x,e,\<rho>\<rangle> # \<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp_5, simp, auto)
   apply (erule flow_state_to_flow_env_5, simp, auto)
  apply (erule flow_state_to_flow_stack_5, simp, auto)
done


lemma flow_state_to_flow_exp_6: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = FST x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_state_to_flow_env_6: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = FST x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<omega>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
      apply (erule flow_over_state.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>p]; auto)
      apply (erule flow_over_value.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>1]; auto)
      apply (erule flow.cases, auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow_over_env.cases, auto)
     apply (drule spec[of _ x\<^sub>p]; auto)
     apply (erule flow_over_value.cases, auto)
     apply (erule flow_over_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
  apply (rename_tac x' \<omega>')
  apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
  apply (drule spec[of _ x\<^sub>p]; auto)
  apply (erule flow_over_value.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (rename_tac x' \<omega>')
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_state_to_flow_stack_6: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = FST x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_state_6: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = FST x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<TTurnstile> <<e,\<rho>(x \<mapsto> \<omega>),\<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp_6, simp, auto)
   apply (erule flow_state_to_flow_env_6, simp, auto)
  apply (erule flow_state_to_flow_stack_6, simp, auto)
done

lemma flow_state_to_flow_exp_7: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = SND x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_state_to_flow_env_7: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = SND x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<omega>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
      apply (erule flow_over_state.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>p]; auto)
      apply (erule flow_over_value.cases, auto)
      apply (erule flow_over_env.cases, auto)
      apply (drule spec[of _ x\<^sub>2]; auto)
      apply (erule flow.cases, auto)
      apply (drule spec[of _ x\<^sub>1]; auto)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow_over_env.cases, auto)
     apply (drule spec[of _ x\<^sub>p]; auto)
     apply (erule flow_over_value.cases, auto)
     apply (erule flow_over_env.cases, auto)
    apply (rename_tac x' \<omega>')
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
   apply (rename_tac x' \<omega>')
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
  apply (rename_tac x' \<omega>')
  apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
  apply (drule spec[of _ x\<^sub>p]; auto)
  apply (erule flow_over_value.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (rename_tac x' \<omega>')
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_state_to_flow_stack_7: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = SND x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_state_7: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = SND x\<^sub>p in e,\<rho>,\<kappa>>> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<V>, \<C>) \<TTurnstile> <<e,\<rho>(x \<mapsto> \<omega>),\<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp_7, simp, auto)
   apply (erule flow_state_to_flow_env_7, simp, auto)
  apply (erule flow_state_to_flow_stack_7, simp, auto)
done

lemma flow_state_to_flow_exp_8: "
 (\<V>, \<C>) \<TTurnstile> <<LET x = APP f x\<^sub>a in e,\<rho>,\<kappa>>> \<Longrightarrow> 
 \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
 (\<V>, \<C>) \<Turnstile> e\<^sub>l
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
 apply (erule flow_over_env.cases, auto)
 apply (drule spec[of _ f]; auto)
 apply (erule flow_over_value.cases, auto)
done

lemma flow_state_to_flow_env_8: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = APP f x\<^sub>a in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
           apply (erule flow_over_state.cases, auto)
           apply (erule flow.cases, auto, (drule spec)+, auto)
            apply (erule flow_over_env.cases, auto, (drule spec)+, auto)
           apply (erule flow_over_env.cases, auto)
          apply (erule flow_over_state.cases, auto)
          apply (erule flow_over_env.cases, auto)
         apply (erule flow_over_state.cases, auto)
         apply (erule flow_over_env.cases, auto)
         apply (drule spec[of _ f]; auto)
         apply (erule flow_over_value.cases, auto)
        apply (erule flow_over_state.cases, auto)
        apply (erule flow_over_env.cases, auto)
       apply (erule flow_over_state.cases, auto)
       apply (erule flow_over_env.cases, auto)
       apply (frule spec[of _ f])
       apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
       apply (drule spec[of _ x\<^sub>a])
       apply (drule spec[of _ \<omega>\<^sub>a], auto)
       apply (erule flow.cases, auto)
       apply (drule spec[of _ q])
       apply (drule spec[of _ f\<^sub>l])
       apply (drule spec[of _ q'])
       apply (drule spec[of _ x\<^sub>l])
       apply (drule spec[of _ q''])
       apply (drule spec[of _ e\<^sub>l]; auto)
      apply (erule flow_over_state.cases, auto)
      apply (erule flow_over_env.cases, auto)
     apply (rename_tac x' \<omega>)
     apply (erule flow_over_state.cases, auto)
     apply (erule flow_over_env.cases, auto)
     apply (frule spec[of _ f])
     apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
     apply (drule spec[of _ x\<^sub>a])
     apply (drule spec[of _ \<omega>\<^sub>a]; auto)
     apply (erule flow_over_value.cases, auto)
     apply (erule flow_over_env.cases, auto)
    apply (rename_tac x' \<omega>)
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
    apply (frule spec[of _ f])
    apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
    apply (drule spec[of _ x\<^sub>a])
    apply (drule spec[of _ \<omega>\<^sub>a]; auto)
    apply (erule flow_over_value.cases, auto)
    apply (erule flow_over_env.cases, auto)
   apply (rename_tac x' \<omega>)
   apply (erule flow_over_state.cases, auto)
   apply (erule flow_over_env.cases, auto)
  apply (rename_tac x' \<omega>)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
apply (rename_tac x' \<omega>)
apply (erule flow_over_state.cases, auto)
apply (erule flow_over_env.cases, auto)
apply (frule spec[of _ f])
apply (drule spec[of _ "\<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>"])
apply (drule spec[of _ x\<^sub>a])
apply (drule spec[of _ \<omega>\<^sub>a]; auto)
apply (erule flow_over_value.cases, auto)
apply (erule flow_over_env.cases, auto)
done

lemma flow_state_to_flow_stack_8: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = APP f x\<^sub>a in e,\<rho>,\<kappa>>> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
"
 apply (rule flow_over_stack.Nonempty)
    apply (erule flow_over_state.cases, auto) 
    apply (erule flow.cases, auto)
    apply (erule flow_over_env.cases, (drule spec)+, auto)
   apply (erule flow_over_state.cases, auto) 
   apply (erule flow.cases, auto)
  apply (erule flow_over_state.cases, auto) 
 apply (erule flow_over_state.cases, auto) 
done

lemma flow_over_state_8: "
  (\<V>, \<C>) \<TTurnstile> <<LET x = APP f x\<^sub>a in e,\<rho>,\<kappa>>> \<Longrightarrow>
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<V>, \<C>) \<TTurnstile> <<e\<^sub>l,\<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a),\<langle>x,e,\<rho>\<rangle> # \<kappa>>>
"
 apply (rule flow_over_state.Any)
    apply (erule flow_state_to_flow_exp_8, simp, auto)
   apply (erule flow_state_to_flow_env_8, simp, auto)
  apply (erule flow_state_to_flow_stack_8, simp, auto)
done

theorem flow_over_state_preservation : "
  \<lbrakk>
    (\<V>, \<C>) \<TTurnstile> \<sigma>; 
    \<sigma> \<hookrightarrow> \<sigma>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<TTurnstile> \<sigma>'
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

lemma flow_seq_step_preservation: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = b in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  <<LET x = b in e,\<rho>,\<kappa>>> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<V>, \<C>) \<parallel>\<lless> \<E>(\<pi> ;; x \<mapsto> \<sigma>')
"
 apply (rule flow_over_pool.Any, auto)
  apply (erule flow_over_pool.cases, auto)
  apply ((drule spec)+, auto)
  apply (erule flow_over_state_preservation, auto)
 apply (erule flow_over_pool.cases, auto)
done

lemma flow_over_pool_to_exp_1: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow> \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> \<pi>\<^sub>s \<noteq> \<pi>\<^sub>r \<Longrightarrow> (\<V>, \<C>) \<Turnstile> e\<^sub>s
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_over_pool_to_env_1: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> <<e\<^sub>s,\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>),\<kappa>\<^sub>s>>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> <<e\<^sub>r,\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m),\<kappa>\<^sub>r>>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow> \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> \<pi>\<^sub>s \<noteq> \<pi>\<^sub>r \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
    apply (erule flow_over_pool.cases, auto)
    apply (frule spec[of _ \<pi>\<^sub>s])
    apply (drule spec[of _ \<pi>\<^sub>r])
    apply (drule spec[of _ "<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>"])
    apply (drule spec[of _ "<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>"])
    apply (drule mp[of "\<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) "])
    apply (drule mp[of "\<E> \<pi>\<^sub>r = Some (<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>)"], auto)
    apply (erule flow_over_state.cases[of "(\<V>, \<C>)" "<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>"], auto)
    apply (erule flow_over_state.cases[of "(\<V>, \<C>)" "<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>"], auto)
    apply (erule flow_over_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>r"], auto)
    apply (erule flow_over_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s"], auto)
    apply (thin_tac "\<forall>x \<pi> x\<^sub>c. \<rho>\<^sub>r x = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace> \<longrightarrow> ^Chan x\<^sub>c \<in> \<C> x\<^sub>c")
    apply (thin_tac "\<forall>x \<pi> x\<^sub>c. \<rho>\<^sub>s x = Some \<lbrace>Ch \<pi> x\<^sub>c\<rbrace> \<longrightarrow> ^Chan x\<^sub>c \<in> \<C> x\<^sub>c")
    apply (drule spec[of _ x\<^sub>r\<^sub>e])
    apply (drule spec[of _ x\<^sub>s\<^sub>e])
    apply (drule spec[of _ "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"])
    apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
    apply (drule mp[of "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"], simp)
    apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
    apply (erule flow_over_value.cases[of "(\<V>, \<C>)" "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"]; auto)
    apply (erule flow_over_value.cases[of "(\<V>, \<C>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
    apply (erule flow_over_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>r\<^sub>e"], auto)
    apply (erule flow_over_env.cases[of "(\<V>, \<C>)" "\<rho>\<^sub>s\<^sub>e"], auto)
    apply (erule flow.cases[of "(\<V>, \<C>)" "LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r"]; auto)
    apply (erule flow.cases[of "(\<V>, \<C>)" "LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s"]; auto)
    apply (thin_tac "\<forall>x\<^sub>s\<^sub>c x\<^sub>m. ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow> ^\<lparr>\<rparr> \<in> \<V> x\<^sub>r \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c)")
    apply (thin_tac "\<forall>x\<^sub>r\<^sub>c. ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>s\<^sub>e \<longrightarrow> (\<forall>x\<^sub>c. ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>s)")
    apply (drule spec[of _ x\<^sub>r\<^sub>c])
    apply (drule spec[of _ x\<^sub>r\<^sub>c])
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (case_tac c; auto)
sorry

lemma flow_over_pool_to_stack_1: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>"], auto)
 apply (erule flow_over_state.cases, auto) 
done

lemma flow_over_pool_to_exp_2: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> 
  \<E> \<pi>\<^sub>r = Some (<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile> e\<^sub>r
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>r])
 apply (drule spec[of _ "<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_over_pool_to_env_2: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> <<e\<^sub>s,\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>),\<kappa>\<^sub>s>>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> <<e\<^sub>r,\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m),\<kappa>\<^sub>r>>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>) \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow> \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
    apply (erule flow_over_pool.cases, auto)
    
    apply (frule spec[of _ \<pi>\<^sub>s])
    apply (drule spec[of _ "<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>"])
    apply ((erule impE[of "\<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>)"]), simp)
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x\<^sub>s\<^sub>e])
    apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"], auto)
    apply (erule flow_over_value.cases, auto)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (drule spec[of _ "\<lbrace>c\<rbrace>"], auto)
    apply (erule flow.cases, auto)
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (drule spec[of _ x\<^sub>s\<^sub>c])
    apply (drule spec[of _ x\<^sub>m])
    apply (drule mp[of "^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>s\<^sub>e"], simp)


    apply (drule spec[of _ \<pi>\<^sub>r])
    apply (drule spec[of _ "<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>"])
    apply ((erule impE[of "\<E> \<pi>\<^sub>r = Some (<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>)"]), simp)
    apply (erule flow_over_state.cases, auto)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x\<^sub>r\<^sub>e], auto)
    apply (erule flow_over_value.cases[of "(\<V>, \<C>)" "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"], auto)
    apply (erule flow_over_env.cases, auto)
    apply (drule spec[of _ x\<^sub>r\<^sub>c])
    apply (drule spec[of _ "\<lbrace>c\<rbrace>"], auto)
    apply (erule flow.cases[of "(\<V>, \<C>)" "LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r"], auto)
    apply (drule spec[of "\<lambda>x\<^sub>c. ^Recv_Evt x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>e \<longrightarrow> \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>r" x\<^sub>r\<^sub>c], auto)
    apply (drule spec[of _ x\<^sub>r\<^sub>c])
    apply (drule spec[of _ x\<^sub>m], auto)

sorry

lemma flow_over_pool_to_stack_2: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) \<Longrightarrow>
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>"], auto)
 apply (erule flow_over_state.cases, auto) 
done


lemma flow_let_sync_preservation: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> <<e\<^sub>s,\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>),\<kappa>\<^sub>s>>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> <<e\<^sub>r,\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m),\<kappa>\<^sub>r>>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (<<LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s,\<rho>\<^sub>s,\<kappa>\<^sub>s>>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (<<LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r,\<rho>\<^sub>r,\<kappa>\<^sub>r>>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> (\<V>, \<C>) \<parallel>\<lless> \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> <<e\<^sub>s,\<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>),\<kappa>\<^sub>s>>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> <<e\<^sub>r,\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m),\<kappa>\<^sub>r>>)
"
 apply (rule flow_over_pool.Any, auto)
     apply (rule flow_over_state.Any)
      apply (erule flow_over_pool_to_exp_1, auto)
     apply (erule flow_over_pool_to_env_1, auto)
    apply (erule flow_over_pool_to_stack_1, auto)
   apply (rule flow_over_state.Any)
     apply (erule flow_over_pool_to_exp_1, auto)
    apply ((erule flow_over_pool_to_env_1), auto)
   apply (erule flow_over_pool_to_stack_1, auto)
   apply (unfold not_def, erule impE, auto)
   apply (rule flow_over_state.Any)
   apply (erule flow_over_pool_to_exp_2, auto)
     apply (erule flow_over_pool_to_env_2, auto)
    apply (erule flow_over_pool_to_stack_2, auto)
   apply (rule flow_over_state.Any)
     apply (erule flow_over_pool_to_exp_2, auto)
    apply ((erule flow_over_pool_to_env_2), auto)
   apply (erule flow_over_pool_to_stack_2, auto)
sorry

lemma flow_over_pool_to_exp_3: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> e
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_over_pool_to_env_3: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
    apply (erule flow_over_pool.cases, auto)
    apply (drule spec[of _ \<pi>])
    apply (drule spec[of _ "<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>"], auto)
    apply (erule flow_over_state.cases, auto)
    apply (erule flow.cases, auto)
   apply (rule flow_over_value_flow_over_env.Chan)
  apply (rename_tac x' \<omega>)
  apply (erule flow_over_pool.cases, auto)
  apply (drule spec[of _ \<pi>])
  apply (drule spec[of _ "<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>"], auto)
  apply (erule flow_over_state.cases, auto)
  apply (erule flow.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (rename_tac x' \<omega>)
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_over_pool_to_stack_3: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_pool_to_exp_4: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; x \<Longrightarrow> \<E> \<pi>' = Some (<<e',\<rho>',\<kappa>'>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> e'
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "<<e',\<rho>',\<kappa>'>>"], auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_pool_to_env_4: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; x \<Longrightarrow> \<E> \<pi>' = Some (<<e',\<rho>',\<kappa>'>>) \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>'
"
 apply (rule flow_over_value_flow_over_env.Any, auto)
  apply (erule flow_over_pool.cases, auto)
  apply (drule spec[of _ \<pi>'])
  apply (drule spec[of _ "<<e',\<rho>',\<kappa>'>>"], auto)
  apply (erule flow_over_state.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "<<e',\<rho>',\<kappa>'>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_over_pool_to_stack_4: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; x \<Longrightarrow> \<E> \<pi>' = Some (<<e',\<rho>',\<kappa>'>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e'\<rfloor>) \<Rrightarrow> \<kappa>'
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "<<e',\<rho>',\<kappa>'>>"], auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_let_chan_preservation: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = CHAN \<lparr>\<rparr> in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<lless> \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>),\<kappa>>>)
"
 apply (rule flow_over_pool.Any, auto)
  apply (rule flow_over_state.Any)
    apply (erule flow_over_pool_to_exp_3, auto)
   apply (erule flow_over_pool_to_env_3, auto)
  apply (erule flow_over_pool_to_stack_3, auto)
 apply (case_tac "\<sigma>", rename_tac e' \<rho>' \<kappa>', auto)
 apply (rule flow_over_state.Any)
   apply (erule flow_over_pool_to_exp_4, auto)
   apply (erule flow_over_pool_to_env_4, auto)
  apply (erule flow_over_pool_to_stack_4, auto)
done


lemma flow_over_pool_to_exp_5: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> e
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_over_pool_to_env_5: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)"
 apply (rule flow_over_value_flow_over_env.Any, auto)
    apply (erule flow_over_pool.cases, auto)
    apply (drule spec[of _ \<pi>])
    apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
    apply (erule flow_over_state.cases, auto)
    apply (erule flow.cases, auto)
   apply (rule flow_over_value_flow_over_env.Unit)
  apply (rename_tac x' \<omega>)
  apply (erule flow_over_pool.cases, auto)
  apply (drule spec[of _ \<pi>])
  apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
  apply (erule flow_over_state.cases, auto)
  apply (erule flow.cases, auto)
  apply (erule flow_over_env.cases, auto)
 apply (rename_tac x' \<omega>)
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
 apply (erule flow_over_env.cases, auto)
done

lemma flow_over_pool_to_stack_5: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_pool_to_exp_6: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> e\<^sub>c
"   
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
 apply (erule flow.cases, auto)
done

lemma flow_over_pool_to_env_6: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<approx> \<rho>
"   
 apply (erule flow_over_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>"], auto)
 apply (erule flow_over_state.cases, auto)
done

lemma flow_over_pool_to_stack_6: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []
"   
 apply (rule flow_over_stack.Empty)
done


lemma flow_let_spawn_preservation: "
  (\<V>, \<C>) \<parallel>\<lless> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (<<LET x = SPAWN e\<^sub>c in e,\<rho>,\<kappa>>>) \<Longrightarrow> 
  (\<V>, \<C>) \<parallel>\<lless> \<E>(\<pi> ;; x \<mapsto> <<e,\<rho>(x \<mapsto> \<lbrace>\<rbrace>),\<kappa>>>, \<pi>;;. \<mapsto> <<e\<^sub>c,\<rho>,[]>>)
"
  apply (rule flow_over_pool.Any, auto)
    apply (rule flow_over_state.Any)
     apply (erule flow_over_pool_to_exp_5, auto)
    apply (erule flow_over_pool_to_env_5, auto)
   apply (erule flow_over_pool_to_stack_5, auto)
   apply (unfold not_def, erule impE, auto)
   apply (rule flow_over_state.Any)
     apply (erule flow_over_pool_to_exp_6, auto)
    apply (erule flow_over_pool_to_env_6, auto)
   apply (erule flow_over_pool_to_stack_6, auto)
  apply (erule flow_over_pool.cases, auto)
done

theorem flow_preservation : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<parallel>\<lless> \<E>'
"
 apply (erule concur_step.cases, auto)
    apply (erule flow_seq_step_preservation, auto)
   apply ((erule flow_let_sync_preservation; blast?), auto)
  apply (erule flow_let_chan_preservation, auto)
 apply (erule flow_let_spawn_preservation, auto)
done

theorem flow_preservation_star' : "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow>
  ((\<V>, \<C>) \<parallel>\<lless> \<E> \<longrightarrow> (\<V>, \<C>) \<parallel>\<lless> \<E>')
"
 thm star.induct[of concur_step]
 apply (erule star.induct[of concur_step], auto)
 apply (rename_tac \<E> \<E>' \<E>'')
 apply (erule notE)
 apply (erule flow_preservation, auto)
done
 

theorem flow_preservation_star : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>;  
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<parallel>\<lless> \<E>'
"
by (drule flow_preservation_star', auto)

theorem flow_over_env_precision : "
  (\<V>, \<C>) \<parallel>\<approx> \<rho>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (unfold abstract_more_precise_def, unfold env_to_abstract_env_def)
 apply (rule allI, rename_tac x)
 apply (case_tac "\<rho> x = None", auto, rename_tac \<omega>)
 apply (erule flow_over_env.cases, auto)
done

theorem flow_over_state_precision : "
  (\<V>, \<C>) \<TTurnstile> <<e, \<rho>, \<kappa>>>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (erule flow_over_state.cases, auto)
 apply (erule flow_over_env_precision)
done

lemma flow_over_pool_to_state: "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>; 
    \<E> \<pi> = Some \<sigma> 
  \<rbrakk>
  \<Longrightarrow>
  (\<V>, \<C>) \<TTurnstile> \<sigma>
"
 apply (erule flow_over_pool.cases)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ \<sigma>])
 apply (erule impE, auto)
done
  
theorem flow_over_pool_precision : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>;
    \<E> \<pi> = Some (<<e, \<rho>, \<kappa>>>)
  \<rbrakk>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (drule flow_over_pool_to_state, simp)
 apply (erule flow_over_state_precision)
done

theorem lift_flow_exp_to_state: "(\<V>, \<C>) \<Turnstile> e \<Longrightarrow> (\<V>, \<C>) \<TTurnstile> <<e, empty, []>>"
 apply (rule flow_over_state.Any, auto)
 apply (rule+, auto, rule)
done

theorem  lift_flow_state_to_pool: "(\<V>, \<C>) \<TTurnstile> \<sigma> \<Longrightarrow> (\<V>, \<C>) \<parallel>\<lless> [[] \<mapsto> \<sigma>]"
  apply (rule flow_over_pool.Any)
  apply (case_tac "\<pi> = []", auto)
done

theorem lift_flow_exp_to_pool: "(\<V>, \<C>) \<Turnstile> e \<Longrightarrow> (\<V>, \<C>) \<parallel>\<lless> [[] \<mapsto> <<e, empty, []>>]"
  apply (drule lift_flow_exp_to_state)
  apply (erule lift_flow_state_to_pool)
done

theorem flow_over_pool_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>; 
    \<E> \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (<<e', \<rho>', \<kappa>'>>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule flow_preservation_star [of \<V> \<C> _ \<E>'], auto)
 apply (erule flow_over_pool_precision [of \<V> \<C> \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done


theorem flow_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile> e; 
    [[] \<mapsto> <<e, empty, []>>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (<<e', \<rho>', \<kappa>'>>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule lift_flow_exp_to_pool)
 apply (erule flow_over_pool_sound [of \<V> \<C> _ \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done

end