theory Abstract_Value_Flow_Analysis
  imports Main Syntax Semantics
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^_" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"
type_synonym bind_env = "var \<Rightarrow> bind set" 
fun result_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>RESULT x\<rfloor> = x" |
  "\<lfloor>LET _ = _ in e\<rfloor> = \<lfloor>e\<rfloor>"

fun site_set :: "exp \<Rightarrow> (var + var) set" where
  "site_set (RESULT _) = {}" |
  "site_set (LET x = SPAWN _ in _) = {Inl x, Inr x}" |
  "site_set (LET x = _ in e) = {Inl x}"

locale flow_analysis = 
  fixes 
    let_unit :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_abs :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> (var \<times> var \<times> exp) \<Rightarrow> exp \<Rightarrow> bool" and 
    let_pair :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> (var \<times> var) \<Rightarrow> exp \<Rightarrow> bool" and 
    let_left :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_right :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_send_evt :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> (var \<times> var) \<Rightarrow> exp \<Rightarrow> bool" and 
    let_recv_evt :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_case :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> (var \<times> var \<times> exp \<times> var \<times> exp) \<Rightarrow> exp \<Rightarrow> bool" and 
    let_fst :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_snd :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_app :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> (var \<times> var) \<Rightarrow> exp \<Rightarrow> bool" and 
    let_sync :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_chan :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" and 
    let_spawn :: "'a \<Rightarrow> abstract_value_env \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool"

context flow_analysis
begin

inductive accept_exp :: "'a \<times> abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result: "
    (\<G>, \<V>) \<Turnstile>\<^sub>e (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk> 
      let_unit \<G> \<V> x e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk>
      let_abs \<G> \<V> x (f', x', e') e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e';
      (\<G>, \<V>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk> 
      let_pair \<G> \<V> x (x\<^sub>1, x\<^sub>2) e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk>
      let_left \<G> \<V> x x\<^sub>l e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = LEFT x\<^sub>l in e
  " |
  Let_Right : "
    \<lbrakk>
      let_right \<G> \<V> x x\<^sub>r e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = RIGHT x\<^sub>r in e
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      let_send_evt \<G> \<V> x (x\<^sub>c, x\<^sub>m) e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      let_recv_evt \<G> \<V> x x\<^sub>c e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      let_case \<G> \<V> x (x\<^sub>s, x\<^sub>l, e\<^sub>l, x\<^sub>r, e\<^sub>r) e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  "|
  Let_Fst: "
    \<lbrakk> 
      let_fst \<G> \<V> x x\<^sub>p e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      let_snd \<G> \<V> x x\<^sub>p e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      let_app \<G> \<V> x (f, x\<^sub>a) e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk> 
      let_sync \<G> \<V> x x\<^sub>e e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      let_chan \<G> \<V> x e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn: "
    \<lbrakk>
      let_spawn \<G> \<V> x e\<^sub>c e;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e\<^sub>c;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<G>, \<V>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e
  "


fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|\<lbrace>Ch \<pi> x\<rbrace>| = ^Chan x" |
  "|\<lbrace>p, \<rho>\<rbrace>| = ^p" |
  "|\<lbrace>\<rbrace>| = ^\<lparr>\<rparr>"

definition env_to_abstract_value_env :: "(var \<rightharpoonup> val) \<Rightarrow> abstract_value_env" ("\<parallel>_\<parallel>" [0]61) where
  "\<parallel>\<rho>\<parallel> = (\<lambda> x . (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {|\<omega>|} |
    None \<Rightarrow> {}
  ))"

definition abstract_value_env_precision :: "abstract_value_env \<Rightarrow> abstract_value_env \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "\<V> \<sqsubseteq> \<V>' \<equiv> (\<forall> x . \<V> x \<subseteq> \<V>' x)"


inductive accept_value :: "'a \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  accept_val_env :: "'a \<times> abstract_value_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "(\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" |
  Chan: "(\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>c\<rbrace>" |
  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e;
      (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |
  Pair: "
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |
  Always_Evt: "
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<G>, \<V>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive accept_stack :: "'a \<times> abstract_value_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<G>, \<V>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<G>, \<V>) \<Turnstile>\<^sub>e e;
      (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive accept_state :: "'a \<times> abstract_value_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<G>, \<V>) \<Turnstile>\<^sub>e e;
      (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive accept_state_pool :: "'a \<times> abstract_value_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>
  "


(*******Soundness*****)

(*
*)
lemma flow_state_to_flow_exp: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma> \<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e\<^sub>\<kappa>
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_stack.cases, auto)
done

lemma flow_over_state_to_env: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>\<kappa>\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply (drule spec)+
 apply (erule impE, auto)
 apply (erule accept_stack.cases, auto)+
done

lemma flow_over_state_1: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<Longrightarrow> \<rho> x = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp, auto)
   apply (erule flow_over_state_to_env, auto)
  apply (erule flow_over_state_to_stack, auto)
done

lemma flow_state_to_flow_exp_2: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done


lemma flow_over_state_to_env_2: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)
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
sorry

lemma flow_over_state_to_stack_2: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_2: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_2)
   apply (erule flow_over_state_to_env_2)
  apply (erule flow_over_state_to_stack_2)
done

(*
lemma flow_over_state_to_exp_3: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)  
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_state_to_env_3: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_3: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_over_state_to_exp_3)
   apply (erule flow_over_state_to_env_3)
  apply (erule flow_over_state_to_stack_3)
done

lemma flow_state_to_flow_exp_4: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e\<^sub>l
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply ((drule spec)+, auto)
done

lemma flow_state_to_flow_env_4: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Left x\<^sub>l', \<rho>\<^sub>l\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>l; \<rho>(x\<^sub>l \<mapsto> \<omega>\<^sub>l); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_4, simp, auto)
   apply (erule flow_state_to_flow_env_4, simp, auto)
  apply (erule flow_state_to_flow_stack_4, simp, auto)
done

lemma flow_state_to_flow_exp_5: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e\<^sub>r
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply ((drule spec)+, auto)
done

lemma flow_state_to_flow_env_5: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> x\<^sub>s = Some \<lbrace>prim.Right x\<^sub>r', \<rho>\<^sub>r\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>r; \<rho>(x\<^sub>r \<mapsto> \<omega>\<^sub>r); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_5, simp, auto)
   apply (erule flow_state_to_flow_env_5, simp, auto)
  apply (erule flow_state_to_flow_stack_5, simp, auto)
done


lemma flow_state_to_flow_exp_6: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_state_to_flow_env_6: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_6: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>1 = Some \<omega> \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_6, simp, auto)
   apply (erule flow_state_to_flow_env_6, simp, auto)
  apply (erule flow_state_to_flow_stack_6, simp, auto)
done

lemma flow_state_to_flow_exp_7: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_state_to_flow_env_7: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<omega>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state.cases, auto)
done

lemma flow_over_state_7: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> x\<^sub>p = Some \<lbrace>prim.Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace> \<Longrightarrow> \<rho>\<^sub>p x\<^sub>2 = Some \<omega> \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; \<rho>(x \<mapsto> \<omega>); \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_7, simp, auto)
   apply (erule flow_state_to_flow_env_7, simp, auto)
  apply (erule flow_state_to_flow_stack_7, simp, auto)
done

lemma flow_state_to_flow_exp_8: "
 (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
 \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
 (\<G>, \<V>) \<Turnstile>\<^sub>e  e\<^sub>l
"
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
 apply (erule accept_val_env.cases, auto)
 apply (drule spec[of _ f]; auto)
 apply (erule accept_value.cases, auto)
done

lemma flow_state_to_flow_env_8: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow> 
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<Rrightarrow> \<langle>x,e,\<rho>\<rangle> # \<kappa>
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<Longrightarrow>
  \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> \<Longrightarrow> \<rho> x\<^sub>a = Some \<omega>\<^sub>a \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e\<^sub>l; \<rho>\<^sub>l(f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a); \<langle>x,e,\<rho>\<rangle> # \<kappa>\<rangle>
"
 apply (rule accept_state.Any)
    apply (erule flow_state_to_flow_exp_8, simp, auto)
   apply (erule flow_state_to_flow_env_8, simp, auto)
  apply (erule flow_state_to_flow_stack_8, simp, auto)
done
*)

theorem flow_over_state_preservation : "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma> \<sigma>; 
    \<sigma> \<hookrightarrow> \<sigma>'
  \<rbrakk> \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma> \<sigma>'
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
sorry

lemma flow_seq_step_preservation: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>' \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; x \<mapsto> \<sigma>')
"
 apply (rule accept_state_pool.Any, auto)
  apply (erule accept_state_pool.cases, auto)
  apply ((drule spec)+, auto)
  apply (erule flow_over_state_preservation, auto)
 apply (erule accept_state_pool.cases, auto)
done

(*
lemma flow_over_pool_to_exp_1: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>e e\<^sub>s
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_1: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>)
"
apply (rule accept_value_accept_val_env.Any; auto)
    apply (erule accept_state_pool.cases, auto)
    apply (frule spec[of _ \<pi>\<^sub>s])
    apply (drule spec[of _ \<pi>\<^sub>r])
    apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"])
    apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"])
    apply (drule mp[of "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) "])
    apply (drule mp[of "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"], auto)
    apply (erule accept_state.cases[of "(\<G>, \<V>)" "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
    apply (erule accept_state.cases[of "(\<G>, \<V>)" "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
    apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>r"], auto)
    apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>s"], auto)
    apply (drule spec[of _ x\<^sub>r\<^sub>e])
    apply (drule spec[of _ x\<^sub>s\<^sub>e])
    apply (drule spec[of _ "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"])
    apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
    apply (drule mp[of "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"], simp)
    apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
    apply (erule accept_value.cases[of "(\<G>, \<V>)" "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"]; auto)
    apply (erule accept_value.cases[of "(\<G>, \<V>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
    apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>r\<^sub>e"], auto)
    apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>s\<^sub>e"], auto)
    apply (erule accept_exp.cases[of "(\<G>, \<V>)" "LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r"]; auto)
    apply (erule accept_exp.cases[of "(\<G>, \<V>)" "LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s"]; auto)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>s\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>s
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>s])
 apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
 apply (erule accept_state.cases, auto) 
done

lemma flow_over_pool_to_exp_2: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>e  e\<^sub>r
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>r])
 apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_2: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow> 
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow> 
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m)
"
apply (rule accept_value_accept_val_env.Any; auto)
      apply (erule accept_state_pool.cases, auto)
      apply (frule spec[of _ \<pi>\<^sub>s])
      apply (drule spec[of _ \<pi>\<^sub>r])
      apply (drule spec[of _ "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"])
      apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"])
      apply (drule mp[of "\<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) "])
      apply (drule mp[of "\<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>)"], auto)
      apply (erule accept_state.cases[of "(\<G>, \<V>)" "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
      apply (erule accept_state.cases[of "(\<G>, \<V>)" "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
      apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>r"], auto)
      apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>s"], auto)
      apply (drule spec[of _ x\<^sub>r\<^sub>e])
      apply (drule spec[of _ x\<^sub>s\<^sub>e])
      apply (drule spec[of _ "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"])
      apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
      apply (drule mp[of "\<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"], simp)
      apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
      apply (erule accept_value.cases[of "(\<G>, \<V>)" "\<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>"]; auto)
      apply (erule accept_value.cases[of "(\<G>, \<V>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
      apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>r\<^sub>e"], auto)
      apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>s\<^sub>e"], auto)
      apply (erule accept_exp.cases[of "(\<G>, \<V>)" "LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r"]; auto)
      apply (erule accept_exp.cases[of "(\<G>, \<V>)" "LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s"]; auto)
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
    apply (erule accept_state.cases[of "(\<G>, \<V>)" "\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>"], auto)
    apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>s"], auto)
    apply (drule spec[of _ x\<^sub>s\<^sub>e])
    apply (drule spec[of _ "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"])
    apply (drule mp[of "\<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>"]; auto)
    apply (erule accept_value.cases[of "(\<G>, \<V>)" "\<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> "]; auto)
    apply (erule accept_val_env.cases[of "(\<G>, \<V>)" "\<rho>\<^sub>s\<^sub>e"], auto)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<Rrightarrow> \<kappa>\<^sub>r
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>\<^sub>r])
 apply (drule spec[of _ "\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>"], auto)
 apply (erule accept_state.cases, auto) 
done

lemma flow_let_sync_preservation: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  \<E>' = \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>s \<Longrightarrow>
  \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m \<Longrightarrow>
  leaf \<E> \<pi>\<^sub>r \<Longrightarrow>
  \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>) \<Longrightarrow>
  \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace> \<Longrightarrow>
  \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>(\<pi>\<^sub>s ;; x\<^sub>s \<mapsto> \<langle>e\<^sub>s; \<rho>\<^sub>s(x\<^sub>s \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; x\<^sub>r \<mapsto> \<langle>e\<^sub>r; \<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m); \<kappa>\<^sub>r\<rangle>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_3: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_exp_4: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>e  e'
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_env_4: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>'
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> \<pi>' \<noteq> \<pi> ;; x \<Longrightarrow> \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e'\<rfloor>) \<Rrightarrow> \<kappa>'
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>'])
 apply (drule spec[of _ "\<langle>e'; \<rho>'; \<kappa>'\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_let_chan_preservation: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>); \<kappa>\<rangle>)
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>e  e
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_5: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>(x \<mapsto> \<lbrace>\<rbrace>)"
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
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
"
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_exp_6: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>e  e\<^sub>c
"   
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
 apply (erule accept_exp.cases, auto)
done

lemma flow_over_pool_to_env_6: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
"   
 apply (erule accept_state_pool.cases, auto)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ "\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>"], auto)
 apply (erule accept_state.cases, auto)
done

lemma flow_over_pool_to_stack_6: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow> 
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<kappa>  \<V> (\<lfloor>e\<^sub>c\<rfloor>) \<Rrightarrow> []
"   
 apply (rule accept_stack.Empty)
done


lemma flow_let_spawn_preservation: "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow> \<E>' = \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow> \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>) \<Longrightarrow> 
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>(\<pi> ;; x \<mapsto> \<langle>e; \<rho>(x \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>, \<pi>;;.x \<mapsto> \<langle>e\<^sub>c; \<rho>; []\<rangle>)
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


*)
(*******)
theorem flow_preservation : "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>'
"
 apply (erule concur_step.cases, auto)
    apply (erule flow_seq_step_preservation, auto)
   apply ((erule flow_let_sync_preservation; blast?), auto)
  apply (erule flow_let_chan_preservation, auto)
 apply (erule flow_let_spawn_preservation, auto)
sorry


theorem flow_preservation_star' : "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow>
  ((\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>')
"
 apply (erule star.induct[of concur_step], auto)
 apply (rename_tac \<E> \<E>' \<E>'')
 apply (erule notE)
 apply (erule flow_preservation, auto)
done
 

theorem flow_preservation_star : "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>;  
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>'
"
by (drule flow_preservation_star', auto)

theorem flow_over_env_precision : "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<rho> \<rho>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (unfold abstract_value_env_precision_def, unfold env_to_abstract_value_env_def)
 apply (rule allI, rename_tac x)
 apply (case_tac "\<rho> x = None", auto, rename_tac \<omega>)
 apply (erule accept_val_env.cases, auto)
done

theorem flow_over_state_precision : "
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (erule accept_state.cases, auto)
 apply (erule flow_over_env_precision)
done

lemma flow_over_pool_to_state: "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<pi> = Some \<sigma> 
  \<rbrakk>
  \<Longrightarrow>
  (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<sigma>
"
 apply (erule accept_state_pool.cases)
 apply (drule spec[of _ \<pi>])
 apply (drule spec[of _ \<sigma>])
 apply (erule impE, auto)
done

  
theorem flow_over_pool_precision : "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>;
    \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>)
  \<rbrakk>
  \<Longrightarrow>
  \<parallel>\<rho>\<parallel> \<sqsubseteq> \<V>
"
 apply (drule flow_over_pool_to_state, simp)
 apply (erule flow_over_state_precision)
done

theorem lift_flow_exp_to_state: "(\<G>, \<V>) \<Turnstile>\<^sub>e e \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<langle>e; empty; []\<rangle>"
 apply (rule accept_state.Any, auto)
 apply (rule+, auto, rule)
done

theorem  lift_flow_state_to_pool: "(\<G>, \<V>) \<Turnstile>\<^sub>\<sigma>  \<sigma> \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<sigma>]"
  apply (rule accept_state_pool.Any)
  apply (case_tac "\<pi> = []", auto)
done

theorem lift_flow_exp_to_pool: "(\<G>, \<V>) \<Turnstile>\<^sub>e  e \<Longrightarrow> (\<G>, \<V>) \<Turnstile>\<^sub>\<E> [[] \<mapsto> \<langle>e; empty; []\<rangle>]"
  apply (drule lift_flow_exp_to_state)
  apply (erule lift_flow_state_to_pool)
done

theorem flow_over_pool_sound : "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>\<E> \<E>; 
    \<E> \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule flow_preservation_star[of \<G> \<V> _ \<E>'], auto)
 apply (erule flow_over_pool_precision[of \<G> \<V> \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done

theorem flow_sound : "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>e e; 
    [[] \<mapsto> \<langle>e; empty; []\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>)
  \<rbrakk> \<Longrightarrow>
  \<parallel>\<rho>'\<parallel> \<sqsubseteq> \<V>
"
 apply (drule lift_flow_exp_to_pool)
 apply (erule flow_over_pool_sound [of \<G> \<V> _ \<E>' \<pi> e' \<rho>' \<kappa>'], auto)
done

corollary flow_sound_coro: "
  \<lbrakk>
    (\<G>, \<V>) \<Turnstile>\<^sub>e e ;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>);
    \<rho>' x = Some \<omega>
  \<rbrakk> \<Longrightarrow>
  {|\<omega>|} \<subseteq> \<V> x
"
  apply (drule flow_sound; assumption?)
  apply (unfold abstract_value_env_precision_def)
  apply (unfold env_to_abstract_value_env_def)
  apply (drule spec[of _ x]; auto)
done






end



(*****)

inductive accept_exp :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk> 
      {\<lparr>\<rparr>} \<subseteq> \<X> x;
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (*site_set e \<in> \<Y> (Inl x)*)
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk>
      {FN f' x' . e' } \<subseteq> \<X> f';
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e';
      {FN f' x' . e' } \<subseteq> \<X> x;
      {^Abs f' x' e'} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk> 
      {\<lparr>x\<^sub>1, x\<^sub>2\<rparr>} \<subseteq> \<X> x;
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk> 
      {LEFT x\<^sub>p} \<subseteq> \<X> x;
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk>
      {RIGHT x\<^sub>p} \<subseteq> \<X> x;
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = RIGHT x\<^sub>p in e
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      {SEND EVT x\<^sub>c x\<^sub>m} \<subseteq> \<X> x;
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      {RECV EVT x\<^sub>c} \<subseteq> \<X> x;
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      {CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r} \<subseteq> \<X> x;
      \<forall> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e\<^sub>l
      ;
      \<forall> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e\<^sub>r
      ;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk> 
      {FST x\<^sub>p} \<subseteq> \<X> x;
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      {SND x\<^sub>p} \<subseteq> \<X> x;
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      {APP f x\<^sub>a} \<subseteq> \<X> x;
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk>
      {SYNC x\<^sub>e} \<subseteq> \<X> x;
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
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      {CHAN \<lparr>\<rparr>} \<subseteq> \<X> x;
      {^Chan x} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn: "
    \<lbrakk>
      {SPAWN e\<^sub>c} \<subseteq> \<X> x;
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e\<^sub>c;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e
  "


fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|\<lbrace>Ch \<pi> x\<rbrace>| = ^Chan x" |
  "|\<lbrace>p, \<rho>\<rbrace>| = ^p" |
  "|\<lbrace>\<rbrace>| = ^\<lparr>\<rparr>"

definition env_to_abstract_value_env :: "(var \<rightharpoonup> val) \<Rightarrow> abstract_value_env" ("\<parallel>_\<parallel>" [0]61) where
  "\<parallel>\<rho>\<parallel>= (\<lambda> x . (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {|\<omega>|} |
    None \<Rightarrow> {}
  ))"


definition abstract_value_env_precision :: "abstract_value_env \<Rightarrow> abstract_value_env \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "\<V> \<sqsubseteq> \<V>' \<equiv> (\<forall> x . \<V> x \<subseteq> \<V>' x)"


inductive accept_value :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  accept_val_env :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "(\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" |
  Chan: "(\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>c\<rbrace>" |
  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |
  Pair: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |
  Always_Evt: "
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive accept_stack :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive accept_state :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive accept_state_pool :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>, \<X>) \<Turnstile>\<^sub>\<E> \<E>
  "
   
end