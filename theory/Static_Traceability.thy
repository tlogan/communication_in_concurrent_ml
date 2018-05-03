theory Static_Traceability
  imports Main Syntax Dynamic_Semantics Static_Semantics Sound_Semantics
    "~~/src/HOL/Library/List"
begin

inductive balanced :: "control_path \<Rightarrow> bool" where
  Empty: "
    balanced []
  " |
  Next: "
    balanced [LNext x]
  " |
  CallReturn: "
    balanced \<pi> \<Longrightarrow>
    balanced ((LCall x) # (\<pi> ;; (LReturn x)))
  " |
  Append: "
    balanced \<pi> \<Longrightarrow> balanced \<pi>' \<Longrightarrow>
    balanced (\<pi> @ \<pi>')
  "

lemma call_return_balanced: "
   balanced [LCall x, LReturn x]
"
using balanced.CallReturn balanced.Empty by fastforce


inductive static_traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> control_path \<Rightarrow> exp \<Rightarrow> bool" ("_ \<turnstile> _ \<down> _ \<mapsto> _" [56,0,0,56]55)  where
  Start: "
    \<V> \<turnstile> e\<^sub>0 \<down> [] \<mapsto> e\<^sub>0
  " |
  Result: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ (LCall x) # \<pi>' \<mapsto> RESULT x\<^sub>r; 
      balanced \<pi>';
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<^sub>n 
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ (LCall x) # (\<pi>';;(LReturn x)) \<mapsto> e\<^sub>n
  " |
  Let_Unit: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = \<lparr>\<rparr> in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Chan: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CHAN \<lparr>\<rparr> in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Prim: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = Prim p in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Spawn_Child: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SPAWN e\<^sub>c in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LSpawn x)  \<mapsto> e\<^sub>c
  " |
  Let_Spawn: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SPAWN e\<^sub>c in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Sync: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SYNC x\<^sub>v in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Fst: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST p in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Snd: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SND p in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LNext x) \<mapsto> e\<^sub>n
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LCall x) \<mapsto> e\<^sub>l
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LCall x) \<mapsto> e\<^sub>r
  " |
  Let_App: " 
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = APP f x\<^sub>a in e\<^sub>n;
      ^Abs f' x' e' \<in> \<V> f
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;(LCall x) \<mapsto> e'
  "


end
