theory Static_Traceability
  imports Main Syntax Dynamic_Semantics Static_Semantics Sound_Semantics
    "~~/src/HOL/Library/List"
begin

inductive path_balanced :: "control_path \<Rightarrow> bool" ("\<downharpoonright>_\<upharpoonleft>" [0]55) where
  Empty: "
    \<downharpoonright>[]\<upharpoonleft>
  " |
  Linear: "
    \<downharpoonright>[`x]\<upharpoonleft>
  " |
  Up_Down: "
    \<downharpoonright>\<pi>\<upharpoonleft> \<Longrightarrow>
    \<downharpoonright>(\<upharpoonleft>x # (\<pi> ;; \<downharpoonleft>x))\<upharpoonleft>
  " |
  Append: "
    \<downharpoonright>\<pi>\<upharpoonleft> \<Longrightarrow> \<downharpoonright>\<pi>'\<upharpoonleft> \<Longrightarrow>
    \<downharpoonright> (\<pi> @ \<pi>') \<upharpoonleft>
  "

lemma up_down_balanced: "
   \<downharpoonright>[\<upharpoonleft>x, \<downharpoonleft>x] \<upharpoonleft>
"
using Up_Down path_balanced.Empty by fastforce


inductive traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> control_path \<Rightarrow> exp \<Rightarrow> bool" ("_ \<turnstile> _ \<down> _ \<mapsto> _" [56,0,0,56]55)  where
  Start: "
    \<V> \<turnstile> e\<^sub>0 \<down> [] \<mapsto> e\<^sub>0
  " |
  Result: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ \<upharpoonleft>x # \<pi>' \<mapsto> RESULT x\<^sub>r; 
      \<downharpoonright>\<pi>'\<upharpoonleft>;
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<^sub>n 
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ \<upharpoonleft>x # (\<pi>';;\<downharpoonleft>x) \<mapsto> e\<^sub>n
  " |
  Let_Unit: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = \<lparr>\<rparr> in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Chan: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CHAN \<lparr>\<rparr> in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Prim: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = Prim p in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Spawn_Child: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SPAWN e\<^sub>c in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;.x \<mapsto> e\<^sub>c
  " |
  Let_Spawn: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SPAWN e\<^sub>c in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Sync: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SYNC x\<^sub>v in e\<^sub>n;
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Fst: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST p in e\<^sub>n;
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Snd: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SND p in e\<^sub>n;
      (* constraint below not necessary for our purposes*)
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n;
      (* constraint below not necessary for our purposes*)
      ^Left x\<^sub>l' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;\<upharpoonleft>x \<mapsto> e\<^sub>l
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n;
      ^Right x\<^sub>r' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;\<upharpoonleft>x \<mapsto> e\<^sub>r
  " |
  Let_App: " 
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = APP f x\<^sub>a in e\<^sub>n;
      ^Abs f' x' e' \<in> \<V> f
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;\<upharpoonleft>x \<mapsto> e'
  "


end