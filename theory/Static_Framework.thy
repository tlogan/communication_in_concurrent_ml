theory Static_Framework
  imports Main Syntax Dynamic_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

datatype def_use_label = Def var | Use var

fun defUseLabel :: "exp \<Rightarrow> def_use_label" where
  "defUseLabel (LET x = b in e) = Def x" |
  "defUseLabel (RESULT y) = Use y"


type_synonym flow_set = "(def_use_label \<times> control_label \<times> def_use_label) set"


inductive static_flow :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_flow \<V> \<F> (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(Def x , (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = SEND EVT x\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = RECV EVT x\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = LEFT x\<^sub>p in e)
  " |
  Let_Right: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = RIGHT x\<^sub>p in e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e\<^sub>b;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (Def x, (LNext x), defUseLabel e),
        (Def x, (LSpawn x), defUseLabel e\<^sub>c)
      } \<subseteq> \<F>;
      static_flow \<V> \<F> e\<^sub>c;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = SYNC x\<^sub>e in e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = FST x\<^sub>p in e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = SND x\<^sub>p in e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (Def x, (LCall x), defUseLabel e\<^sub>l),
        (Def x, (LCall x), defUseLabel e\<^sub>r),
        (Use (\<lfloor>e\<^sub>l\<rfloor>), (LReturn x), defUseLabel e),
        (Use (\<lfloor>e\<^sub>r\<rfloor>), (LReturn x), defUseLabel e)
      } \<subseteq> \<F>;
      static_flow \<V> \<F> e\<^sub>l;
      static_flow \<V> \<F> e\<^sub>r;
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow>
        {
          (Def x, (LCall x), defUseLabel e\<^sub>b),
          (Use (\<lfloor>e\<^sub>b\<rfloor>), (LReturn x), defUseLabel e)
        } \<subseteq> \<F>);
      static_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow \<V> \<F> (LET x = APP f x\<^sub>a in e)
  "


inductive is_subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  Refl : "
    is_subexp e e
  " | 
  Let: "
    is_subexp e\<^sub>n e \<Longrightarrow>
    is_subexp (LET x = b in e\<^sub>n) e
  " | 
  Let_Spawn_Child: "
    is_subexp e\<^sub>c e \<Longrightarrow>
    is_subexp (LET x = SPAWN e\<^sub>c in e\<^sub>n) e
  " |
  Let_Case_Left: "
    is_subexp e\<^sub>l e \<Longrightarrow>
    is_subexp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e
  " |
  Let_Case_Right: "
    is_subexp e\<^sub>r e \<Longrightarrow>
    is_subexp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e
  " |
  Let_Abs_Body: "
    is_subexp e\<^sub>b e \<Longrightarrow>
    is_subexp (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) e
  "


(* TO DO: ensure that the abstract value env doesn't need hold values of new spawn variables*)
(* find channel creation subexpressions*)
(* transforming LET x = SYNC xSE in e into LET x = SPAWN eCh in e, should work*)
(* How to determine eCh? Find the SYNC RECV EVT sub expression, where channel values send site's values*)

(*

Xiao says "
The next definition
and lemma show that for each dynamic send/receive site of
any channel instance, there is a corresponding approximate path in
the extended CFG, which starts from the channel’s creation site
(TLL modification: or from ad-hoc spawn expression to tie in sync recv_evts into corresponding chan expression with sync send_evt)
"

dynamic flow of channel instance:
let \<pi> \<in> Sendst(k)
PathHtk(\<pi>) = \<langle>\<pi>1, \<pi>2\<rangle>. This means that
\<pi>1(1)
1 is the creation site of k, k flows through \<pi>1 and then is sent as
a message from \<pi>1(−1) to \<pi>2(1) on some channel instance, and some
value is sent on k at \<pi>2(−1) is a send on k.

for every dynamic path to a send or recv site in an expression,
there is a corresponding modified path in a corresponding modified expression.


Q: Need to modify dynamic semantics with history of communication?
A: Seems like the only reason is because modified paths use 
the sender's front with receiver's back for passed channels.  
We can simply use the back, the path of which is already recorded in the trace_pool.

(\<pi>Send, Ch \<pi>C xC, \<pi>Recv)

Xiao says:

"
Lemma 6 For any trace t 2 Trace(p), channel instance k in t, and any control path \<pi>1, \<pi>2 2
Sendst(k) [ Recvst(k), if \<pi>1 6= \<pi>2 then PathHtk(\<pi>1) 6= PathHtk(\<pi>2).

Proof: This is obvious from dynamic semantics on Section 3.1.
"

Need to consider only subprograms where channel is live.o

Check how Xiao proves that graph of subprogram actually represents the whole program.

strategy 1:
Find all the fragments that start with (LET x = CHAN \<lparr>\<rparr> in e).
Find all the fragments that start with (LET x = RECV eRE in e).
join fragments with initial (LET * = SPAWN (LET x = RECV eRE in) in (LET x = CHAN \<lparr>\<rparr> in e))

incomplete strategy 2:
Transform 
  Let x = (Sync Send xc mc) in exp_sender
  Let y = (Sync Recv xc) in exp in exp_receiver
into 
  Let x = (Spawn exp_receiver) in exp_sender

the path to exp receiver will change from (LNext a) (LSpawn b) (LNext c) ... (LNext y) to (LSpawn x)  
There's actually no need for subs

*)


end