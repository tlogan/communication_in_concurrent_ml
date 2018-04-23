theory Static_Live_Channel_Analysis
  imports Main Syntax Dynamic_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

inductive built_on_chan :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"  where
  Chan: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> V x 
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Send_Evt: "
    \<lbrakk>
      ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>s\<^sub>c \<or> built_on_chan V x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Recv_Evt: "
    \<lbrakk>
      ^Recv_Evt x\<^sub>r\<^sub>c \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Pair: "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>1 \<or> built_on_chan V x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Left: "
    \<lbrakk>
      ^(Left x\<^sub>a) \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Right: "
    \<lbrakk>
      ^(Right x\<^sub>a) \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  "


datatype def_use_label = Def var | Use var

fun defUseLabel :: "exp \<Rightarrow> def_use_label" where
  "defUseLabel (LET x = b in e) = Def x" |
  "defUseLabel (RESULT y) = Use y"


fun chanSet :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var set" where
  "chanSet V x\<^sub>c x = (if built_on_chan V x\<^sub>c x then {x} else {})" 



type_synonym label_map = "def_use_label \<Rightarrow> var set"
inductive channel_live :: "(abstract_value_env \<times> label_map \<times> label_map) \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" ("_ \<tturnstile> _ \<triangleleft> _" [55,0,55]55) where
  Result: "
    \<lbrakk>
      chanSet V x\<^sub>c y \<subseteq> Ln (Use y)
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> RESULT y
  " |
  Let_Unit: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      Lx (Def x) \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = \<lparr>\<rparr> in e
  " |
  Let_Chan: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Send_Evt: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (
        (Lx (Def x) - chanSet V x\<^sub>c x) \<union> 
        chanSet V x\<^sub>c x\<^sub>s\<^sub>c \<union> chanSet V x\<^sub>c x\<^sub>m 
      ) \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>r\<^sub>c \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = RECV EVT x\<^sub>r\<^sub>c in e
  " |
  Let_Pair: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (
        (Lx (Def x) - chanSet V x\<^sub>c x) \<union> 
        chanSet V x\<^sub>c x\<^sub>1 \<union> chanSet V x\<^sub>c x\<^sub>2
      ) \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = LEFT x\<^sub>a in e
  " |
  Let_Right: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = RIGHT x\<^sub>a in e
  " |
  Let_Abs: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>b;
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = FN f x\<^sub>p . e\<^sub>b  in e
  " |
  Let_Spawn: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>c;
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SPAWN e\<^sub>c in e
  " |
  Let_Sync: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>e \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SYNC x\<^sub>e in e
  " |
  Let_Fst: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = FST x\<^sub>a in e
  " |
  Let_Snd: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SND x\<^sub>a in e
  " |
  Let_Case: "
    \<lbrakk>
      Ln (defUseLabel e\<^sub>l) \<union> Ln (defUseLabel e\<^sub>r) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>s \<subseteq> Ln (Def x);

      Ln (defUseLabel e) \<subseteq> Lx (Use (\<lfloor>e\<^sub>l\<rfloor>));
      Lx (Use (\<lfloor>e\<^sub>l\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> Ln (Use (\<lfloor>e\<^sub>l\<rfloor>));

      Ln (defUseLabel e) \<subseteq> Lx (Use (\<lfloor>e\<^sub>r\<rfloor>));
      Lx (Use (\<lfloor>e\<^sub>r\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> Ln (Use (\<lfloor>e\<^sub>r\<rfloor>));

      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>l;
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>r;
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow> 
        Ln (defUseLabel e) \<subseteq> Lx (Use (\<lfloor>e\<^sub>b\<rfloor>)) \<and>
        Lx (Use (\<lfloor>e\<^sub>b\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> Ln (Use (\<lfloor>e\<^sub>b\<rfloor>)) \<and>
        Ln (defUseLabel e\<^sub>b) \<subseteq> Lx (Def x)
      );
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (V, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = APP f x\<^sub>a in e
  "

inductive expStartsWithChan :: "abstract_value_env \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  Let_Chan: "
    expStartsWithChan V xC (LET xC = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Sync_Recv_Evt: "
    {^Chan xC} \<subseteq> V x \<Longrightarrow>
    expStartsWithChan V xC (LET x = RECV EVT xRC in e)
  "


inductive isLiveFragment :: "label_map \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool" where
  TrimEnd: "
    Set.is_empty (Lx (Def x)) \<Longrightarrow>
    isLiveFragment Lx (LET x = b in e) (LET x = b in RESULT y)
  " |
  TrimStart: "
    Set.is_empty (Lx (Def x)) \<Longrightarrow>
    isLiveFragment Lx e liveExp \<Longrightarrow>
    isLiveFragment Lx (LET x = b in e) liveExp
  " |
  Live_Let: "
    \<not> Set.is_empty (Lx (Def x)) \<Longrightarrow>
    isLiveFragment Lx e liveExp \<Longrightarrow>
    isLiveFragment Lx (LET x = b in e) (LET x = b in liveExp)
  " |
  Live_Result: "
    isLiveFragment Lx (RESULT x) (RESULT y)
  "



(* TO DO: ensure that the abstract value env doesn't need hold values of new spawn variables*)
inductive isSimplifiedExp :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool" where
  Let_Spawn: "
    isSimplifiedExp V Lx xC e eNext \<Longrightarrow>
    isSimplifiedExp V Lx xC e eChild \<Longrightarrow>
    isSimplifiedExp V Lx xC e (LET x = SPAWN eChild in eNext)
  " |
  Let_Chan: "
    isLiveFragment Lx e (LET xC = CHAN \<lparr>\<rparr> in eNext) \<Longrightarrow>
    isSimplifiedExp V Lx xC e (LET xC = CHAN \<lparr>\<rparr> in eNext)
  " |
  Let_Sync_Recv_Evt: "
    isLiveFragment Lx e (LET y = SYNC xRE in eNext) \<Longrightarrow>
    {^Chan xC} \<subseteq> V y \<Longrightarrow>
    {^Recv_Evt xRC} \<subseteq> V xRE \<Longrightarrow>
    isSimplifiedExp V Lx xC e (LET y = SYNC xRE in eNext)
  "

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