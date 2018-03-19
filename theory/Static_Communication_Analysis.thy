theory Static_Communication_Analysis
  imports Main Syntax Runtime_Semantics Static_Semantics Runtime_Communication_Analysis
begin

inductive built_on_channel :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"  where
  Chan: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> \<V> x 
    \<rbrakk> \<Longrightarrow> 
    built_on_channel \<V> x\<^sub>c x
  " |
  Send_Evt: "
    \<lbrakk>
      ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x;
      built_on_channel \<V> x\<^sub>c x\<^sub>s\<^sub>c \<or> built_on_channel \<V> x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    built_on_channel \<V> x\<^sub>c x
  " |
  Recv_Evt: "
    \<lbrakk>
      ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x;
      built_on_channel \<V> x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    built_on_channel \<V> x\<^sub>c x
  " |
  Pair: "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> \<V> x;
      built_on_channel \<V> x\<^sub>c x\<^sub>1 \<or> built_on_channel \<V> x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    built_on_channel \<V> x\<^sub>c x
  " |
  Left: "
    \<lbrakk>
      ^(Left x\<^sub>a) \<in> \<V> x;
      built_on_channel \<V> x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_channel \<V> x\<^sub>c x
  " |
  Right: "
    \<lbrakk>
      ^(Right x\<^sub>a) \<in> \<V> x;
      built_on_channel \<V> x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_channel \<V> x\<^sub>c x
  "

type_synonym exp_map = "exp \<Rightarrow> var set"
inductive channel_live :: "(abstract_value_env \<times> exp_map \<times> exp_map) \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" ("_ \<tturnstile> _ \<triangleleft> _" [55,0,55]55) where
  Result: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> \<V> x \<longrightarrow> {y} \<subseteq> \<L>n (RESULT y)
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> RESULT y
  " |
  Let_Unit: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = \<lparr>\<rparr> in e);
      \<L>x (LET x = \<lparr>\<rparr> in e) \<subseteq> \<L>n (LET x = \<lparr>\<rparr> in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = \<lparr>\<rparr> in e
  " |
  Let_Chan_Pass: "
    \<lbrakk>
      x\<^sub>c \<noteq> x;
      \<L>n e \<subseteq> \<L>x (LET x = CHAN \<lparr>\<rparr> in e);
      \<L>x (LET x = CHAN \<lparr>\<rparr> in e) \<subseteq> \<L>n (LET x = CHAN \<lparr>\<rparr> in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Chan_Kill: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = CHAN \<lparr>\<rparr> in e);
      \<L>x (LET x = CHAN \<lparr>\<rparr> in e) - {x\<^sub>c} \<subseteq> \<L>n (LET x = CHAN \<lparr>\<rparr> in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x\<^sub>c = CHAN \<lparr>\<rparr> in e
  " |
  Let_Send_Evt: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e);
      (
        (\<L>x (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>s\<^sub>c | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>s\<^sub>c} \<union> 
        {x\<^sub>m | x\<^sub>c .  built_on_channel \<V> x\<^sub>c x\<^sub>m} 
      ) \<subseteq> \<L>n (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = RECV EVT x\<^sub>r\<^sub>c in e);
      (
        (\<L>x (LET x = RECV EVT x\<^sub>r\<^sub>c in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>r\<^sub>c | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>r\<^sub>c}
      ) \<subseteq> \<L>n (LET x = RECV EVT x\<^sub>r\<^sub>c in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = RECV EVT x\<^sub>r\<^sub>c in e
  " |
  Let_Pair: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e);
      (
        (\<L>x (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>1 | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>1} \<union> 
        {x\<^sub>2 | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>2}
      ) \<subseteq> \<L>n (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = LEFT x\<^sub>a in e);
      (
        (\<L>x (LET x = LEFT x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> \<L>n (LET x = LEFT x\<^sub>a in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = LEFT x\<^sub>a in e
  " |
  Let_Right: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = RIGHT x\<^sub>a in e);
      (
        (\<L>x (LET x = RIGHT x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> \<L>n (LET x = RIGHT x\<^sub>a in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = RIGHT x\<^sub>a in e
  " |
  Let_Abs: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = FN f x\<^sub>p . e\<^sub>b  in e);
      (
        (\<L>x (LET x = FN f x\<^sub>p . e\<^sub>b  in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x})
      ) \<subseteq> \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b  in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>b;
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = FN f x\<^sub>p . e\<^sub>b  in e
  " |
  Let_Spawn: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = SPAWN e\<^sub>c in e);
      (
        (\<L>x (LET x = SPAWN e\<^sub>c in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x})
      ) \<subseteq> \<L>n (LET x = SPAWN e\<^sub>c in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>c;
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SPAWN e\<^sub>c in e
  " |
  Let_Sync: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = SYNC x\<^sub>e in e);
      (
        (\<L>x (LET x = SYNC x\<^sub>e in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union>
        {x\<^sub>e | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>e}
      ) \<subseteq> \<L>n (LET x = SYNC x\<^sub>e in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SYNC x\<^sub>e in e
  " |
  Let_Fst: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = FST x\<^sub>a in e);
      (
        (\<L>x (LET x = FST x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> \<L>n (LET x = FST x\<^sub>a in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = FST x\<^sub>a in e
  " |
  Let_Snd: "
    \<lbrakk>
      \<L>n e \<subseteq> \<L>x (LET x = SND x\<^sub>a in e);
      (
        (\<L>x (LET x = SND x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> \<L>n (LET x = SND x\<^sub>a in e);
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SND x\<^sub>a in e
  " |
  Let_Case: "
    \<lbrakk>
      \<L>n e\<^sub>l \<union> \<L>n e\<^sub>r \<subseteq> \<L>x (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e);
      (
        (\<L>x (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>s | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>s}
      ) \<subseteq> \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e);

      \<L>n e \<subseteq> \<L>x (RESULT \<lfloor>e\<^sub>l\<rfloor>);
      \<L>x (RESULT \<lfloor>e\<^sub>l\<rfloor>) \<union> {\<lfloor>e\<^sub>l\<rfloor> | x\<^sub>c . built_on_channel \<V> x\<^sub>c (\<lfloor>e\<^sub>l\<rfloor>)} \<subseteq> \<L>n (RESULT \<lfloor>e\<^sub>l\<rfloor>);

      \<L>n e \<subseteq> \<L>x (RESULT \<lfloor>e\<^sub>r\<rfloor>);
      \<L>x (RESULT \<lfloor>e\<^sub>r\<rfloor>) \<union> {\<lfloor>e\<^sub>r\<rfloor> | x\<^sub>c . built_on_channel \<V> x\<^sub>c (\<lfloor>e\<^sub>r\<rfloor>)} \<subseteq> \<L>n (RESULT \<lfloor>e\<^sub>r\<rfloor>);

      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>l;
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>r;
      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_App: "
    \<lbrakk>

      \<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow> \<L>n e\<^sub>b \<subseteq> \<L>x (LET x = APP f x\<^sub>a in e);
      (
        (\<L>x (LET x = APP f x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_channel \<V> x\<^sub>c x}) \<union>
        {x\<^sub>a | x\<^sub>c . built_on_channel \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> \<L>n (LET x = APP f x\<^sub>a in e);

      \<L>n e \<subseteq> \<L>x (RESULT \<lfloor>e\<^sub>b\<rfloor>);
      \<L>x (RESULT \<lfloor>e\<^sub>b\<rfloor>) \<union> {\<lfloor>e\<^sub>b\<rfloor> | x\<^sub>c . built_on_channel \<V> x\<^sub>c (\<lfloor>e\<^sub>b\<rfloor>)} \<subseteq> \<L>n (RESULT \<lfloor>e\<^sub>b\<rfloor>);

      (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<L>n, \<L>x) \<tturnstile> x\<^sub>c \<triangleleft> LET x = APP f x\<^sub>a in e
  "


inductive life_in_exp :: "exp_map \<Rightarrow> exp => bool" where
  Base: "
    \<lbrakk>
      \<L>n e \<noteq> Set.empty
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n e
  " |
  Abs: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>b \<or>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)
  " |
  Case: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>l \<or>
      life_in_exp \<L>n e\<^sub>r \<or>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " |
  Spawn: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>c \<or>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = SPAWN e\<^sub>c in e\<^sub>n)
  " |
  Let: "
    \<lbrakk>
      life_in_exp \<L>n e\<^sub>n
    \<rbrakk> \<Longrightarrow> 
    life_in_exp \<L>n (LET x = b in e\<^sub>n)
  "
  
fun trim :: "exp_map \<Rightarrow> exp \<Rightarrow> exp" where
  "trim \<L>n (RESULT y) = (RESULT y)" |

  "trim \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)) then
       (LET x = FN f x\<^sub>p . trim \<L>n e\<^sub>b in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " |

  "trim \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)) then
       (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> trim \<L>n e\<^sub>l RIGHT x\<^sub>r |> trim \<L>n e\<^sub>r in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " |

  "trim \<L>n (LET x = SPAWN e\<^sub>c in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = SPAWN e\<^sub>c in e\<^sub>n)) then
       (LET x = SPAWN trim \<L>n e\<^sub>c in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " |

  "trim \<L>n (LET x = b in e\<^sub>n) =
     (if (life_in_exp \<L>n (LET x = b in e\<^sub>n)) then
       (LET x = b in trim \<L>n e\<^sub>n)
     else
       RESULT (Var ''trimmed''))
  " 

(*

identify edges that channels can flow along (messages, sequences, calls, spawns).

identify variables that after which channels are live
identify variables that before which channels are live

liveness trimming:

if channels is not live after self application, 
then if recursive call continuation does not contain any receives or creation of same channel
then replace recursive call continuation with a Result

*)




definition is_static_send_path :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_send_path \<A> x\<^sub>c \<pi>' \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>s\<^sub>c x\<^sub>m e\<^sub>n . 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
  )"

definition is_static_recv_path :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_recv_path \<A> x\<^sub>c \<pi>' \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>r\<^sub>c e\<^sub>n. 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e
  )"

(*  

Reppy/Xiao analyze the subprogram within which a channel is live, 
thus avoiding conflating different instances of a channel with one name, 
such as one created in a loop.

Reppy/Xiao do not distinguish between paths that 
occur in the same run from those that occur in the same subprogram.

Reppy/Xiao consider paths with the same process path to be noncompetitive statically.

*)

inductive inclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Ordered: "
    \<lbrakk>
      prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
    \<rbrakk> \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
 Spawn_Left: "
    \<pi> @ .x # \<pi>\<^sub>1 \<asymp> \<pi> @ `x # \<pi>\<^sub>2
 " |
 Spawn_Right: "
    \<pi> @ `x # \<pi>\<^sub>1 \<asymp> \<pi> @ .x # \<pi>\<^sub>2
 "

lemma inclusive_commut: "
  \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>2 \<asymp> \<pi>\<^sub>1
"
 apply (erule inclusive.cases; auto)
  apply (simp add: Ordered)
  apply (simp add: Ordered)
  apply (simp add: Spawn_Right)
  apply (simp add: Spawn_Left)
done



lemma inclusive_preserved_under_unordered_extension: "
  \<not> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> \<not> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow> \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 ;; l \<asymp> \<pi>\<^sub>2
"
 apply (erule inclusive.cases; auto)
  apply (simp add: Spawn_Left)
  apply (simp add: Spawn_Right)
done

definition singular :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "singular \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"
(* 
     For greater precision replace \<pi>\<^sub>1 = \<pi>\<^sub>2 with (trim e\<^sub>t \<pi>\<^sub>1) = (trim e\<^sub>t \<pi>\<^sub>2)
     where trim returns the longest reachable prefix for e\<^sub>t and
     e\<^sub>t is a smaller program based on the live channel analysis.
*)

definition noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"

definition static_one_shot :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_shot \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) singular"

definition static_one_to_one :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_to_one \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) noncompetitive \<and> all (is_static_recv_path \<A> x\<^sub>c) noncompetitive"

definition static_fan_out :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_out \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) noncompetitive"

definition static_fan_in :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_in \<A> x\<^sub>c \<equiv> all (is_static_recv_path \<A> x\<^sub>c) noncompetitive"


end
