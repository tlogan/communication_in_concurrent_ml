theory Static_Live_Channel_Analysis
  imports Main Syntax Dynamic_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

inductive built_on_chan :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"  where
  Chan: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> \<V> x 
    \<rbrakk> \<Longrightarrow> 
    built_on_chan \<V> x\<^sub>c x
  " |
  Send_Evt: "
    \<lbrakk>
      ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x;
      built_on_chan \<V> x\<^sub>c x\<^sub>s\<^sub>c \<or> built_on_chan \<V> x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    built_on_chan \<V> x\<^sub>c x
  " |
  Recv_Evt: "
    \<lbrakk>
      ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x;
      built_on_chan \<V> x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    built_on_chan \<V> x\<^sub>c x
  " |
  Pair: "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> \<V> x;
      built_on_chan \<V> x\<^sub>c x\<^sub>1 \<or> built_on_chan \<V> x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    built_on_chan \<V> x\<^sub>c x
  " |
  Left: "
    \<lbrakk>
      ^(Left x\<^sub>a) \<in> \<V> x;
      built_on_chan \<V> x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_chan \<V> x\<^sub>c x
  " |
  Right: "
    \<lbrakk>
      ^(Right x\<^sub>a) \<in> \<V> x;
      built_on_chan \<V> x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_chan \<V> x\<^sub>c x
  "

type_synonym exp_map = "exp \<Rightarrow> var set"
inductive channel_live :: "(abstract_value_env \<times> exp_map \<times> exp_map) \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" ("_ \<tturnstile> _ \<triangleleft> _" [55,0,55]55) where
  Result: "
    \<lbrakk>
      {y | x\<^sub>c . built_on_chan \<V> x\<^sub>c y} \<subseteq> Ln (RESULT y)
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> RESULT y
  " |
  Let_Unit: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = \<lparr>\<rparr> in e);
      Lx (LET x = \<lparr>\<rparr> in e) \<subseteq> Ln (LET x = \<lparr>\<rparr> in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = \<lparr>\<rparr> in e
  " |
  Let_Chan: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = CHAN \<lparr>\<rparr> in e);
      (Lx (LET x = CHAN \<lparr>\<rparr> in e) - 
        {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}
      ) \<subseteq> Ln (LET x = CHAN \<lparr>\<rparr> in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Send_Evt: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e);
      (
        (Lx (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>s\<^sub>c | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>s\<^sub>c} \<union> 
        {x\<^sub>m | x\<^sub>c .  built_on_chan \<V> x\<^sub>c x\<^sub>m} 
      ) \<subseteq> Ln (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = RECV EVT x\<^sub>r\<^sub>c in e);
      (
        (Lx (LET x = RECV EVT x\<^sub>r\<^sub>c in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>r\<^sub>c | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>r\<^sub>c}
      ) \<subseteq> Ln (LET x = RECV EVT x\<^sub>r\<^sub>c in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = RECV EVT x\<^sub>r\<^sub>c in e
  " |
  Let_Pair: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e);
      (
        (Lx (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>1 | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>1} \<union> 
        {x\<^sub>2 | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>2}
      ) \<subseteq> Ln (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = LEFT x\<^sub>a in e);
      (
        (Lx (LET x = LEFT x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> Ln (LET x = LEFT x\<^sub>a in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = LEFT x\<^sub>a in e
  " |
  Let_Right: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = RIGHT x\<^sub>a in e);
      (
        (Lx (LET x = RIGHT x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> Ln (LET x = RIGHT x\<^sub>a in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = RIGHT x\<^sub>a in e
  " |
  Let_Abs: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = FN f x\<^sub>p . e\<^sub>b  in e);
      (
        (Lx (LET x = FN f x\<^sub>p . e\<^sub>b  in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x})
      ) \<subseteq> Ln (LET x = FN f x\<^sub>p . e\<^sub>b  in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>b;
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = FN f x\<^sub>p . e\<^sub>b  in e
  " |
  Let_Spawn: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = SPAWN e\<^sub>c in e);
      (
        (Lx (LET x = SPAWN e\<^sub>c in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x})
      ) \<subseteq> Ln (LET x = SPAWN e\<^sub>c in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>c;
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SPAWN e\<^sub>c in e
  " |
  Let_Sync: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = SYNC x\<^sub>e in e);
      (
        (Lx (LET x = SYNC x\<^sub>e in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union>
        {x\<^sub>e | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>e}
      ) \<subseteq> Ln (LET x = SYNC x\<^sub>e in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SYNC x\<^sub>e in e
  " |
  Let_Fst: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = FST x\<^sub>a in e);
      (
        (Lx (LET x = FST x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> Ln (LET x = FST x\<^sub>a in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = FST x\<^sub>a in e
  " |
  Let_Snd: "
    \<lbrakk>
      Ln e \<subseteq> Lx (LET x = SND x\<^sub>a in e);
      (
        (Lx (LET x = SND x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>a | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> Ln (LET x = SND x\<^sub>a in e);
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = SND x\<^sub>a in e
  " |
  Let_Case: "
    \<lbrakk>
      Ln e\<^sub>l \<union> Ln e\<^sub>r \<subseteq> Lx (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e);
      (
        (Lx (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union> 
        {x\<^sub>s | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>s}
      ) \<subseteq> Ln (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e);

      Ln e \<subseteq> Lx (RESULT \<lfloor>e\<^sub>l\<rfloor>);
      Lx (RESULT \<lfloor>e\<^sub>l\<rfloor>) \<union> {\<lfloor>e\<^sub>l\<rfloor> | x\<^sub>c . built_on_chan \<V> x\<^sub>c (\<lfloor>e\<^sub>l\<rfloor>)} \<subseteq> Ln (RESULT \<lfloor>e\<^sub>l\<rfloor>);

      Ln e \<subseteq> Lx (RESULT \<lfloor>e\<^sub>r\<rfloor>);
      Lx (RESULT \<lfloor>e\<^sub>r\<rfloor>) \<union> {\<lfloor>e\<^sub>r\<rfloor> | x\<^sub>c . built_on_chan \<V> x\<^sub>c (\<lfloor>e\<^sub>r\<rfloor>)} \<subseteq> Ln (RESULT \<lfloor>e\<^sub>r\<rfloor>);

      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>l;
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e\<^sub>r;
      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow> 
        Ln e \<subseteq> Lx (RESULT \<lfloor>e\<^sub>b\<rfloor>) \<and>
        Lx (RESULT \<lfloor>e\<^sub>b\<rfloor>) \<union> {\<lfloor>e\<^sub>b\<rfloor> | x\<^sub>c . built_on_chan \<V> x\<^sub>c (\<lfloor>e\<^sub>b\<rfloor>)} \<subseteq> Ln (RESULT \<lfloor>e\<^sub>b\<rfloor>) \<and>
        Ln e\<^sub>b \<subseteq> Lx (LET x = APP f x\<^sub>a in e)
      );
      (
        (Lx (LET x = APP f x\<^sub>a in e) - 
          {x | x\<^sub>c . built_on_chan \<V> x\<^sub>c x}) \<union>
        {x\<^sub>a | x\<^sub>c . built_on_chan \<V> x\<^sub>c x\<^sub>a}
      ) \<subseteq> Ln (LET x = APP f x\<^sub>a in e);

      (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, Ln, Lx) \<tturnstile> x\<^sub>c \<triangleleft> LET x = APP f x\<^sub>a in e
  "


(*

DECLARATIVE DECSCRIPTION:

Create predicate chanel_gen_exp to state all expressions that create a channel bound to x\<^sub>c.
Create predicate acitve_exp to state that an is active from a channel exp.
use active exp to limit is_send_path analysis to particular channel creation site.

COMPUTATIONAL TECHNIQUE:
Need to consider only subprograms where channel is live.

Transform 
  Let x = (Sync Send xc mc) in exp_sender
  Let y = (Sync Recv xc) in exp in exp_receiver
into 
  Let x = (Spawn exp_receiver[y\mc]) in exp_sender

*)


end