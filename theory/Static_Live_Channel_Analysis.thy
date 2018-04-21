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


inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" ("_ \<preceq>\<^sub>e _" [56,56]55) where
  Refl : "
    e \<preceq>\<^sub>e e
  " | 
  Let: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = b in e\<^sub>n)
  " | 
  Let_Spawn_Child: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>c
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = SPAWN e\<^sub>c in e\<^sub>n)
  " |
  Let_Case_Left: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>l
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " | 
  Let_Case_Right: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>r
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " |
  Let_Abs_Body: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>b 
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)
  "



lemma subexp_trans: "
  e\<^sub>x \<preceq>\<^sub>e e\<^sub>y \<Longrightarrow> e\<^sub>y \<preceq>\<^sub>e e\<^sub>z \<Longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>z
"
proof -
  assume "e\<^sub>x \<preceq>\<^sub>e e\<^sub>y"
  assume "e\<^sub>y \<preceq>\<^sub>e e\<^sub>z" then
  have "(\<forall> e\<^sub>x . e\<^sub>x \<preceq>\<^sub>e e\<^sub>y \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>z)"
  proof (induction rule: subexp.induct)
    case (Refl e)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e" by simp
  next
    case (Let e e\<^sub>n x b)
    assume "e \<preceq>\<^sub>e e\<^sub>n" "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>n"

    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>n \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = b in e\<^sub>n" by (simp add: subexp.Let) 
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>n`
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = b in e\<^sub>n" by blast
  next
    case (Let_Spawn_Child e e\<^sub>c x e\<^sub>n)
    assume "e \<preceq>\<^sub>e e\<^sub>c" "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>c"

    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>c \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = SPAWN e\<^sub>c in e\<^sub>n" by (simp add: subexp.Let_Spawn_Child)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>c`
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = SPAWN e\<^sub>c in e\<^sub>n"by blast
  next
    case (Let_Case_Left e e\<^sub>l x x\<^sub>s x\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    assume "e \<preceq>\<^sub>e e\<^sub>l" "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>l"

    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>l \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by (simp add: subexp.Let_Case_Left)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>l`
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by blast
  next
    case (Let_Case_Right e e\<^sub>r x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>n)
    assume "e \<preceq>\<^sub>e e\<^sub>r" "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>r"

    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>r \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by (simp add: subexp.Let_Case_Right)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>r`
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by blast
  next
    case (Let_Abs_Body e e\<^sub>b x f x\<^sub>p e\<^sub>n)
    assume "e \<preceq>\<^sub>e e\<^sub>b" "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>b"

    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>b \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n" by (simp add: subexp.Let_Abs_Body)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>b`
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n" by blast
  qed 
  with `e\<^sub>x \<preceq>\<^sub>e e\<^sub>y`
  show "e\<^sub>x \<preceq>\<^sub>e e\<^sub>z" by blast
qed

lemma subexp1: "
  e\<^sub>n \<preceq>\<^sub>e LET x = b in e\<^sub>n
"
by (simp add: Let Refl)


(*

Need to consider only subprograms where channel is live.

Transform 
  Let x = (Sync Send xc mc) in exp_sender
  Let y = (Sync Recv xc) in exp in exp_receiver
into 
  Let x = (Spawn exp_receiver) in exp_sender

the path to exp receiver will change from (LNext a) (LSpawn b) (LNext c) ... (LNext y) to (LSpawn x)  
There's actually no need for subs

*)

end