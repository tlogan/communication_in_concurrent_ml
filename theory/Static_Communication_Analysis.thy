theory Static_Communication_Analysis
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics 
    Static_Traceability 
    Dynamic_Communication_Analysis
    Static_Framework
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


fun chanSet :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var set" where
  "chanSet V x\<^sub>c x = (if built_on_chan V x\<^sub>c x then {x} else {})"


type_synonym label_map = "def_use_label \<Rightarrow> var set"
inductive static_chan_liveness :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "
    \<lbrakk>
      chanSet V x\<^sub>c y \<subseteq> Ln (Use y)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (RESULT y)
  " |
  Let_Unit: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      Lx (Def x) \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (
        (Lx (Def x) - chanSet V x\<^sub>c x) \<union> 
        chanSet V x\<^sub>c x\<^sub>s\<^sub>c \<union> chanSet V x\<^sub>c x\<^sub>m 
      ) \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>r\<^sub>c \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = RECV EVT x\<^sub>r\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (
        (Lx (Def x) - chanSet V x\<^sub>c x) \<union> 
        chanSet V x\<^sub>c x\<^sub>1 \<union> chanSet V x\<^sub>c x\<^sub>2
      ) \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = LEFT x\<^sub>a in e)
  " |
  Let_Right: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = RIGHT x\<^sub>a in e)
  " |
  Let_Abs: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>b;
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>c;
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>e \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SYNC x\<^sub>e in e)
  " |
  Let_Fst: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FST x\<^sub>a in e)
  " |
  Let_Snd: "
    \<lbrakk>
      Ln (defUseLabel e) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SND x\<^sub>a in e)
  " |
  Let_Case: "
    \<lbrakk>
      Ln (defUseLabel e\<^sub>l) \<union> Ln (defUseLabel e\<^sub>r) \<subseteq> Lx (Def x);
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>s \<subseteq> Ln (Def x);

      Ln (defUseLabel e) \<subseteq> Lx (Use (\<lfloor>e\<^sub>l\<rfloor>));
      Lx (Use (\<lfloor>e\<^sub>l\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> Ln (Use (\<lfloor>e\<^sub>l\<rfloor>));

      Ln (defUseLabel e) \<subseteq> Lx (Use (\<lfloor>e\<^sub>r\<rfloor>));
      Lx (Use (\<lfloor>e\<^sub>r\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> Ln (Use (\<lfloor>e\<^sub>r\<rfloor>));

      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>l;
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>r;
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow> 
        Ln (defUseLabel e) \<subseteq> Lx (Use (\<lfloor>e\<^sub>b\<rfloor>)) \<and>
        Lx (Use (\<lfloor>e\<^sub>b\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> Ln (Use (\<lfloor>e\<^sub>b\<rfloor>)) \<and>
        Ln (defUseLabel e\<^sub>b) \<subseteq> Lx (Def x)
      );
      (Lx (Def x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (Def x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = APP f x\<^sub>a in e)
  "



inductive static_live_flow :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_live_flow \<V> \<F> (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(Def x , (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = SEND EVT x\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = RECV EVT x\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = LEFT x\<^sub>p in e)
  " |
  Let_Right: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = RIGHT x\<^sub>p in e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e\<^sub>b;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (Def x, (LNext x), defUseLabel e),
        (Def x, (LSpawn x), defUseLabel e\<^sub>c)
      } \<subseteq> \<F>;
      static_live_flow \<V> \<F> e\<^sub>c;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = SYNC x\<^sub>e in e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = FST x\<^sub>p in e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(Def x, (LNext x), defUseLabel e)} \<subseteq> \<F>;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = SND x\<^sub>p in e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (Def x, (LCall x), defUseLabel e\<^sub>l),
        (Def x, (LCall x), defUseLabel e\<^sub>r),
        (Use (\<lfloor>e\<^sub>l\<rfloor>), (LReturn x), defUseLabel e),
        (Use (\<lfloor>e\<^sub>r\<rfloor>), (LReturn x), defUseLabel e)
      } \<subseteq> \<F>;
      static_live_flow \<V> \<F> e\<^sub>l;
      static_live_flow \<V> \<F> e\<^sub>r;
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow>
        {
          (Def x, (LCall x), defUseLabel e\<^sub>b),
          (Use (\<lfloor>e\<^sub>b\<rfloor>), (LReturn x), defUseLabel e)
        } \<subseteq> \<F>);
      static_live_flow \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_live_flow \<V> \<F> (LET x = APP f x\<^sub>a in e)
  "


definition is_static_send_path :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_send_path \<V> e x\<^sub>c \<pi>\<^sub>y \<equiv> (\<exists> x\<^sub>y x\<^sub>e x\<^sub>s\<^sub>c x\<^sub>m e\<^sub>n . 
    \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
  )"

definition is_static_recv_path :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_recv_path \<V> e x\<^sub>c \<pi>\<^sub>y \<equiv> (\<exists> x\<^sub>y x\<^sub>e x\<^sub>r\<^sub>c e\<^sub>n. 
    \<V> \<turnstile> e \<down> \<pi>\<^sub>y \<mapsto> LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e
  )"

inductive inclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Ordered: "
    \<lbrakk>
      prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
    \<rbrakk> \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
 Spawn_Left: "
    \<pi> @ (LSpawn x) # \<pi>\<^sub>1 \<asymp> \<pi> @ (LNext x) # \<pi>\<^sub>2
 " |
 Spawn_Right: "
    \<pi> @ (LNext x) # \<pi>\<^sub>1 \<asymp> \<pi> @ (LSpawn x) # \<pi>\<^sub>2
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

definition noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"


definition static_one_shot :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  "static_one_shot \<V> Lx x\<^sub>c e \<equiv> 
    (\<forall> eSimp . isSimplifiedExp \<V> Lx x\<^sub>c e eSimp \<longrightarrow> all (is_static_send_path \<V> eSimp x\<^sub>c) singular)"

definition static_one_to_one :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow>  bool" where
  "static_one_to_one \<V> Lx x\<^sub>c e \<equiv> 
    (\<forall> eSimp . isSimplifiedExp \<V> Lx x\<^sub>c e eSimp \<longrightarrow> 
      all (is_static_send_path \<V> eSimp x\<^sub>c) noncompetitive \<and> all (is_static_recv_path \<V> eSimp x\<^sub>c) noncompetitive)"

definition static_fan_out :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  "static_fan_out \<V> Lx x\<^sub>c e \<equiv> 
    (\<forall> eSimp . isSimplifiedExp \<V> Lx x\<^sub>c e eSimp \<longrightarrow> all (is_static_send_path \<V> eSimp x\<^sub>c) noncompetitive)"

definition static_fan_in :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  "static_fan_in \<V> Lx x\<^sub>c e \<equiv> 
    (\<forall> eSimp . isSimplifiedExp \<V> Lx x\<^sub>c e eSimp \<longrightarrow> all (is_static_recv_path \<V> eSimp x\<^sub>c) noncompetitive)"


end
