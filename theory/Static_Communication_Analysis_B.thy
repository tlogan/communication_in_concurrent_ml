theory Static_Communication_Analysis
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Static_Framework Sound_Framework
    Dynamic_Communication_Analysis 
begin

(*




inductive static_flow_set :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> (var \<Rightarrow> node_label \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_flow_set V F may_be_recv_site (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(NLet x , ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = SEND EVT x\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = RECV EVT x\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = LEFT x\<^sub>p in e)
  " |
  Let_Right: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = RIGHT x\<^sub>p in e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e\<^sub>b;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (NLet x, ENext, nodeLabel e),
        (NLet x, ESpawn, nodeLabel e\<^sub>c)
      } \<subseteq> F;
      static_flow_set V F may_be_recv_site e\<^sub>c;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      (\<forall> xSC xM xC y.
        {^Send_Evt xSC xM} \<subseteq> V xSE \<longrightarrow>
        {^Chan xC} \<subseteq> V xSC \<longrightarrow>
        may_be_recv_site xC (NLet y) \<longrightarrow>
        {(NLet x, ESend xSE, NLet y)} \<subseteq> F
      );
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = SYNC xSE in e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = FST x\<^sub>p in e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = SND x\<^sub>p in e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (NLet x, ECall x, nodeLabel e\<^sub>l),
        (NLet x, ECall x, nodeLabel e\<^sub>r),
        (NResult (\<lfloor>e\<^sub>l\<rfloor>), EReturn x, nodeLabel e),
        (NResult (\<lfloor>e\<^sub>r\<rfloor>), EReturn x, nodeLabel e)
      } \<subseteq> F;
      static_flow_set V F may_be_recv_site e\<^sub>l;
      static_flow_set V F may_be_recv_site e\<^sub>r;
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow>
        {
          (NLet x, ECall x, nodeLabel e\<^sub>b),
          (NResult (\<lfloor>e\<^sub>b\<rfloor>), EReturn x, nodeLabel e)
        } \<subseteq> F);
      static_flow_set V F may_be_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_flow_set V F may_be_recv_site (LET x = APP f x\<^sub>a in e)
  "

inductive 
  may_be_built_on_abstract_chan :: "abstract_value_env \<Rightarrow> node_map \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
where
  Chan: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> V x 
    \<rbrakk> \<Longrightarrow> 
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " |
  Send_Evt: "
    \<lbrakk>
      ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> V x;
      may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>s\<^sub>c \<or> may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " |
  Recv_Evt: "
    \<lbrakk>
      ^Recv_Evt x\<^sub>r\<^sub>c \<in> V x;
      may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " |
  Pair: "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> V x;
      may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>1 \<or> may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " |
  Left: "
    \<lbrakk>
      ^(Left x\<^sub>a) \<in> V x;
      may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " |
  Right: "
    \<lbrakk>
      ^(Right x\<^sub>a) \<in> V x;
      may_be_built_on_abstract_chan V Ln x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " |
  Abs: "
    ^Abs f x\<^sub>p e\<^sub>b \<in> V x \<Longrightarrow> 
    \<not> Set.is_empty (Ln (nodeLabel e\<^sub>b) - {x\<^sub>p}) \<Longrightarrow>
    may_be_built_on_abstract_chan V Ln x\<^sub>c x
  " 
(*
  |

  Result: "
    may_be_built_on_abstract_chan V Ln x\<^sub>c x \<Longrightarrow>
    may_be_built_on_abstract_chan_exp V x\<^sub>c (RESULT x)
  " |
  Let: "
    may_be_built_on_abstract_chan V Ln x\<^sub>c x \<or> 
    may_be_built_on_abstract_chan_exp V x\<^sub>c e \<Longrightarrow>
    may_be_built_on_abstract_chan_exp V x\<^sub>c (LET x = b in e)
  "
*)

fun chan_set :: "abstract_value_env \<Rightarrow> node_map \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var set" where
  "chan_set V Ln x\<^sub>c x = (if (may_be_built_on_abstract_chan V Ln x\<^sub>c x) then {x} else {})"


inductive static_chan_liveness :: "abstract_value_env \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "
    \<lbrakk>
      chan_set V Ln x\<^sub>c y = Ln (NResult y)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (RESULT y)
  " |
  Let_Unit: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      Lx (NLet x) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>s\<^sub>c \<union> chan_set V Ln x\<^sub>c x\<^sub>m = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>r\<^sub>c = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = RECV EVT x\<^sub>r\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union>  chan_set V Ln x\<^sub>c x\<^sub>1 \<union> chan_set V Ln x\<^sub>c x\<^sub>2 = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = LEFT x\<^sub>a in e)
  " |
  Let_Right: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = RIGHT x\<^sub>a in e)
  " |
  Let_Abs: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>b;
      (Lx (NLet x) - {x}) \<union> (Ln (nodeLabel e\<^sub>b) - {x\<^sub>p}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>c;
      Ln (nodeLabel e) \<union> Ln (nodeLabel e\<^sub>c) = Lx (NLet x);
      (Lx (NLet x) - {x}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>e = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SYNC x\<^sub>e in e)
  " |
  Let_Fst: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FST x\<^sub>a in e)
  " |
  Let_Snd: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SND x\<^sub>a in e)
  " |
  Let_Case: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>l;
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>r;
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>s \<union> 
         (Ln (nodeLabel e\<^sub>l) - {x\<^sub>l}) \<union> (Ln (nodeLabel e\<^sub>r) - {x\<^sub>r}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c f \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = APP f x\<^sub>a in e)
  "




inductive may_be_static_path :: "flow_set \<Rightarrow> node_label \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty: "
    may_be_static_path F end []
  " |
  Edge: "
    (start, edge, end) \<in> F \<Longrightarrow>
    may_be_static_path F end [(start, edge)]
  " |
  Step: "
    may_be_static_path F end ((middle, edge') # post) \<Longrightarrow>
    (start, edge, middle) \<in> F \<Longrightarrow>
    path = [(start, edge), (middle, edge')] @ post \<Longrightarrow>
    may_be_static_path F end path
  "

inductive static_balanced :: "static_path \<Rightarrow> bool" where
  Empty: "
    static_balanced []
  " |
  Next: "
    static_balanced [(NLet x, ENext)]
  " |
  CallReturn: "
    static_balanced path \<Longrightarrow>
    static_balanced ((NLet x, ECall x) # (path @ [(NResult y, EReturn x)]))
  " |
  Append: "
    path \<noteq> [] \<Longrightarrow>
    static_balanced path \<Longrightarrow>
    path' \<noteq> [] \<Longrightarrow>
    static_balanced path' \<Longrightarrow>
    static_balanced (path @ path')
  "

inductive static_unbalanced :: "static_path \<Rightarrow> bool" where
  Result: "
    static_unbalanced ((NResult y, EReturn x) # post)
  " |
  Next: "
    static_unbalanced post \<Longrightarrow>
    static_unbalanced ((NLet x, ENext) # post)
  "


inductive may_be_static_live_flow :: "flow_set \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> flow_label \<Rightarrow> bool"  where
  Next: "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, ENext, l')
  " |
  Spawn: "
    (l, ESpawn, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, ESpawn, l')
  " |
  Call_Live_Outer: "
    (l, ECall x, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, ECall x, l')
  " |
  Call_Live_Inner: "
    (l, ECall x, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, ECall x, l')
  " |
  Return: "
    (l, EReturn x, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, EReturn x, l')
  " |
  Send: "
    ((NLet xSend), ESend xE, (NLet xRecv)) \<in> F \<Longrightarrow>
    {xE} \<subseteq> (Ln (NLet xSend)) \<Longrightarrow>
    may_be_static_live_flow F Ln Lx ((NLet xSend), ESend xE, (NLet xRecv))
  "

inductive may_be_static_live_path :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> node_label \<Rightarrow> (node_label \<Rightarrow> bool) \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    may_be_static_live_path V F Ln Lx start isEnd []
  " |
  Edge: "
    isEnd end \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (start, edge, end) \<Longrightarrow>
    may_be_static_live_path V F Ln Lx start isEnd [(start, edge)]
  " |
  Step: "
    may_be_static_live_path V F Ln Lx middle isEnd ((middle, edge') # path) \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (start, edge, middle) \<Longrightarrow>
    may_be_static_live_path V F Ln Lx start isEnd ((start, edge) # (middle, edge') # path)
  " |

  Pre_Return: "
    may_be_static_live_path V F Ln Lx (NResult y) isEnd ((NResult y, EReturn x) # post) \<Longrightarrow>
    may_be_static_path  F (NResult y) pre \<Longrightarrow>
    \<not> static_balanced (pre @ [(NResult y, EReturn x)]) \<Longrightarrow>
    \<not> Set.is_empty (Lx (NLet x)) \<Longrightarrow>
    path = pre @ (NResult y, EReturn x) # post \<Longrightarrow>
    may_be_static_live_path V F Ln Lx start isEnd path
  "

(*

inductive may_be_inclusive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Prefix1: "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
  Prefix2: "
    prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
  Spawn1: "
    \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Spawn2: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>2
  " |
  Send1: "
    \<pi> @ (NLet x, ESend xE) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Send2: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESend xE) # \<pi>\<^sub>2
  " |
  Kite: "
    p1 @ [(NLet x1, ESend xE1)] \<noteq> (p2 @ [(NLet x2, ESend xE2)]) \<Longrightarrow>
    ((NLet x, ENext) # p1 @ [(NLet x1, ESend xE1)] @ p1') \<asymp> 
      ((NLet x, ENext) # p2 @ [(NLet x2, ESend xE2)] @ p2')
  "

lemma may_be_inclusive_commut: "
  path\<^sub>1 \<asymp> path\<^sub>2 \<Longrightarrow> path\<^sub>2 \<asymp> path\<^sub>1
"
 apply (erule may_be_inclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
  apply (simp add: Send2)
  apply (simp add: Send1)
  using Kite apply auto[1]
  using Kite apply auto[1]
  using Kite apply auto[1]
done


lemma may_be_inclusive_preserved_under_unordered_extension: "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> path\<^sub>1 \<asymp> path\<^sub>2 \<Longrightarrow> path\<^sub>1 @ [l] \<asymp> path\<^sub>2
"
 apply (erule may_be_inclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
  apply (simp add: Send1)
  apply (simp add: Send2)
  using Kite apply auto[1]
  using Kite apply auto[1]
  using Kite apply auto
done

lemma may_be_inclusive_preserved_under_unordered_double_extension: "
  path\<^sub>1 \<asymp> path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> path\<^sub>1 @ [l1] \<asymp> path\<^sub>2 @ [l2]
"
by (metis may_be_inclusive_commut may_be_inclusive_preserved_under_unordered_extension prefix_append prefix_def)

*)

inductive singular :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  equal: "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "
(*|
  exclusive: "
    \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "*)

inductive noncompetitive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  ordered: "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  " (*|
  exclusive: "
    \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "*)



inductive static_one_shot :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_fan_in V e xC 
  "


















(*


lemma inclusive_preserved: "
  \<E> \<rightarrow> \<E>' \<Longrightarrow>
  \<forall>\<pi>1. (\<exists>\<sigma>\<^sub>1. \<E> \<pi>1 = Some \<sigma>\<^sub>1) \<longrightarrow> (\<forall>\<pi>2. (\<exists>\<sigma>\<^sub>2. \<E> \<pi>2 = Some \<sigma>\<^sub>2) \<longrightarrow> \<pi>1 \<asymp> \<pi>2) \<Longrightarrow>
  \<E>' \<pi>1 = Some \<sigma>\<^sub>1 \<Longrightarrow> \<E>' \<pi>2 = Some \<sigma>\<^sub>2 \<Longrightarrow> 
  \<pi>1 \<asymp> \<pi>2
"
 apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)

   apply (case_tac "\<pi>1 = \<pi> ;; (LReturn x\<^sub>\<kappa>')"; auto; (case_tac "\<pi>2 = \<pi> ;; (LReturn x\<^sub>\<kappa>')"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)
   
   apply (case_tac "\<pi>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext x)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext x)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LSpawn x)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LSpawn x)"; auto))
   apply (simp add: Ordered)
   apply (case_tac "\<pi>2 = \<pi> ;; (LNext x)"; auto)
  apply (simp add: Spawn_Left)
  apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
  apply (case_tac "\<pi>1 = \<pi> ;; (LNext x)"; auto)
  apply (simp add: Spawn_Right)
  apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict) 
   apply (case_tac "\<pi>1 = \<pi> ;; (LNext x)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext x)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>1 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (simp add: Ordered)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf.simps prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>1 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf.simps prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
 
done


lemma runtime_paths_are_inclusive': "
  \<E>\<^sub>0 \<rightarrow>* \<E> \<Longrightarrow>
  (\<forall> \<pi>1 \<pi>2 \<sigma>\<^sub>1 \<sigma>\<^sub>2.
    \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E> \<pi>1 = Some \<sigma>\<^sub>1 \<longrightarrow>
    \<E> \<pi>2 = Some \<sigma>\<^sub>2 \<longrightarrow>
    \<pi>1 \<asymp> \<pi>2
  )
"
 apply (drule star_implies_star_left)
 apply (erule star_left.induct; auto)
  apply (simp add: Ordered)
 apply (rename_tac \<E> \<E>' \<pi>1 \<sigma>\<^sub>1 \<pi>2 \<sigma>\<^sub>2)
 apply (blast dest: inclusive_preserved)
done



lemma runtime_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>1' = Some \<sigma>\<^sub>1';
    \<E>' \<pi>2' = Some \<sigma>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>1' \<asymp> \<pi>2'
"
by (blast dest: runtime_paths_are_inclusive')




lemma runtime_send_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' c \<pi>1';
    is_send_path \<E>' c \<pi>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>1' \<asymp> \<pi>2'
"
apply (unfold is_send_path.simps; auto)
using runtime_paths_are_inclusive by blast


*)

inductive 
  dynamic_built_on_chan_var :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> var \<Rightarrow> bool" and
  dynamic_built_on_chan_prim :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> prim \<Rightarrow> bool" and
  dynamic_built_on_chan_bindee :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> bind \<Rightarrow> bool" and
  dynamic_built_on_chan_exp :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> exp \<Rightarrow> bool" 
where
  Chan: "
    \<rho> x = Some (VChan c) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |
  Closure: "
    dynamic_built_on_chan_prim \<rho>' c p \<Longrightarrow>
    \<rho> x = Some (VClosure p \<rho>') \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |


  Send_Evt: "
    dynamic_built_on_chan_var \<rho> c xSC \<or> dynamic_built_on_chan_var \<rho> c xM \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Send_Evt xSC xM)
  " |
  Recv_Evt: "
    dynamic_built_on_chan_var \<rho> c xRC \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Recv_Evt xRC)
  " |
  Pair: "
    dynamic_built_on_chan_var \<rho> c x1 \<or> dynamic_built_on_chan \<rho> c x2 \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Pair x1 x2)
  " |
  Left: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Left xSum)
  " |
  Right: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Right xSum)
  " |
  Abs: "
    dynamic_built_on_chan_exp \<rho>' c e \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Abs f x e)
  " |

  Prim: "
    dynamic_built_on_chan_prim \<rho> c p \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (Prim p)
  " |
  Spawn: "
    dynamic_built_on_chan_exp \<rho> c eCh \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (SPAWN eCh)
  " |
  Sync: "
    dynamic_built_on_chan_var \<rho> c xY \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (SYNC xY)
  " |
  Fst: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (FST xP)
  " |
  Snd: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (SND xP)
  " |
  Case: "
    dynamic_built_on_chan_var \<rho> c xS \<or> 
    dynamic_built_on_chan_exp \<rho> c eL \<or> dynamic_built_on_chan_exp \<rho> c eR \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (CASE xS LEFT xL |> eL RIGHT xR |> eR)
  " |
  App: "
    dynamic_built_on_chan_var \<rho> c f \<or>
    dynamic_built_on_chan_var \<rho> c xA \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (APP f xA)
  " |

  Result: "
    dynamic_built_on_chan_var \<rho> c x \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (RESULT x)
  " |
  Let: "
    dynamic_built_on_chan_bindee \<rho> c b \<or> dynamic_built_on_chan_exp \<rho> c e \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (LET x = b in e)
  "

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


inductive paths_congruent_mod_chan :: "trace_pool * com_set \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Unordered: "
    paths_congruent \<pi> pathx \<Longrightarrow>
    \<not> (prefix pathx path) \<Longrightarrow>
    \<not> (prefix path pathx) \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) c \<pi> path
  " |
  Chan: "
    paths_congruent ((LNext xC) # \<pi>Suff) path \<Longrightarrow>
    \<E> (\<pi>C @ (LNext xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) (Ch \<pi>C xC) (\<pi>C @ (LNext xC) # \<pi>Suff) path
  " |
  Sync: "
    paths_congruent \<pi>Suffix pathSuffix \<Longrightarrow>
    \<E> (\<pi>R @ (LNext xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
    dynamic_built_on_chan_var \<rho>RY c xR \<Longrightarrow>
    \<E> \<pi>S = Some (\<langle>LET xS = SYNC xSE in eSY;\<rho>SY;\<kappa>SY\<rangle>) \<Longrightarrow>
    \<E> \<pi>R = Some (\<langle>LET xR = SYNC xRE in eRY;\<rho>RY;\<kappa>RY\<rangle>) \<Longrightarrow>
    {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) c \<pi>S pathPre \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) c (\<pi>R @ (LNext xR) # \<pi>Suffix) (pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # pathSuffix)
  " 

lemma no_empty_paths_congruent_mod_chan: "
  \<not> (paths_congruent_mod_chan EH c [] path)"
  apply (rule notI)
  apply (erule paths_congruent_mod_chan.cases; auto)
  apply (erule paths_congruent.cases; auto)
done

(*
lemma static_paths_of_same_run_inclusive_base: "
  E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow> 
  paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2"
  from H1 H2 H4 show 
    "path1 \<asymp> path2" 
    by (metis fun_upd_apply no_empty_paths_congruent_mod_chan)
qed


lemma paths_equal_implies_paths_inclusive: "
  path1 = path2 \<Longrightarrow> path1 \<asymp> path2 
"
by (simp add: Prefix2)

lemma paths_cong_preserved_under_reduction: "
  paths_congruent (\<pi> ;; l) (path @ [n]) \<Longrightarrow>
  paths_congruent \<pi> path"
using paths_congruent.cases by fastforce


lemma equal_concrete_paths_implies_unordered_or_equal_abstract_paths: "
paths_congruent_mod_chan EH c \<pi> path1 \<Longrightarrow>
paths_congruent_mod_chan EH c \<pi> path2 \<Longrightarrow>
path1 = path2 \<or> (\<not> prefix path1 path2 \<and> \<not> prefix path2 path1)
"
sorry

lemma path_cong_mod_chan_preserved_under_reduction: "
paths_congruent_mod_chan (E', H') (Ch \<pi>C xC) (\<pi> ;; l) (path @ [n]) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path
"
sorry

lemma leaf_prefix_exists: "
  leaf E' (\<pi> ;; l) \<Longrightarrow>
  (E, H) \<rightarrow> (E', H') \<Longrightarrow>
  E \<pi> \<noteq> None
"
sorry


lemma path_state_preserved_for_non_leaf: "
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' (\<pi> ;; l) = Some \<sigma> \<Longrightarrow>
\<not> leaf E \<pi> \<Longrightarrow>
E (\<pi> ;; l) = Some \<sigma>
"
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply presburger+
  apply (metis append1_eq_conv fun_upd_other)
  apply (metis butlast_snoc fun_upd_apply)
done


lemma static_paths_of_same_run_inclusive_step: "
\<forall>\<pi>1 \<pi>2 path1 path2.
  E \<pi>1 \<noteq> None \<longrightarrow>
  E \<pi>2 \<noteq> None \<longrightarrow>
  paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1 \<longrightarrow> 
  paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2 \<longrightarrow> 
  path1 \<asymp> path2 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
paths_congruent_mod_chan (E', H') (Ch \<pi>C xC) \<pi>1 path1 \<Longrightarrow> 
paths_congruent_mod_chan (E', H') (Ch \<pi>C xC) \<pi>2 path2 \<Longrightarrow>
path1 \<asymp> path2 
"
(* TO DO: switch to ISAR style;

   derive equal and unordered paths; 
   derive inclusive paths

*)

proof ((case_tac "path1 = []"; (simp add: Prefix1)), (case_tac "path2 = []", (simp add: Prefix2)))
  assume 
    H1: "
      \<forall>\<pi>1. (\<exists>y. E \<pi>1 = Some y) \<longrightarrow>
      (\<forall>\<pi>2. (\<exists>y. E \<pi>2 = Some y) \<longrightarrow>
      (\<forall>path1. paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1 \<longrightarrow>
      (\<forall>path2. paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2 \<longrightarrow> 
        path1 \<asymp> path2)))" and
    H2: "star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H)" and
    H3: "(E, H) \<rightarrow> (E', H')" and
    H4: "\<exists>y. E' \<pi>1 = Some y" and
    H5: "\<exists>y. E' \<pi>2 = Some y " and
    H6: "paths_congruent_mod_chan (E', H') (Ch \<pi>C xC) \<pi>1 path1" and
    H7: "paths_congruent_mod_chan (E', H') (Ch \<pi>C xC) \<pi>2 path2" and
    H8: "path1 \<noteq> []" and 
    H9: "path2 \<noteq> []"

  obtain \<sigma>1 where 
    H10: "E' \<pi>1 = Some \<sigma>1"
    using H4 by blast

  obtain \<sigma>2 where 
    H11: "E' \<pi>2 = Some \<sigma>2"
    using H5 by blast

  obtain \<pi>1x l1 path1x n1 where
    H12: "\<pi>1x ;; l1 = \<pi>1" and
    H13: "path1x @ [n1] = path1" and
    H14: "paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1x path1x" 
  by (metis H3 H6 H8 append_butlast_last_id path_cong_mod_chan_preserved_under_reduction no_empty_paths_congruent_mod_chan)

  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x ;; l2 = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2x path2x"
  by (metis H3 H7 H9 append_butlast_last_id path_cong_mod_chan_preserved_under_reduction no_empty_paths_congruent_mod_chan)


  have H18: "paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1" sorry

  have H19: "paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2" sorry

  show "path1 \<asymp> path2"
  proof cases
    assume L1H1: "leaf E \<pi>1x"
    obtain \<sigma>1x where
      L1H2: "E \<pi>1x = Some \<sigma>1x" using L1H1 leaf.simps by auto
    show "path1 \<asymp> path2"
    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have "path1x \<asymp> path2x"
        using H1 H14 H17 L1H2 L2H2 by blast
      (* inclusive definition fails in case of non-unique variable bindings *)
      show "path1 \<asymp> path2" sorry
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      have L2H3: "path1x \<asymp> path2"
        using H1 H14 H19 L1H2 L2H2 by auto

      have L2H4: "\<not> strict_prefix \<pi>1x \<pi>2"
        by (metis L1H1 L2H2 leaf.cases option.distinct(1))
      show "path1 \<asymp> path2"
      proof cases
        assume L3H1: "prefix path1x path2"
       (* inclusive definition fails in case of non-unique variable bindings *)
        show "path1 \<asymp> path2" sorry
      next
        assume L3H1: "\<not> prefix path1x path2"
        show "path1 \<asymp> path2"
          by (metis H13 L2H3 L3H1 Prefix2 may_be_inclusive_preserved_under_unordered_extension prefix_prefix)
      qed
    qed

  next
    assume L1H1: "\<not> leaf E \<pi>1x"
      have L1H2: "E \<pi>1 = Some \<sigma>1"
        using H10 H12 H3 L1H1 path_state_preserved_for_non_leaf by blast
    show "path1 \<asymp> path2"

    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have L2H3: "path1 \<asymp> path2x"
        using H1 H17 H18 L1H2 L2H2 by auto
      show "path1 \<asymp> path2"
      proof cases
        assume L3H1: "prefix path2x path1"
        show "path1 \<asymp> path2" sorry
      next
        assume L3H1: "\<not> prefix path2x path1"
        show "path1 \<asymp> path2"
          by (metis H16 L2H3 L3H1 Prefix1 may_be_inclusive_commut may_be_inclusive_preserved_under_unordered_extension prefix_prefix)
      qed
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      show "path1 \<asymp> path2"
        using H1 H18 H19 L1H2 L2H2 by blast
    qed

  qed

qed
(*
apply ((case_tac "path1 = []"; (auto simp: Prefix1)), (case_tac "path2 = []", (auto simp: Prefix2)))
apply (case_tac "path2 = []", (auto simp: Prefix2))
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply (case_tac "\<pi>1 = \<pi> ;; LReturn x\<^sub>\<kappa>"; auto; (case_tac "\<pi>2 = \<pi> ;; LReturn x\<^sub>\<kappa>"; auto)?)
  apply (drule_tac x = \<pi> in spec; auto)
  apply (drule_tac x = \<pi> in spec; auto)
  apply (drule_tac x = "(butlast path1)" in spec; auto)
  apply (metis append_butlast_last_id path_cong_mod_chan_preserved_under_reduction)
  apply (drule_tac x = "(butlast path2)" in spec; auto)
  apply (metis append_butlast_last_id path_cong_mod_chan_preserved_under_reduction)
  apply (erule paths_congruent_mod_chan.cases; auto; (erule paths_congruent_mod_chan.cases; auto))
  apply (erule paths_congruent.cases; auto; (erule paths_congruent.cases; auto); (erule nodes_congruent.cases))
done
*)

lemma static_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
proof -
  assume
    H1: "([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

  from H1 have
    "star_left (op \<rightarrow>) ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')" by (simp add: star_implies_star_left)
  
  then obtain X0 X' where 
    H6: "X0 = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" 
        "X' = (\<E>', H')" and
    H7: "star_left (op \<rightarrow>) X0 X'" by auto

  from H7 have 
    H8: "
      \<forall> \<E>' H' \<pi>1 \<pi>2 path1 path2.
      X0 = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<longrightarrow> X' = (\<E>', H') \<longrightarrow>
      \<E>' \<pi>1 \<noteq> None \<longrightarrow>
      \<E>' \<pi>2 \<noteq> None \<longrightarrow>
      paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow>
      paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow>
      path1 \<asymp> path2
    "
  proof induction
    case (refl z)
    then show ?case
      using static_paths_of_same_run_inclusive_base by blast
  next
    case (step x y z)

    {
      fix \<E>' H' \<pi>1 \<pi>2 path1 path2
      assume 
        L2H1: "x = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" and
        L2H2: "z = (\<E>', H')" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
        L2H6: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8: "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          paths_congruent_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow> 
          paths_congruent_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow> 
          path1 \<asymp> path2 "
        by blast

      have 
        "path1 \<asymp> path2"
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 static_paths_of_same_run_inclusive_step step.hyps(1) step.hyps(2) by blast
    }
    then show ?case by blast
  qed

  from H2 H3 H4 H5 H6(1) H6(2) H8 show 
    "path1 \<asymp> path2" by blast
qed

lemma is_send_path_implies_nonempty_pool: "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2: "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed

lemma send_static_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
using is_send_path_implies_nonempty_pool static_paths_of_same_run_inclusive by fastforce
*)




lemma send_path_equality_sound: "
  path1 = path2 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  \<pi>1 = \<pi>2
"
sorry
(*
lemma send_static_paths_equal_unordered_implies_dynamic_paths_equal: "
pathSync = pathSynca \<or> (\<not> pathSynca \<asymp> pathSync) \<Longrightarrow> 

([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>1 \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>2 \<Longrightarrow>

paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>\<^sub>1 pathSync \<Longrightarrow>
paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>\<^sub>2 pathSynca \<Longrightarrow>

\<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (simp add: send_path_equality_sound send_static_paths_of_same_run_unordered)
*)
(* END *)


(* PATH SOUND *)

lemma isnt_path_sound: "
  \<E>' \<pi> = Some (\<langle>LET x = b in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> z \<noteq> None \<Longrightarrow>
  dynamic_built_on_chan_var \<rho> (Ch \<pi>C xC) z \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_congruent_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi> path \<and>
    may_be_static_live_path V F Ln Lx (NLet xC) isEnd path
"
sorry


lemma isnt_send_evt_sound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> V x\<^sub>e
"
  apply (drule values_not_bound_sound; assumption?; auto)
done

lemma isnt_send_chan_sound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi> xC));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan xC \<in> V x\<^sub>s\<^sub>c
"
 apply (frule may_be_static_eval_to_pool)
 apply (drule may_be_static_eval_preserved_under_concur_step_star[of _ _ _ ]; assumption?)
 apply (erule may_be_static_eval_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule may_be_static_eval_state.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule may_be_static_eval_value.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ "(VChan (Ch \<pi> xC))"]; simp)
done

lemma isnt_send_site_sound: "
  \<E>' \<pi>Sync = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>C xC)) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  may_be_static_send_node_label V e xC (NLet x\<^sub>y)
"
 apply (unfold may_be_static_send_node_label.simps; auto)
 apply (rule exI[of _ x\<^sub>s\<^sub>c]; auto)
 apply (auto simp: isnt_send_chan_sound)
 apply (rule exI[of _ x\<^sub>m]; auto?)
 apply (rule exI[of _ x\<^sub>e]; auto?)
 apply (blast dest: isnt_send_evt_sound)
 apply (rule exI; auto?)
 apply (erule isnt_exp_sound; auto)
done


lemma isnt_send_path_sound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  \<exists> pathSync .
    (paths_congruent_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = x\<^sub>s\<^sub>c and \<pi>C = \<pi>C and \<rho>\<^sub>e = \<rho>\<^sub>e in isnt_send_site_sound; auto?)
 apply (frule isnt_path_sound; auto?)
  apply (auto simp: 
    dynamic_built_on_chan_var.simps 
    dynamic_built_on_chan_var_dynamic_built_on_chan_prim_dynamic_built_on_chan_bindee_dynamic_built_on_chan_exp.Send_Evt 
  )
done

(* END PATH SOUND *)



theorem one_shot_sound': "
  every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) op =
"
apply (simp add: every_two_dynamic_paths.simps every_two_static_paths.simps singular.simps; auto)
apply (metis isnt_send_path_sound send_path_equality_sound)
done
(*
 apply (simp add: every_two_dynamic_paths.simps every_two_static_paths.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>\<^sub>1 in isnt_send_path_sound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>\<^sub>2 in isnt_send_path_sound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (simp add: send_static_paths_equal_unordered_implies_dynamic_paths_equal)
 done
*)



theorem one_shot_sound: "
  \<lbrakk>
    static_one_shot V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_shot.cases; auto)
 apply (unfold one_shot.simps)
 apply (simp add: one_shot_sound')
done

(*
TO DO LATER:
*)

theorem noncompetitive_send_to_ordered_send: "
  every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry
(*
apply (simp add: every_two_dynamic_paths.simps noncompetitive.simps; auto)
using isnt_send_path_sound runtime_send_paths_are_inclusive by blast
*)

theorem fan_out_sound: "
  \<lbrakk>
    static_fan_out V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> xC)
"
 apply (erule static_fan_out.cases; auto)
 apply (unfold fan_out.simps)
 apply (metis noncompetitive_send_to_ordered_send)
done

lemma noncompetitive_recv_to_ordered_recv: "
   every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
   static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
   every_two_dynamic_paths (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem fan_in_sound: "
  \<lbrakk>
    static_fan_in V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> xC)
"
 apply (erule static_fan_in.cases; auto)
 apply (unfold fan_in.simps)
 apply (metis noncompetitive_recv_to_ordered_recv)
done


theorem one_to_one_sound: "
  \<lbrakk>
    static_one_to_one V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_to_one.cases; auto)
 apply (unfold one_to_one.simps)
 apply (simp add: noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send)
done




(*
lemma paths_cong_mod_chan_preserved_under_reduction: "
(suffix \<pi> (\<pi>C ;; (LNext xC)) \<and> suffix path [(NLet xC, ENext)] \<or>
  True) \<Longrightarrow>
paths_congruent_mod_chan EH' (Ch \<pi>C xC) (\<pi> ;; l) (path @ [n]) \<Longrightarrow>
E \<pi> \<noteq> None \<Longrightarrow>
paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"
proof -
  assume
    H1: "E \<pi> \<noteq> None" and
    H2: "\<pi> \<noteq> []" "path \<noteq> []" and
    H3: "paths_congruent_mod_chan EH' c (\<pi> ;; l) (path @ [n])"

  from H3
  show "paths_congruent_mod_chan (E, H) c \<pi> path"
  proof cases

    case (Chan xC \<pi>X E' \<pi>C H')

    have 
      H4: "\<pi> ;; l = \<pi>C @ (butlast (LNext xC # \<pi>X)) ;; l"
      by (metis butlast_append butlast_snoc list.simps(3) local.Chan(3))
    
    have 
      H5: "paths_congruent ((butlast (LNext xC # \<pi>X)) ;; l) (path @ [n])"
      by (metis append_butlast_last_id last_ConsL last_appendR list.simps(3) local.Chan(3) local.Chan(4))

    have 
      H6: "butlast (LNext xC # \<pi>X) \<noteq> []"
      by (metis H2(2) H5 paths_congruent.cases snoc_eq_iff_butlast)

    have 
      H7: "paths_congruent (butlast (LNext xC # \<pi>X)) path"
      using H2(2) H5 H6 paths_cong_preserved_under_reduction by blast

    have 
      H8: "paths_congruent (LNext xC # (butlast \<pi>X)) path"
      by (metis H6 H7 butlast.simps(2))

    have L2H10: "\<pi> = \<pi>C @ butlast (LNext xC # \<pi>X)"
    using H4 by blast

    have "paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"
    using H1 H6 H8 L2H10 paths_congruent_mod_chan.Chan by auto
     
    then show "paths_congruent_mod_chan (E, H) c \<pi> path"
    by (simp add: local.Chan(2))

  next
    case (Sync \<pi>Suffix pathSuffix E' \<pi>R xR \<rho>RY \<pi>S xS xSE eSY \<rho>SY \<kappa>SY xRE eRY \<kappa>RY H' pathPre)

    
    then show "paths_congruent_mod_chan (E, H) c \<pi> path"
    proof cases
      assume L1H1: "pathSuffix = []"

      have L1H2: "path = pathPre @ [(NLet xS, ESend xSE)]"
        using L1H1 local.Sync(3) by auto

      have L1H3: "\<pi>Suffix = []"
        using L1H1 local.Sync(4) paths_congruent.cases by blast

      have L1H3: "\<pi> = \<pi>R"
        using L1H3 local.Sync(2) by blast

      have "paths_congruent_mod_chan (E, H) c \<pi>R (pathPre @ [(NLet xS, ESend xSE)])" sorry

      then show ?thesis sorry
    next
      assume L1H1: "pathSuffix \<noteq> []"

      have 
        L1H2: "path = pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # (butlast pathSuffix)"
        by (metis L1H1 butlast.simps(2) butlast_append butlast_snoc list.simps(3) local.Sync(3))
      
      have L1H3: "\<pi>Suffix \<noteq> []"
        using local.Sync(4) paths_congruent.cases sorry

      have L1H4: "\<pi> = \<pi>R @ LNext xR # (butlast \<pi>Suffix)"
        by (metis L1H3 butlast.simps(2) butlast_append butlast_snoc list.distinct(1) local.Sync(2))

      show ?thesis
      proof cases
        assume 
          L2H1: "(butlast pathSuffix) = []"

        have 
          L2H2: "path = pathPre @ [(NLet xS, ESend xSE), (NLet xR, ENext)]"
          by (simp add: L1H2 L2H1)

        have 
          L2H3: "(butlast \<pi>Suffix) = []" sorry

        have L2H4: "\<pi> = \<pi>R @ [LNext xR]" by (simp add: L1H4 L2H3)

        have 
          "paths_congruent_mod_chan (E, H) c (\<pi>R @ [LNext xR]) (pathPre @ [(NLet xS, ESend xSE), (NLet xR, ENext)])" sorry

        then show ?thesis
          by (simp add: L2H2 L2H4)
      next
        assume "(butlast pathSuffix) \<noteq> []"
        then show ?thesis sorry
      qed
    qed
  (*next
    third case
  *)
  qed
qed
*)


end

*)
