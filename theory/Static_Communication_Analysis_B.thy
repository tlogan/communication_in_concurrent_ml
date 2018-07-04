theory Static_Communication_Analysis_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication_Analysis 
    Static_Communication_Analysis 
begin

datatype edge_label = ENext | ESpawn | ECall | EReturn var

type_synonym flow_label = "(node_label \<times> edge_label \<times> node_label)"

type_synonym flow_set = "flow_label set"

type_synonym step_label = "(node_label \<times> edge_label)"

type_synonym abstract_path = "step_label list"


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
        (NLet x, ECall, nodeLabel e\<^sub>l),
        (NLet x, ECall, nodeLabel e\<^sub>r),
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
          (NLet x, ECall, nodeLabel e\<^sub>b),
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




inductive may_be_abstract_path :: "flow_set \<Rightarrow> node_label \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    may_be_abstract_path F end []
  " |
  Edge: "
    (start, edge, end) \<in> F \<Longrightarrow>
    may_be_abstract_path F end [(start, edge)]
  " |
  Step: "
    may_be_abstract_path F end ((middle, edge') # post) \<Longrightarrow>
    (start, edge, middle) \<in> F \<Longrightarrow>
    path = [(start, edge), (middle, edge')] @ post \<Longrightarrow>
    may_be_abstract_path F end path
  "

inductive abstract_balanced :: "abstract_path \<Rightarrow> bool" where
  Empty: "
    abstract_balanced []
  " |
  Next: "
    abstract_balanced [(NLet x, ENext)]
  " |
  CallReturn: "
    abstract_balanced path \<Longrightarrow>
    abstract_balanced ((NLet x, ECall) # (path @ [(NResult y, EReturn x)]))
  " |
  Append: "
    path \<noteq> [] \<Longrightarrow>
    abstract_balanced path \<Longrightarrow>
    path' \<noteq> [] \<Longrightarrow>
    abstract_balanced path' \<Longrightarrow>
    abstract_balanced (path @ path')
  "

inductive static_unbalanced :: "abstract_path \<Rightarrow> bool" where
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
    (l, ECall, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, ECall, l')
  " |
  Call_Live_Inner: "
    (l, ECall, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    may_be_static_live_flow F Ln Lx (l, ECall, l')
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

inductive may_be_static_live_path :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> node_label \<Rightarrow> (node_label \<Rightarrow> bool) \<Rightarrow> abstract_path \<Rightarrow> bool" where
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
    may_be_abstract_path  F (NResult y) pre \<Longrightarrow>
    \<not> abstract_balanced (pre @ [(NResult y, EReturn x)]) \<Longrightarrow>
    \<not> Set.is_empty (Lx (NLet x)) \<Longrightarrow>
    path = pre @ (NResult y, EReturn x) # post \<Longrightarrow>
    may_be_static_live_path V F Ln Lx start isEnd path
  "

inductive singular :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  equal: "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive noncompetitive :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  ordered: "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "



inductive static_one_shot :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
    static_fan_in V e xC 
  "

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

inductive paths_congruent :: "control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    paths_congruent [] []
  " |
  Next: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> ;; (LNext x)) (path @ [(NLet x, ENext)])
  " |
  Spawn: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> ;; (LSpawn x)) (path @ [(NLet x, ESpawn)])
  " |
  Call: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> ;; (LCall x)) (path @ [(NLet x, ECall)])
  "  |
  Return: "
    paths_congruent \<pi> (path @ (NLet x, ECall) # path') \<Longrightarrow>
    abstract_balanced path' \<Longrightarrow>
    paths_congruent (\<pi> ;; (LReturn y)) (path @ (NLet x, ECall) # path' @ [(NResult y, EReturn x)])
  " 

inductive paths_congruent_mod_chan :: "trace_pool * com_set \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
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
lemma send_abstract_paths_equal_unordered_implies_dynamic_paths_equal: "
pathSync = pathSynca \<or> (\<not> pathSynca \<asymp> pathSync) \<Longrightarrow> 

([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>1 \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>2 \<Longrightarrow>

paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>\<^sub>1 pathSync \<Longrightarrow>
paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>\<^sub>2 pathSynca \<Longrightarrow>

\<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (simp add: send_path_equality_sound send_abstract_paths_of_same_run_unordered)
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


theorem one_shot_sound': "
  every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) op =
"
apply (simp add: every_two_dynamic_paths.simps every_two.simps singular.simps; auto)
apply (metis isnt_send_path_sound send_path_equality_sound)
done



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

theorem noncompetitive_send_to_ordered_send: "
  every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) ordered
"

apply (simp add: every_two_dynamic_paths.simps noncompetitive.simps; auto)
sorry

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
   every_two (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
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


end
