theory Static_Communication_Analysis
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication_Analysis
    Static_Traceability
    Static_Framework
begin

inductive may_be_static_send_node_label :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  Sync: "
    {^Chan xC} \<subseteq> V xSC \<Longrightarrow>
    {^Send_Evt xSC xM} \<subseteq> V xE \<Longrightarrow>
    is_super_exp e (LET x = SYNC xE in e') \<Longrightarrow>
    may_be_static_send_node_label V e xC (NLet x)
  "

inductive may_be_static_recv_node_label :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  Sync: "
    {^Chan xC} \<subseteq> V xRC \<Longrightarrow>
    {^Recv_Evt xRC} \<subseteq> V xE \<Longrightarrow>
    is_super_exp e (LET x = SYNC xE in e') \<Longrightarrow>
    may_be_static_recv_node_label V e xC (NLet x)
  "


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
      {^Pair x1 x2} \<subseteq> V x\<^sub>a;
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x1 = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FST x\<^sub>a in e)
  " |
  Let_Snd: "
    \<lbrakk>
      static_chan_liveness V Ln Lx x\<^sub>c e;
      Ln (nodeLabel e) = Lx (NLet x);
      {^Pair x1 x2} \<subseteq> V x\<^sub>a;
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x2 = Ln (NLet x)
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
  " |

  Post_Call: "
    may_be_static_path F end ((NLet x, ECall x) # post) \<Longrightarrow>
    isEnd end \<Longrightarrow>
    \<not> static_balanced ((NLet x, ECall x) # post) \<Longrightarrow>
    \<not> Set.is_empty (Lx (NLet x)) \<Longrightarrow>
    may_be_static_live_path V F Ln Lx (NLet x) isEnd ((NLet x, ECall x) # post)
  " 




inductive may_be_inclusive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Ordered: "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
  Spawn_Left: "
    \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Spawn_Right: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>2
  " |
  Send_Left: "
    \<pi> @ (NLet x, ESend xE) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Send_Right: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESend xE) # \<pi>\<^sub>2
  "

lemma may_be_inclusive_commut: "
  \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>2 \<asymp> \<pi>\<^sub>1
"
 apply (erule may_be_inclusive.cases; auto)
  apply (simp add: Ordered)
  apply (simp add: Ordered)
  apply (simp add: Spawn_Right)
  apply (simp add: Spawn_Left)
  apply (simp add: Send_Right)
  apply (simp add: Send_Left)
done


lemma may_be_inclusive_preserved_under_unordered_extension: "
  \<not> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> \<not> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow> \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 @ [l] \<asymp> \<pi>\<^sub>2
"
 apply (erule may_be_inclusive.cases; auto)
  apply (simp add: Spawn_Left)
  apply (simp add: Spawn_Right)
  apply (simp add: Send_Left)
  apply (simp add: Send_Right)
done


inductive singular :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  equal: "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive noncompetitive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  ordered: "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


inductive every_two_static_paths  :: "(static_path \<Rightarrow> bool) \<Rightarrow> (static_path \<Rightarrow> static_path \<Rightarrow> bool) \<Rightarrow> bool" where
  pred: "
    (\<forall> path1 path2 .
      P path1 \<longrightarrow>
      P path2 \<longrightarrow>
      R path1 path2
    ) \<Longrightarrow>
    every_two_static_paths P R
  "


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

end
