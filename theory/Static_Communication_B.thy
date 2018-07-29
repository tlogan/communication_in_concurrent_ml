theory Static_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
    Static_Communication
begin

datatype edge_label = ENext | ESpawn | ESend var | ECall | EReturn var

type_synonym flow_label = "(node_label \<times> edge_label \<times> node_label)"

type_synonym flow_set = "flow_label set"

type_synonym step_label = "(node_label \<times> edge_label)"

type_synonym abstract_path = "step_label list"


inductive static_traversable :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> (var \<Rightarrow> node_label \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_traversable V F static_recv_site (Rslt x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(NLet x , ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x Unt e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x MkChn e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (SendEvt x\<^sub>c x\<^sub>m)) e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (RecvEvt x\<^sub>c)) e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  Let_Left: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Lft x\<^sub>p)) e)
  " |
  Let_Right: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Rght x\<^sub>p)) e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e\<^sub>b;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (NLet x, ENext, top_node_label e),
        (NLet x, ESpawn, top_node_label e\<^sub>c)
      } \<subseteq> F;
      static_traversable V F static_recv_site e\<^sub>c;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Spwn e\<^sub>c) e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      (\<forall> xSC xM xC y.
        {^SendEvt xSC xM} \<subseteq> V xSE \<longrightarrow>
        {^Chan xC} \<subseteq> V xSC \<longrightarrow>
        static_recv_site xC (NLet y) \<longrightarrow>
        {(NLet x, ESend xSE, NLet y)} \<subseteq> F
      );
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Sync xSE) e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Fst x\<^sub>p) e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Snd x\<^sub>p) e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (NLet x, ECall, top_node_label e\<^sub>l),
        (NLet x, ECall, top_node_label e\<^sub>r),
        (NResult (\<lfloor>e\<^sub>l\<rfloor>), EReturn x, top_node_label e),
        (NResult (\<lfloor>e\<^sub>r\<rfloor>), EReturn x, top_node_label e)
      } \<subseteq> F;
      static_traversable V F static_recv_site e\<^sub>l;
      static_traversable V F static_recv_site e\<^sub>r;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow>
        {
          (NLet x, ECall, top_node_label e\<^sub>b),
          (NResult (\<lfloor>e\<^sub>b\<rfloor>), EReturn x, top_node_label e)
        } \<subseteq> F);
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (App f x\<^sub>a) e)
  "

inductive 
  static_built_on_chan :: "abstract_env \<Rightarrow> node_map \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
where
  Chan: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> V x 
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V Ln x\<^sub>c x
  " |
  Send_Evt: "
    \<lbrakk>
      ^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> V x;
      static_built_on_chan V Ln x\<^sub>c x\<^sub>s\<^sub>c \<or> static_built_on_chan V Ln x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V Ln x\<^sub>c x
  " |
  Recv_Evt: "
    \<lbrakk>
      ^RecvEvt x\<^sub>r\<^sub>c \<in> V x;
      static_built_on_chan V Ln x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V Ln x\<^sub>c x
  " |
  Pair: "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> V x;
      static_built_on_chan V Ln x\<^sub>c x\<^sub>1 \<or> static_built_on_chan V Ln x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V Ln x\<^sub>c x
  " |
  Left: "
    \<lbrakk>
      ^(Lft x\<^sub>a) \<in> V x;
      static_built_on_chan V Ln x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V Ln x\<^sub>c x
  " |
  Right: "
    \<lbrakk>
      ^(Rght x\<^sub>a) \<in> V x;
      static_built_on_chan V Ln x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V Ln x\<^sub>c x
  " |
  Abs: "
    ^Abs f x\<^sub>p e\<^sub>b \<in> V x \<Longrightarrow> 
    \<not> Set.is_empty (Ln (top_node_label e\<^sub>b) - {x\<^sub>p}) \<Longrightarrow>
    static_built_on_chan V Ln x\<^sub>c x
  " 
(*
  |

  Result: "
    static_built_on_chan V Ln x\<^sub>c x \<Longrightarrow>
    static_built_on_chan_exp V x\<^sub>c (Rslt x)
  " |
  Let: "
    static_built_on_chan V Ln x\<^sub>c x \<or> 
    static_built_on_chan_exp V x\<^sub>c e \<Longrightarrow>
    static_built_on_chan_exp V x\<^sub>c (Let x b e)
  "
*)

fun chan_set :: "abstract_env \<Rightarrow> node_map \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var set" where
  "chan_set V Ln x\<^sub>c x = (if (static_built_on_chan V Ln x\<^sub>c x) then {x} else {})"


inductive static_live_chan :: "abstract_env \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "
    \<lbrakk>
      chan_set V Ln x\<^sub>c y = Ln (NResult y)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Rslt y)
  " |
  Let_Unit: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      Lx (NLet x) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x Unt e)
  " |
  Let_Chan: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x MkChn e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>s\<^sub>c \<union> chan_set V Ln x\<^sub>c x\<^sub>m = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (SendEvt x\<^sub>s\<^sub>c x\<^sub>m)) e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>r\<^sub>c = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (RecvEvt x\<^sub>r\<^sub>c)) e)
  " |
  Let_Pair: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union>  chan_set V Ln x\<^sub>c x\<^sub>1 \<union> chan_set V Ln x\<^sub>c x\<^sub>2 = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  Let_Left: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Lft x\<^sub>a)) e)
  " |
  Let_Right: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Rght x\<^sub>a)) e)
  " |
  Let_Abs: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>b;
      (Lx (NLet x) - {x}) \<union> (Ln (top_node_label e\<^sub>b) - {x\<^sub>p}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e)
  " |
  Let_Spawn: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>c;
      Ln (top_node_label e) \<union> Ln (top_node_label e\<^sub>c) = Lx (NLet x);
      (Lx (NLet x) - {x}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Spwn e\<^sub>c) e)
  " |
  Let_Sync: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>e = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Sync x\<^sub>e) e)
  " |
  Let_Fst: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Fst x\<^sub>a) e)
  " |
  Let_Snd: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Snd x\<^sub>a) e)
  " |
  Let_Case: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>l;
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>r;
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>s \<union> 
         (Ln (top_node_label e\<^sub>l) - {x\<^sub>l}) \<union> (Ln (top_node_label e\<^sub>r) - {x\<^sub>r}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  " |
  Let_App: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_node_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c f \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (App f x\<^sub>a) e)
  "




inductive static_traceable :: "flow_set \<Rightarrow> node_label \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    static_traceable F end []
  " |
  Edge: "
    (start, edge, end) \<in> F \<Longrightarrow>
    static_traceable F end [(start, edge)]
  " |
  Step: "
    static_traceable F end ((middle, edge') # post) \<Longrightarrow>
    (start, edge, middle) \<in> F \<Longrightarrow>
    path = [(start, edge), (middle, edge')] @ post \<Longrightarrow>
    static_traceable F end path
  "

inductive static_balanced :: "abstract_path \<Rightarrow> bool" where
  Empty: "
    static_balanced []
  " |
  Next: "
    static_balanced [(NLet x, ENext)]
  " |
  CallReturn: "
    static_balanced path \<Longrightarrow>
    static_balanced ((NLet x, ECall) # (path @ [(NResult y, EReturn x)]))
  " |
  Append: "
    path \<noteq> [] \<Longrightarrow>
    static_balanced path \<Longrightarrow>
    path' \<noteq> [] \<Longrightarrow>
    static_balanced path' \<Longrightarrow>
    static_balanced (path @ path')
  "

(*
inductive static_unbalanced :: "abstract_path \<Rightarrow> bool" where
  Result: "
    static_unbalanced ((NResult y, EReturn x) # post)
  " |
  Next: "
    static_unbalanced post \<Longrightarrow>
    static_unbalanced ((NLet x, ENext) # post)
  "
*)

inductive static_live_traversable :: "flow_set \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> flow_label \<Rightarrow> bool"  where
  Next: "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_traversable F Ln Lx (l, ENext, l')
  " |
  Spawn: "
    (l, ESpawn, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_traversable F Ln Lx (l, ESpawn, l')
  " |
  Call_Live_Outer: "
    (l, ECall, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    static_live_traversable F Ln Lx (l, ECall, l')
  " |
  Call_Live_Inner: "
    (l, ECall, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_traversable F Ln Lx (l, ECall, l')
  " |
  Return: "
    (l, EReturn x, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_traversable F Ln Lx (l, EReturn x, l')
  " |
  Send: "
    ((NLet xSend), ESend xE, (NLet xRecv)) \<in> F \<Longrightarrow>
    {xE} \<subseteq> (Ln (NLet xSend)) \<Longrightarrow>
    static_live_traversable F Ln Lx ((NLet xSend), ESend xE, (NLet xRecv))
  "

inductive static_live_traceable :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> node_map \<Rightarrow> node_map \<Rightarrow> node_label \<Rightarrow> (node_label \<Rightarrow> bool) \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    static_live_traceable V F Ln Lx start isEnd []
  " |
  Edge: "
    isEnd end \<Longrightarrow>
    static_live_traversable F Ln Lx (start, edge, end) \<Longrightarrow>
    static_live_traceable V F Ln Lx start isEnd [(start, edge)]
  " |
  Step: "
    static_live_traceable V F Ln Lx middle isEnd ((middle, edge') # path) \<Longrightarrow>
    static_live_traversable F Ln Lx (start, edge, middle) \<Longrightarrow>
    static_live_traceable V F Ln Lx start isEnd ((start, edge) # (middle, edge') # path)
  " |

  Pre_Return: "
    static_live_traceable V F Ln Lx (NResult y) isEnd ((NResult y, EReturn x) # post) \<Longrightarrow>
    static_traceable  F (NResult y) pre \<Longrightarrow>
    \<not> static_balanced (pre @ [(NResult y, EReturn x)]) \<Longrightarrow>
    \<not> Set.is_empty (Lx (NLet x)) \<Longrightarrow>
    path = pre @ (NResult y, EReturn x) # post \<Longrightarrow>
    static_live_traceable V F Ln Lx start isEnd path
  "



inductive static_inclusive :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Prefix1: "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>
    static_inclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Prefix2: "
    prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    static_inclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Spawn1: "
    static_inclusive (\<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>1) (\<pi> @ (NLet x, ENext) # \<pi>\<^sub>2)
  " |
  Spawn2: "
    static_inclusive (\<pi> @ (NLet x, ENext) # \<pi>\<^sub>1) (\<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>2)
  " |
  Send1: "
    static_inclusive (\<pi> @ (NLet x, ESend xE) # \<pi>\<^sub>1) (\<pi> @ (NLet x, ENext) # \<pi>\<^sub>2)
  " |
  Send2: "
    static_inclusive (\<pi> @ (NLet x, ENext) # \<pi>\<^sub>1) (\<pi> @ (NLet x, ESend xE) # \<pi>\<^sub>2)
  "

inductive singular :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  equal: "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (static_inclusive \<pi>\<^sub>1 \<pi>\<^sub>2) \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive noncompetitive :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  ordered: "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (static_inclusive \<pi>\<^sub>1 \<pi>\<^sub>2) \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


inductive static_one_shot :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) singular \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
    static_fan_in V e xC 
  "
locale communication_sound_B = 
  Static_Communication.communication_sound static_one_shot static_fan_out static_fan_in static_one_to_one
begin 
end


lemma static_inclusive_commut: "
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> static_inclusive path\<^sub>2 path\<^sub>1
"
 apply (erule static_inclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
  apply (simp add: Send2)
  apply (simp add: Send1)
done


lemma static_inclusive_preserved_under_unordered_extension: "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> 
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> static_inclusive (path\<^sub>1 @ [l]) path\<^sub>2
"
 apply (erule static_inclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
  apply (simp add: Send1)
  apply (simp add: Send2)
done

lemma static_inclusive_preserved_under_unordered_double_extension: "
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> static_inclusive (path\<^sub>1 @ [l1]) (path\<^sub>2 @ [l2])
"
by (metis static_inclusive_commut static_inclusive_preserved_under_unordered_extension prefix_append prefix_def)


inductive paths_correspond :: "control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    paths_correspond [] []
  " |
  Next: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LNxt x]) (path @ [(NLet x, ENext)])
  " |
  Spawn: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LSpwn x]) (path @ [(NLet x, ESpawn)])
  " |
  Call: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LCall x]) (path @ [(NLet x, ECall)])
  "  |
  Return: "
    paths_correspond \<pi> (path @ (NLet x, ECall) # path') \<Longrightarrow>
    static_balanced path' \<Longrightarrow>
    paths_correspond (\<pi> @ [LRtn y]) (path @ (NLet x, ECall) # path' @ [(NResult y, EReturn x)])
  " 

inductive paths_correspond_mod_chan :: 
  "trace_pool * cmmn_set \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Unordered: "
    paths_correspond \<pi> pathx \<Longrightarrow>
    \<not> (prefix pathx path) \<Longrightarrow>
    \<not> (prefix path pathx) \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c \<pi> path
  " |
  Chan: "
    paths_correspond ((LNxt xC) # \<pi>Suff) path \<Longrightarrow>
    \<E> (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path
  " |
  Sync: "
    paths_correspond \<pi>Suffix pathSuffix \<Longrightarrow>
    \<E> (\<pi>R @ (LNxt xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
    dynamic_built_on_chan_var \<rho>RY c xR \<Longrightarrow>
    \<E> \<pi>S = Some (\<langle>(Let xS (Sync xSE) eSY);\<rho>SY;\<kappa>SY\<rangle>) \<Longrightarrow>
    \<E> \<pi>R = Some (\<langle>(Let xR (Sync xRE) eRY);\<rho>RY;\<kappa>RY\<rangle>) \<Longrightarrow>
    {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c \<pi>S pathPre \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c (\<pi>R @ (LNxt xR) # \<pi>Suffix) (pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # pathSuffix)
  " 

lemma no_empty_paths_correspond_mod_chan: "
  \<not> (paths_correspond_mod_chan EH c [] path)"
  apply (rule notI)
  apply (erule paths_correspond_mod_chan.cases; auto)
  apply (erule paths_correspond.cases; auto)
done


lemma not_static_inclusive_sound_base: "
  E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow> 
  paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_inclusive path1 path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2"
  from H1 H2 H4 show 
    "static_inclusive path1 path2" 
    by (metis fun_upd_apply no_empty_paths_correspond_mod_chan)
qed

lemma paths_equal_implies_paths_inclusive: "
  path1 = path2 \<Longrightarrow> static_inclusive path1 path2 
"
by (simp add: Prefix2)


(*
lemma equal_concrete_paths_implies_unordered_or_equal_abstract_paths: "
paths_correspond_mod_chan EH c \<pi> path1 \<Longrightarrow>
paths_correspond_mod_chan EH c \<pi> path2 \<Longrightarrow>
path1 = path2 \<or> (\<not> prefix path1 path2 \<and> \<not> prefix path2 path1)
"
sorry
*)

lemma paths_cong_mod_chan_preserved_under_reduction: "
paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) (\<pi> @ [l]) (path @ [n]) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path
"
sorry



lemma leaf_prefix_exists: "
  leaf E' (\<pi> @ [l]) \<Longrightarrow>
  (E, H) \<rightarrow> (E', H') \<Longrightarrow>
  E \<pi> \<noteq> None
"
sorry


lemma path_state_preserved_for_non_leaf: "
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' (\<pi> @ [l]) = Some \<sigma> \<Longrightarrow>
\<not> leaf E \<pi> \<Longrightarrow>
E (\<pi> @ [l]) = Some \<sigma>
"
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply presburger+
  apply (metis append1_eq_conv fun_upd_other)
  apply (metis butlast_snoc fun_upd_apply)
done


lemma not_static_inclusive_sound_step: "
\<forall>\<pi>1 \<pi>2 path1 path2.
  E \<pi>1 \<noteq> None \<longrightarrow>
  E \<pi>2 \<noteq> None \<longrightarrow>
  paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1 \<longrightarrow> 
  paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2 \<longrightarrow> 
  static_inclusive path1 path2 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>1 path1 \<Longrightarrow> 
paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>2 path2 \<Longrightarrow>
static_inclusive path1 path2 
"
proof ((case_tac "path1 = []"; (simp add: Prefix1)), (case_tac "path2 = []", (simp add: Prefix2)))
  assume 
    H1: "
      \<forall>\<pi>1. (\<exists>y. E \<pi>1 = Some y) \<longrightarrow>
      (\<forall>\<pi>2. (\<exists>y. E \<pi>2 = Some y) \<longrightarrow>
      (\<forall>path1. paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1 \<longrightarrow>
      (\<forall>path2. paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2 \<longrightarrow> 
        static_inclusive path1 path2)))" and
    H2: "star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H)" and
    H3: "(E, H) \<rightarrow> (E', H')" and
    H4: "\<exists>y. E' \<pi>1 = Some y" and
    H5: "\<exists>y. E' \<pi>2 = Some y " and
    H6: "paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>1 path1" and
    H7: "paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>2 path2" and
    H8: "path1 \<noteq> []" and 
    H9: "path2 \<noteq> []"

  obtain \<sigma>1 where 
    H10: "E' \<pi>1 = Some \<sigma>1"
    using H4 by blast

  obtain \<sigma>2 where 
    H11: "E' \<pi>2 = Some \<sigma>2"
    using H5 by blast

  obtain \<pi>1x l1 path1x n1 where
    H12: "\<pi>1x @ [l1] = \<pi>1" and
    H13: "path1x @ [n1] = path1" and
    H14: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1x path1x" 
  by (metis H3 H6 H8 append_butlast_last_id paths_cong_mod_chan_preserved_under_reduction no_empty_paths_correspond_mod_chan)

  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x @ [l2] = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2x path2x"
  by (metis H3 H7 H9 append_butlast_last_id paths_cong_mod_chan_preserved_under_reduction no_empty_paths_correspond_mod_chan)


  have H18: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1" sorry

  have H19: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2" sorry

  show "static_inclusive path1 path2"
  proof cases
    assume L1H1: "leaf E \<pi>1x"
    obtain \<sigma>1x where
      L1H2: "E \<pi>1x = Some \<sigma>1x" using L1H1 leaf.simps by auto
    show "static_inclusive path1 path2"
    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have "static_inclusive path1x path2x"
        using H1 H14 H17 L1H2 L2H2 by blast
      show "static_inclusive path1 path2" sorry
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      have L2H3: "static_inclusive path1x path2"
        using H1 H14 H19 L1H2 L2H2 by auto

      have L2H4: "\<not> strict_prefix \<pi>1x \<pi>2"
        by (metis L1H1 L2H2 leaf.cases option.distinct(1))
      show "static_inclusive path1 path2"
      proof cases
        assume L3H1: "prefix path1x path2"
       (* inclusive definition fails in case of non-unique variable bindings *)
        show "static_inclusive path1 path2" sorry
      next
        assume L3H1: "\<not> prefix path1x path2"
        show "static_inclusive path1 path2"
          by (metis H13 L2H3 L3H1 Prefix2 static_inclusive_preserved_under_unordered_extension prefix_prefix)
      qed
    qed

  next
    assume L1H1: "\<not> leaf E \<pi>1x"
      have L1H2: "E \<pi>1 = Some \<sigma>1"
        using H10 H12 H3 L1H1 path_state_preserved_for_non_leaf by blast
    show "static_inclusive path1 path2"

    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have L2H3: "static_inclusive path1 path2x"
        using H1 H17 H18 L1H2 L2H2 by auto
      show "static_inclusive path1 path2"
      proof cases
        assume L3H1: "prefix path2x path1"
        show "static_inclusive path1 path2" sorry
      next
        assume L3H1: "\<not> prefix path2x path1"
        show "static_inclusive path1 path2"
          by (metis H16 L2H3 L3H1 Prefix1 static_inclusive_commut static_inclusive_preserved_under_unordered_extension prefix_prefix)
      qed
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      show "static_inclusive path1 path2"
        using H1 H18 H19 L1H2 L2H2 by blast
    qed

  qed

qed


lemma not_static_inclusive_sound: "
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_inclusive path1 path2
"
proof -
  assume
    H1: "star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

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
      paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow>
      paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow>
      static_inclusive path1 path2
    "
  proof induction
    case (refl z)
    then show ?case
      using not_static_inclusive_sound_base by blast
  next
    case (step x y z)

    {
      fix \<E>' H' \<pi>1 \<pi>2 path1 path2
      assume 
        L2H1: "x = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" and
        L2H2: "z = (\<E>', H')" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
        L2H6: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8: "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          paths_correspond_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow> 
          paths_correspond_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow> 
          static_inclusive path1 path2 "
        by blast

      have 
        "static_inclusive path1 path2"
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 not_static_inclusive_sound_step step.hyps(1) step.hyps(2) by blast
    }
    then show ?case by blast
  qed

  from H2 H3 H4 H5 H6(1) H6(2) H8 show 
    "static_inclusive path1 path2" by blast
qed

lemma is_send_path_implies_nonempty_pool: "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2: "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>(Let x\<^sub>y (Sync x\<^sub>e) e\<^sub>n);\<rho>;\<kappa>\<rangle>) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed


lemma static_equality_sound: "
  path1 = path2 \<Longrightarrow>
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None   \<Longrightarrow> 
  \<pi>1 = \<pi>2
"
sorry


(* PATH SOUND *)

lemma not_static_traceable_sound: "
  \<E>' \<pi> = Some (\<langle>(Let x b e\<^sub>n);\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> z \<noteq> None \<Longrightarrow>
  dynamic_built_on_chan_var \<rho> (Ch \<pi>C xC) z \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_correspond_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi> path \<and>
    static_live_traceable V F Ln Lx (NLet xC) isEnd path
"
sorry


lemma send_not_static_traceable_sound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  \<exists> pathSync .
    (paths_correspond_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in node_not_send_site_sound; auto?)
 apply (frule not_static_traceable_sound; auto?)
  apply (auto simp: 
    dynamic_built_on_chan_var.simps 
    dynamic_built_on_chan_var_dynamic_built_on_chan_prim_dynamic_built_on_chan_bound_exp_dynamic_built_on_chan_exp.Send_Evt 
  )
done

(* END PATH SOUND *)


theorem one_shot_sound': "
  every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) singular \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  every_two (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: every_two.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>1 in send_not_static_traceable_sound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>2 in send_not_static_traceable_sound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (metis is_send_path_implies_nonempty_pool not_static_inclusive_sound static_equality_sound)
done

theorem one_shot_sound: "
  \<lbrakk>
    static_one_shot V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
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
  every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry
(*
apply (simp add: every_two.simps noncompetitive.simps; auto)
using send_not_static_traceable_sound runtime_send_paths_are_inclusive by blast
*)

theorem fan_out_sound: "
  \<lbrakk>
    static_fan_out V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> xC)
"
 apply (erule static_fan_out.cases; auto)
 apply (unfold fan_out.simps)
 apply (metis noncompetitive_send_to_ordered_send)
done

lemma noncompetitive_recv_to_ordered_recv: "
   every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
   static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
   every_two (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem fan_in_sound: "
  \<lbrakk>
    static_fan_in V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
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
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_to_one.cases; auto)
 apply (unfold one_to_one.simps)
 apply (metis fan_in_sound fan_out.intros noncompetitive_send_to_ordered_send static_fan_in.intros)
done

interpretation communication_sound_B
proof -
 show "communication_sound_B" sorry
qed

(*



lemma paths_cong_preserved_under_reduction: "
  paths_correspond (\<pi> @ [l) (path @ [n]) \<Longrightarrow>
  paths_correspond \<pi> path"
using paths_correspond.cases by fastforce


lemma paths_cong_mod_chan_preserved_under_reduction: "
(suffix \<pi> (\<pi>C @ [LNxt xC)) \<and> suffix path [(NLet xC, ENext)] \<or>
  True) \<Longrightarrow>
paths_correspond_mod_chan EH' (Ch \<pi>C xC) (\<pi> @ [l) (path @ [n]) \<Longrightarrow>
E \<pi> \<noteq> None \<Longrightarrow>
paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"
proof -
  assume
    H1: "E \<pi> \<noteq> None" and
    H2: "\<pi> \<noteq> []" "path \<noteq> []" and
    H3: "paths_correspond_mod_chan EH' c (\<pi> @ [l) (path @ [n])"

  from H3
  show "paths_correspond_mod_chan (E, H) c \<pi> path"
  proof cases

    case (Chan xC \<pi>X E' \<pi>C H')

    have 
      H4: "\<pi> @ [l = \<pi>C @ (butlast (LNxt xC # \<pi>X)) @ [l"
      by (metis butlast_append butlast_snoc list.simps(3) local.Chan(3))
    
    have 
      H5: "paths_correspond ((butlast (LNxt xC # \<pi>X)) @ [l) (path @ [n])"
      by (metis append_butlast_last_id last_ConsL last_appendR list.simps(3) local.Chan(3) local.Chan(4))

    have 
      H6: "butlast (LNxt xC # \<pi>X) \<noteq> []"
      by (metis H2(2) H5 paths_correspond.cases snoc_eq_iff_butlast)

    have 
      H7: "paths_correspond (butlast (LNxt xC # \<pi>X)) path"
      using H2(2) H5 H6 paths_cong_preserved_under_reduction by blast

    have 
      H8: "paths_correspond (LNxt xC # (butlast \<pi>X)) path"
      by (metis H6 H7 butlast.simps(2))

    have L2H10: "\<pi> = \<pi>C @ butlast (LNxt xC # \<pi>X)"
    using H4 by blast

    have "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"
    using H1 H6 H8 L2H10 paths_correspond_mod_chan.Chan by auto
     
    then show "paths_correspond_mod_chan (E, H) c \<pi> path"
    by (simp add: local.Chan(2))

  next
    case (Sync \<pi>Suffix pathSuffix E' \<pi>R xR \<rho>RY \<pi>S xS xSE eSY \<rho>SY \<kappa>SY xRE eRY \<kappa>RY H' pathPre)

    
    then show "paths_correspond_mod_chan (E, H) c \<pi> path"
    proof cases
      assume L1H1: "pathSuffix = []"

      have L1H2: "path = pathPre @ [(NLet xS, ESend xSE)]"
        using L1H1 local.Sync(3) by auto

      have L1H3: "\<pi>Suffix = []"
        using L1H1 local.Sync(4) paths_correspond.cases by blast

      have L1H3: "\<pi> = \<pi>R"
        using L1H3 local.Sync(2) by blast

      have "paths_correspond_mod_chan (E, H) c \<pi>R (pathPre @ [(NLet xS, ESend xSE)])" sorry

      then show ?thesis sorry
    next
      assume L1H1: "pathSuffix \<noteq> []"

      have 
        L1H2: "path = pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # (butlast pathSuffix)"
        by (metis L1H1 butlast.simps(2) butlast_append butlast_snoc list.simps(3) local.Sync(3))
      
      have L1H3: "\<pi>Suffix \<noteq> []"
        using local.Sync(4) paths_correspond.cases sorry

      have L1H4: "\<pi> = \<pi>R @ LNxt xR # (butlast \<pi>Suffix)"
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

        have L2H4: "\<pi> = \<pi>R @ [LNxt xR]" by (simp add: L1H4 L2H3)

        have 
          "paths_correspond_mod_chan (E, H) c (\<pi>R @ [LNxt xR]) (pathPre @ [(NLet xS, ESend xSE), (NLet xR, ENext)])" sorry

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


(*
lemma paths_cong_mod_chan_preserved_under_reduction_chan: "
  paths_correspond ((LNxt xC) # \<pi>Suff @ [l) (path @ [n]) \<Longrightarrow>
  E (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
  paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path"
using paths_cong_preserved_under_reduction paths_correspond_mod_chan.Chan by blast

lemma  paths_cong_mod_chan_preserved_under_reduction_sync: "
  paths_correspond (\<pi>Suffix @ [l) (pathSuffix @ [n]) \<Longrightarrow>
  \<E> (\<pi>R @ (LNxt xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
  dynamic_built_on_chan_var \<rho>RY c xR \<Longrightarrow>
  \<E> \<pi>S = Some (\<langle>(Let xS (Sync xSE) eSY);\<rho>SY;\<kappa>SY\<rangle>) \<Longrightarrow>
  \<E> \<pi>R = Some (\<langle>(Let xR (Sync xRE) eRY);\<rho>RY;\<kappa>RY\<rangle>) \<Longrightarrow>
  {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
  paths_correspond_mod_chan (\<E>, H) c \<pi>Severy_two pathPre \<Longrightarrow>
  paths_correspond_mod_chan (\<E>, H) c (\<pi>R @ (LNxt xR) # \<pi>Suffix) (pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # pathSuffix)"
by (meson paths_cong_preserved_under_reduction paths_correspond_mod_chan.Sync)
*)





end
