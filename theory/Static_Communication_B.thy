theory Static_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
    Static_Communication
begin

datatype mode = ENext | ESpawn | ESend var | ECall | EReturn var

type_synonym transition = "(label \<times> mode \<times> label)"

type_synonym transition_set = "transition set"

type_synonym step_label = "(label \<times> mode)"

type_synonym abstract_path = "step_label list"


inductive static_traversable :: "abstract_env \<Rightarrow> transition_set \<Rightarrow> (var \<Rightarrow> label \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_traversable V F static_recv_site (Rslt x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(NLet x , ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x Unt e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x MkChn e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (SendEvt x\<^sub>c x\<^sub>m)) e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (RecvEvt x\<^sub>c)) e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  Let_Left: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Lft x\<^sub>p)) e)
  " |
  Let_Right: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Rght x\<^sub>p)) e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e\<^sub>b;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (NLet x, ENext, top_label e),
        (NLet x, ESpawn, top_label e\<^sub>c)
      } \<subseteq> F;
      static_traversable V F static_recv_site e\<^sub>c;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Spwn e\<^sub>c) e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
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
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Fst x\<^sub>p) e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(NLet x, ENext, top_label e)} \<subseteq> F;
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (Snd x\<^sub>p) e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (NLet x, ECall, top_label e\<^sub>l),
        (NLet x, ECall, top_label e\<^sub>r),
        (NResult (\<lfloor>e\<^sub>l\<rfloor>), EReturn x, top_label e),
        (NResult (\<lfloor>e\<^sub>r\<rfloor>), EReturn x, top_label e)
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
          (NLet x, ECall, top_label e\<^sub>b),
          (NResult (\<lfloor>e\<^sub>b\<rfloor>), EReturn x, top_label e)
        } \<subseteq> F);
      static_traversable V F static_recv_site e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F static_recv_site (Let x (App f x\<^sub>a) e)
  "

inductive 
  static_built_on_chan :: "abstract_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"
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
    \<not> Set.is_empty (Ln (top_label e\<^sub>b) - {x\<^sub>p}) \<Longrightarrow>
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

fun chan_set :: "abstract_env \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var set" where
  "chan_set V Ln x\<^sub>c x = (if (static_built_on_chan V Ln x\<^sub>c x) then {x} else {})"


inductive static_live_chan :: "abstract_env \<Rightarrow> label_map \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "
    \<lbrakk>
      chan_set V Ln x\<^sub>c y = Ln (NResult y)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Rslt y)
  " |
  Let_Unit: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      Lx (NLet x) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x Unt e)
  " |
  Let_Chan: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x MkChn e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>s\<^sub>c \<union> chan_set V Ln x\<^sub>c x\<^sub>m = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (SendEvt x\<^sub>s\<^sub>c x\<^sub>m)) e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>r\<^sub>c = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (RecvEvt x\<^sub>r\<^sub>c)) e)
  " |
  Let_Pair: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union>  chan_set V Ln x\<^sub>c x\<^sub>1 \<union> chan_set V Ln x\<^sub>c x\<^sub>2 = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  Let_Left: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Lft x\<^sub>a)) e)
  " |
  Let_Right: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Rght x\<^sub>a)) e)
  " |
  Let_Abs: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>b;
      (Lx (NLet x) - {x}) \<union> (Ln (top_label e\<^sub>b) - {x\<^sub>p}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e)
  " |
  Let_Spawn: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>c;
      Ln (top_label e) \<union> Ln (top_label e\<^sub>c) = Lx (NLet x);
      (Lx (NLet x) - {x}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Spwn e\<^sub>c) e)
  " |
  Let_Sync: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>e = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Sync x\<^sub>e) e)
  " |
  Let_Fst: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Fst x\<^sub>a) e)
  " |
  Let_Snd: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Snd x\<^sub>a) e)
  " |
  Let_Case: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>l;
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>r;
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c x\<^sub>s \<union> 
         (Ln (top_label e\<^sub>l) - {x\<^sub>l}) \<union> (Ln (top_label e\<^sub>r) - {x\<^sub>r}) = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  " |
  Let_App: "
    \<lbrakk>
      static_live_chan V Ln Lx x\<^sub>c e;
      Ln (top_label e) = Lx (NLet x);
      (Lx (NLet x) - {x}) \<union> chan_set V Ln x\<^sub>c f \<union> chan_set V Ln x\<^sub>c x\<^sub>a = Ln (NLet x)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Let x (App f x\<^sub>a) e)
  "




inductive static_traceable :: "transition_set \<Rightarrow> label \<Rightarrow> abstract_path \<Rightarrow> bool" where
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
    static_traceable F end ([(start, edge), (middle, edge')] @ post)
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

inductive static_live_traversable :: "transition_set \<Rightarrow> label_map \<Rightarrow> label_map \<Rightarrow> transition \<Rightarrow> bool"  where
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

inductive static_live_traceable :: "abstract_env \<Rightarrow> transition_set \<Rightarrow> label_map \<Rightarrow> label_map \<Rightarrow> label \<Rightarrow> (label \<Rightarrow> bool) \<Rightarrow> abstract_path \<Rightarrow> bool" where
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
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC)) singular \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_label V e) e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC)) noncompetitive \<Longrightarrow>
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_label V e) e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_label V e) e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    static_traversable V F (static_recv_label V e) e \<Longrightarrow>
    static_fan_in V e xC 
  "



end