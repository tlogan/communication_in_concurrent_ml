theory Static_Communication_A
  imports Main Syntax 
    Dynamic_Semantics 
    Static_Semantics
    Dynamic_Communication
    Static_Communication
begin

datatype edge_label = ENext | ESpawn | ECall | EReturn

type_synonym flow_label = "(node_label \<times> edge_label \<times> node_label)"

type_synonym flow_set = "flow_label set"

type_synonym step_label = "(node_label \<times> edge_label)"

type_synonym abstract_path = "step_label list"


inductive static_traversable :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_traversable V F (Rslt x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(NLet x , ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x Unt e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x MkChn e)
  " |
  Let_SendEvt: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Prim (SendEvt x\<^sub>c x\<^sub>m)) e)
  " |
  Let_RecvEvt: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Prim (RecvEvt x\<^sub>c)) e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Prim (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  Let_Left: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Prim (Lft x\<^sub>p)) e)
  " |
  Let_Right: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Prim (Rght x\<^sub>p)) e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e\<^sub>b;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (NLet x, ENext, top_node_label e),
        (NLet x, ESpawn, top_node_label e\<^sub>c)
      } \<subseteq> F;
      static_traversable V F e\<^sub>c;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Spwn e\<^sub>c) e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Sync xSE) e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Fst x\<^sub>p) e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(NLet x, ENext, top_node_label e)} \<subseteq> F;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Snd x\<^sub>p) e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (NLet x, ECall, top_node_label e\<^sub>l),
        (NLet x, ECall, top_node_label e\<^sub>r),
        (NResult (\<lfloor>e\<^sub>l\<rfloor>), EReturn, top_node_label e),
        (NResult (\<lfloor>e\<^sub>r\<rfloor>), EReturn, top_node_label e)
      } \<subseteq> F;
      static_traversable V F e\<^sub>l;
      static_traversable V F e\<^sub>r;
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow>
        {
          (NLet x, ECall, top_node_label e\<^sub>b),
          (NResult (\<lfloor>e\<^sub>b\<rfloor>), EReturn, top_node_label e)
        } \<subseteq> F);
      static_traversable V F e
    \<rbrakk> \<Longrightarrow>
    static_traversable V F (Let x (App f x\<^sub>a) e)
  "



inductive static_traceable :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> node_label \<Rightarrow> (node_label \<Rightarrow> bool) \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    static_traceable V F start isEnd []
  " |
  Edge: "
    isEnd end \<Longrightarrow>
    {(start, edge, end)} \<subseteq> F \<Longrightarrow>
    static_traceable V F start isEnd [(start, edge)]
  " |
  Step: "
    static_traceable V F middle isEnd ((middle, edge') # path) \<Longrightarrow>
    {(start, edge, middle)} \<subseteq> F \<Longrightarrow>
    static_traceable V F start isEnd ((start, edge) # (middle, edge') # path)
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
    every_two (static_traceable V F (top_node_label e) (static_send_node_label V e xC)) singular \<Longrightarrow>
    static_traversable V F e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_traceable V F (top_node_label e) (static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    every_two (static_traceable V F (top_node_label e) (static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_traversable V F e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_traceable V F (top_node_label e) (static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_traversable V F e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (static_traceable V F (top_node_label e) (static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_traversable V F e \<Longrightarrow>
    static_fan_in V e xC 
  "

locale communication_sound_A = 
  Static_Communication.communication_sound static_one_shot static_fan_out static_fan_in static_one_to_one

end
