theory Static_Communication_A
  imports Main Syntax 
    Dynamic_Semantics 
    Static_Semantics
    Dynamic_Communication
    Static_Communication
begin

datatype mode = ENext | ESpawn | ECall | EReturn

type_synonym flow = "(tm_id \<times> mode \<times> tm_id)"

type_synonym flow_set = "flow set"

type_synonym step = "(tm_id \<times> mode)"

type_synonym static_path = "step list"


inductive staticFlowsAccept :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> bool"  where
  Result: "
    staticFlowsAccept V F (Rslt x)
  " |
  BindUnit: "
    \<lbrakk>
      {(IdBind x , ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x Unt e)
  " |
  BindMkChn: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x MkChn e)
  " |
  BindSendEvt: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (SendEvt x\<^sub>c x\<^sub>m)) e)
  " |
  BindRecvEvt: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (RecvEvt x\<^sub>c)) e)
  " |
  BindPair: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  BindLeft: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Lft x\<^sub>p)) e)
  " |
  BindRight: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Rht x\<^sub>p)) e)
  " |
  BindFun: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e\<^sub>b;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e)
  " |
  BindSpawn: "
    \<lbrakk>
      {
        (IdBind x, ENext, tmId e),
        (IdBind x, ESpawn, tmId e\<^sub>c)
      } \<subseteq> F;
      staticFlowsAccept V F e\<^sub>c;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Spwn e\<^sub>c) e)
  " |
  BindSync: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Sync xSE) e)
  " |
  BindFst: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Fst x\<^sub>p) e)
  " |
  BindSnd: "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Snd x\<^sub>p) e)
  " |
  BindCase: "
    \<lbrakk>
      {
        (IdBind x, ECall, tmId e\<^sub>l),
        (IdBind x, ECall, tmId e\<^sub>r),
        (IdRslt (\<lfloor>e\<^sub>l\<rfloor>), EReturn, tmId e),
        (IdRslt (\<lfloor>e\<^sub>r\<rfloor>), EReturn, tmId e)
      } \<subseteq> F;
      staticFlowsAccept V F e\<^sub>l;
      staticFlowsAccept V F e\<^sub>r;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  " |
  BindApp: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . SAtm (Fun f' x\<^sub>p e\<^sub>b) \<in> V f \<longrightarrow>
        {
          (IdBind x, ECall, tmId e\<^sub>b),
          (IdRslt (\<lfloor>e\<^sub>b\<rfloor>), EReturn, tmId e)
        } \<subseteq> F);
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (App f x\<^sub>a) e)
  "




inductive staticInclusive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Prefix1: "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>
    staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Prefix2: "
    prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Spawn1: "
    staticInclusive (\<pi> @ (IdBind x, ESpawn) # \<pi>\<^sub>1) (\<pi> @ (IdBind x, ENext) # \<pi>\<^sub>2)
  " |
  Spawn2: "
    staticInclusive (\<pi> @ (IdBind x, ENext) # \<pi>\<^sub>1) (\<pi> @ (IdBind x, ESpawn) # \<pi>\<^sub>2)
  "


inductive singular :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  equal: "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2) \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive noncompetitive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  ordered: "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2) \<Longrightarrow>
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


inductive staticTraceable :: "(tm_id * 'a * tm_id) set \<Rightarrow> tm_id \<Rightarrow> (tm_id \<Rightarrow> bool) \<Rightarrow> (tm_id * 'a) list \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    staticTraceable F start isEnd []
  " |
  Step: "
    staticTraceable F start (\<lambda> l . l = middle) path \<Longrightarrow>
    isEnd end \<Longrightarrow>
    {(middle, edge, end)} \<subseteq> F \<Longrightarrow>
    staticTraceable F start isEnd (path @ [(middle, edge)])
  "



inductive staticOneToMany :: "tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync: "
    forEveryTwo (staticTraceable F (tmId e) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
    staticOneToMany e xC 
  "

inductive staticManyToOne :: "tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync: "
    forEveryTwo (staticTraceable F (tmId e) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
    staticManyToOne e xC 
  "


inductive staticOneToOne :: "tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync: "
    forEveryTwo (staticTraceable F (tmId e) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
    forEveryTwo (staticTraceable F (tmId e) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
    staticOneToOne e xC 
  "
inductive staticOneShot :: "tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync: "
    forEveryTwo (staticTraceable F (tmId e) (staticSendSite V e xC)) singular \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
    staticOneShot e xC 
  "


inductive staticOneSync :: "tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync: "
    forEveryTwo (staticTraceable F (tmId e) (staticSendSite V e xC)) singular \<Longrightarrow>
    forEveryTwo (staticTraceable F (tmId e) (staticRecvSite V e xC)) singular \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
    staticOneSync e xC 
  "


end
