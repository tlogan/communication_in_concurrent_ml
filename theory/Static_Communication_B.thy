theory Static_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
    Static_Communication
begin

datatype mode = ENext | ESpawn | ESend name | ECall | EReturn

type_synonym flow = "(tm_id * mode * tm_id)"

type_synonym flow_set = "flow set"

type_synonym step = "(tm_id * mode)"

type_synonym static_path = "step list"

inductive staticFlowsAccept :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> bool"  where
  Result:
  "
    staticFlowsAccept staticEnv graph (Rslt x)
  "
| BindUnit:
  "
    \<lbrakk>
      {(IdBind x , ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x Unt e)
  "
| BindMkChn:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x MkChn e)
  "
| BindSendEvt:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Atom (SendEvt x\<^sub>c x\<^sub>m)) e)
  "
| BindRecvEvt:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Atom (RecvEvt x\<^sub>c)) e)
  "
| BindPair:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Atom (Pair x\<^sub>1 x\<^sub>2)) e)
  "
| BindLeft:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Atom (Lft x\<^sub>p)) e)
  "
| BindRight:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Atom (Rht x\<^sub>p)) e)
  "
| BindFun:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e\<^sub>b;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e)
  "
| BindSpawn:
  "
    \<lbrakk>
      {
        (IdBind x, ENext, tmId e),
        (IdBind x, ESpawn, tmId e\<^sub>c)
      } \<subseteq> F;
      staticFlowsAccept staticEnv graph e\<^sub>c;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Spwn e\<^sub>c) e)
  "
| BindSync:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      (\<forall> xSC xM xC y.
        {SAtm (SendEvt xSC xM)} \<subseteq> staticEnv xSE \<longrightarrow>
        {SChn xC} \<subseteq> staticEnv xSC \<longrightarrow>
        staticRecvSite staticEnv e xC (IdBind y) \<longrightarrow>
        {(IdBind x, ESend xSE, IdBind y)} \<subseteq> F
      );
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Sync xSE) e)
  "
| BindFst:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Fst x\<^sub>p) e)
  "
| BindSnd:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Snd x\<^sub>p) e)
  "
| BindCase:
  "
    \<lbrakk>
      {
        (IdBind x, ECall, tmId e\<^sub>l),
        (IdBind x, ECall, tmId e\<^sub>r),
        (IdRslt (\<lfloor>e\<^sub>l\<rfloor>), EReturn, tmId e),
        (IdRslt (\<lfloor>e\<^sub>r\<rfloor>), EReturn, tmId e)
      } \<subseteq> F;
      staticFlowsAccept staticEnv graph e\<^sub>l;
      staticFlowsAccept staticEnv graph e\<^sub>r;
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  "
| BindApp:
  "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . SAtm (Fun f' x\<^sub>p e\<^sub>b) \<in> staticEnv f \<longrightarrow>
        {
          (IdBind x, ECall, tmId e\<^sub>b),
          (IdRslt (\<lfloor>e\<^sub>b\<rfloor>), EReturn, tmId e)
        } \<subseteq> F);
      staticFlowsAccept staticEnv graph e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept staticEnv graph (Bind x (App f x\<^sub>a) e)
  "


inductive 
  staticBuiltOnChan :: "static_env \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool"
where
  Chan:
  "
    \<lbrakk>
      SChn x\<^sub>c \<in> staticEnv x 
    \<rbrakk> \<Longrightarrow> 
    staticBuiltOnChan staticEnv x\<^sub>c x
  "
| Send_Evt:
  "
    \<lbrakk>
      SAtm (SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<in> staticEnv x;
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>s\<^sub>c \<or> staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    staticBuiltOnChan staticEnv x\<^sub>c x
  "
| Recv_Evt:
  "
    \<lbrakk>
      SAtm (RecvEvt x\<^sub>r\<^sub>c) \<in> staticEnv x;
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    staticBuiltOnChan staticEnv x\<^sub>c x
  "
| Pair:
  "
    \<lbrakk>
      SAtm (Pair x\<^sub>1 x\<^sub>2) \<in> staticEnv x;
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>1 \<or> staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    staticBuiltOnChan staticEnv x\<^sub>c x
  "
| Left:
  "
    \<lbrakk>
      SAtm (Lft x\<^sub>a) \<in> staticEnv x;
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    staticBuiltOnChan staticEnv x\<^sub>c x
  "
| Right:
  "
    \<lbrakk>
      SAtm (Rht x\<^sub>a) \<in> staticEnv x;
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    staticBuiltOnChan staticEnv x\<^sub>c x
  "
| Fun:
  "
    SAtm (Fun f x\<^sub>p e\<^sub>b) \<in> staticEnv x \<Longrightarrow> 
    n\<^sub>f\<^sub>v \<in> freeVarsAtom (Fun f x\<^sub>p e\<^sub>b) \<Longrightarrow>
    staticBuiltOnChan staticEnv x\<^sub>c n\<^sub>f\<^sub>v \<Longrightarrow>
    staticBuiltOnChan staticEnv x\<^sub>c x
  " 


inductive staticLiveChan :: "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> tm \<Rightarrow> bool" where
  Result:
  "
    \<lbrakk>
      (staticBuiltOnChan staticEnv x\<^sub>c y) \<longrightarrow> {y} \<subseteq> entr (IdRslt y)
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Rslt y)
  "
| BindUnit:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x Unt e)
  "
| BindMkChn:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x MkChn e)
  "
| BindSend_Evt:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>s\<^sub>c \<longrightarrow> {x\<^sub>s\<^sub>c} \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>m \<longrightarrow> {x\<^sub>m} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Atom (SendEvt x\<^sub>s\<^sub>c x\<^sub>m)) e)
  "
| BindRecv_Evt:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>r \<longrightarrow> {x\<^sub>r} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Atom (RecvEvt x\<^sub>r\<^sub>c)) e)
  "
| BindPair:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>1 \<longrightarrow> {x\<^sub>1} \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>2 \<longrightarrow> {x\<^sub>2} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Atom (Pair x\<^sub>1 x\<^sub>2)) e)
  "
| BindLeft:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Atom (Lft x\<^sub>a)) e)
  "
| BindRight:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Atom (Rht x\<^sub>a)) e)
  "
| BindFun:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<union> (entr (tmId e\<^sub>b) - {x\<^sub>p}) \<subseteq> entr (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e\<^sub>b;
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e)
  "
| BindSpawn:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      entr (tmId e) \<union> entr (tmId e\<^sub>c) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e\<^sub>c;
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Spwn e\<^sub>c) e)
  "
| BindSync:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>e \<longrightarrow> {x\<^sub>e} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Sync x\<^sub>e) e)
  "
| BindFst:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Fst x\<^sub>a) e)
  "
| BindSnd:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Snd x\<^sub>a) e)
  "
| BindCase:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<union> (entr (tmId e\<^sub>l) - {x\<^sub>l}) \<union> (entr (tmId e\<^sub>r) - {x\<^sub>r}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>s \<longrightarrow> {x\<^sub>s} \<subseteq> entr (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e\<^sub>l;
      staticLiveChan staticEnv entr exit x\<^sub>c e\<^sub>r;
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  "
| BindApp:
  "
    \<lbrakk>
      (exit (IdBind x) - {x}) \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> entr (IdBind x);
      staticBuiltOnChan staticEnv x\<^sub>c f \<longrightarrow> {f} \<subseteq> entr (IdBind x);
      entr (tmId e) \<subseteq> exit (IdBind x);
      staticLiveChan staticEnv entr exit x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    staticLiveChan staticEnv entr exit x\<^sub>c (Bind x (App f x\<^sub>a) e)
  "

inductive staticLiveFlow :: "flow_set \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> flow \<Rightarrow> bool"  where
  Next:
  "
    (l, ENext, l') \<in> graph \<Longrightarrow>
    \<not> Set.is_empty (exit l) \<Longrightarrow>
    \<not> Set.is_empty (entr l') \<Longrightarrow>
    staticLiveFlow graph entr exit (l, ENext, l')
  "
| Spawn:
  "
    (l, ESpawn, l') \<in> graph \<Longrightarrow>
    \<not> Set.is_empty (exit l) \<Longrightarrow>
    \<not> Set.is_empty (entr l') \<Longrightarrow>
    staticLiveFlow graph entr exit (l, ESpawn, l')
  "
| CallOuter:
  "
    (l, ECall, l') \<in> graph \<Longrightarrow>
    \<not> Set.is_empty (exit l) \<Longrightarrow>
    staticLiveFlow graph entr exit (l, ECall, l')
  "
| CallInner:
  "
    (l, ECall, l') \<in> graph \<Longrightarrow>
    \<not> Set.is_empty (entr l') \<Longrightarrow>
    staticLiveFlow graph entr exit (l, ECall, l')
  "
| Return:
  "
    (l, EReturn, l') \<in> graph \<Longrightarrow>
    \<not> Set.is_empty (entr l') \<Longrightarrow>
    staticLiveFlow graph entr exit (l, EReturn, l')
  "
| Send:
  "
    ((IdBind xSend), ESend xE, (IdBind xRecv)) \<in> graph \<Longrightarrow>
    {xE} \<subseteq> (entr (IdBind xSend)) \<Longrightarrow>
    staticLiveFlow graph entr exit ((IdBind xSend), ESend xE, (IdBind xRecv))
  "



inductive staticTraceable :: "flow_set \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> tm_id \<Rightarrow> (tm_id \<Rightarrow> bool) \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty:
  "
    \<forall> end edge . isEnd end \<longrightarrow> \<not> staticLiveFlow graph entr exit (start, edge, end) \<Longrightarrow>
    staticTraceable graph entr exit start isEnd []
  "
| Edge:
  "
    staticTraceable graph entr exit start (\<lambda> l . l = middle) path \<Longrightarrow>
    isEnd end \<Longrightarrow>

    staticLiveFlow graph entr exit (middle, edge, end) \<Longrightarrow>

    staticTraceable graph entr exit start isEnd (path @ [(middle, edge)])
  "

inductive staticInclusive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Prefix1:
  "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>
    staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  "
| Prefix2:
  "
    prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  "
| Spawn1:
  "
    staticInclusive (\<pi> @ (IdBind x, ESpawn) # \<pi>\<^sub>1) (\<pi> @ (IdBind x, ENext) # \<pi>\<^sub>2)
  "
| Spawn2:
  "
    staticInclusive (\<pi> @ (IdBind x, ENext) # \<pi>\<^sub>1) (\<pi> @ (IdBind x, ESpawn) # \<pi>\<^sub>2)
  "
| Send1:
  "
    staticInclusive (\<pi> @ (IdBind x, ESend xE) # \<pi>\<^sub>1) (\<pi> @ (IdBind x, ENext) # \<pi>\<^sub>2)
  "
| Send2:
  "
    staticInclusive (\<pi> @ (IdBind x, ENext) # \<pi>\<^sub>1) (\<pi> @ (IdBind x, ESend xE) # \<pi>\<^sub>2)
  "

inductive singular :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  equal:
  "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "
| exclusive:
  "
    \<not> (staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2) \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive noncompetitive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
  ordered:
  "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "
| exclusive:
  "
    \<not> (staticInclusive \<pi>\<^sub>1 \<pi>\<^sub>2) \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


inductive staticOneShot :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    forEveryTwo (staticTraceable graph entr exit (IdBind xC) (staticSendSite staticEnv e xC)) singular \<Longrightarrow>
    staticLiveChan staticEnv entr exit xC e \<Longrightarrow>
    staticFlowsAccept staticEnv graph e \<Longrightarrow>
    staticOneShot staticEnv e xC 
  "

inductive staticOneToOne :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    forEveryTwo (staticTraceable graph entr exit (IdBind xC) (staticSendSite staticEnv e xC)) noncompetitive \<Longrightarrow>
    forEveryTwo (staticTraceable graph entr exit (IdBind xC) (staticRecvSite staticEnv e xC)) noncompetitive \<Longrightarrow>
    staticLiveChan staticEnv entr exit xC e \<Longrightarrow>
    staticFlowsAccept staticEnv graph e \<Longrightarrow>
    staticOneToOne staticEnv e xC 
  "

inductive staticOneToMany :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    forEveryTwo (staticTraceable graph entr exit (IdBind xC) (staticSendSite staticEnv e xC)) noncompetitive \<Longrightarrow>
    staticLiveChan staticEnv entr exit xC e \<Longrightarrow>
    staticFlowsAccept staticEnv graph e \<Longrightarrow>
    staticOneToMany staticEnv e xC 
  "

inductive staticManyToOne :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    forEveryTwo (staticTraceable graph entr exit (IdBind xC) (staticRecvSite staticEnv e xC)) noncompetitive \<Longrightarrow>
    staticLiveChan staticEnv entr exit xC e \<Longrightarrow>
    staticFlowsAccept staticEnv graph e \<Longrightarrow>
    staticManyToOne staticEnv e xC 
  "



end
