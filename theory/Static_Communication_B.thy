theory Static_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
    Static_Communication
begin

datatype mode = ENext | ESpawn | ESend name | ECall | EReturn

type_synonym flow = "(tm_id \<times> mode \<times> tm_id)"

type_synonym flow_set = "flow set"

type_synonym step = "(tm_id \<times> mode)"

type_synonym static_path = "step list"

inductive staticFlowsAccept :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> bool"  where
  Result:
  "
    staticFlowsAccept V F (Rslt x)
  "
| BindUnit:
  "
    \<lbrakk>
      {(IdBind x , ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x Unt e)
  "
| BindMkChn:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x MkChn e)
  "
| BindSend_Evt:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (SendEvt x\<^sub>c x\<^sub>m)) e)
  "
| BindRecv_Evt:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (RecvEvt x\<^sub>c)) e)
  "
| BindPair:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Pair x\<^sub>1 x\<^sub>2)) e)
  "
| BindLeft:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Lft x\<^sub>p)) e)
  "
| BindRight:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Rht x\<^sub>p)) e)
  "
| BindFun:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e\<^sub>b;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e)
  "
| BindSpawn:
  "
    \<lbrakk>
      {
        (IdBind x, ENext, tmId e),
        (IdBind x, ESpawn, tmId e\<^sub>c)
      } \<subseteq> F;
      staticFlowsAccept V F e\<^sub>c;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Spwn e\<^sub>c) e)
  "
| BindSync:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      (\<forall> xSC xM xC y.
        {^SendEvt xSC xM} \<subseteq> V xSE \<longrightarrow>
        {^Chan xC} \<subseteq> V xSC \<longrightarrow>
        staticRecvSite V e xC (IdBind y) \<longrightarrow>
        {(IdBind x, ESend xSE, IdBind y)} \<subseteq> F
      );
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Sync xSE) e)
  "
| BindFst:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Fst x\<^sub>p) e)
  "
| BindSnd:
  "
    \<lbrakk>
      {(IdBind x, ENext, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Snd x\<^sub>p) e)
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
      staticFlowsAccept V F e\<^sub>l;
      staticFlowsAccept V F e\<^sub>r;
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  "
| BindApp:
  "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Fun f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow>
        {
          (IdBind x, ECall, tmId e\<^sub>b),
          (IdRslt (\<lfloor>e\<^sub>b\<rfloor>), EReturn, tmId e)
        } \<subseteq> F);
      staticFlowsAccept V F e
    \<rbrakk> \<Longrightarrow>
    staticFlowsAccept V F (Bind x (App f x\<^sub>a) e)
  "


inductive 
  static_built_on_chan :: "static_env \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool"
where
  Chan:
  "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> V x 
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V x\<^sub>c x
  "
| Send_Evt:
  "
    \<lbrakk>
      ^SendEvt x\<^sub>s\<^sub>c x\<^sub>m \<in> V x;
      static_built_on_chan V x\<^sub>c x\<^sub>s\<^sub>c \<or> static_built_on_chan V x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V x\<^sub>c x
  "
| Recv_Evt:
  "
    \<lbrakk>
      ^RecvEvt x\<^sub>r\<^sub>c \<in> V x;
      static_built_on_chan V x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V x\<^sub>c x
  "
| Pair:
  "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> V x;
      static_built_on_chan V x\<^sub>c x\<^sub>1 \<or> static_built_on_chan V x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V x\<^sub>c x
  "
| Left:
  "
    \<lbrakk>
      ^(Lft x\<^sub>a) \<in> V x;
      static_built_on_chan V x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V x\<^sub>c x
  "
| Right:
  "
    \<lbrakk>
      ^(Rht x\<^sub>a) \<in> V x;
      static_built_on_chan V x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    static_built_on_chan V x\<^sub>c x
  "
| Fun:
  "
    ^Fun f x\<^sub>p e\<^sub>b \<in> V x \<Longrightarrow> 
    n\<^sub>f\<^sub>v \<in> freeVarsAtom (Fun f x\<^sub>p e\<^sub>b) \<Longrightarrow>
    static_built_on_chan V x\<^sub>c n\<^sub>f\<^sub>v \<Longrightarrow>
    static_built_on_chan V x\<^sub>c x
  " 


inductive static_live_chan :: "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> tm \<Rightarrow> bool" where
  Result:
  "
    \<lbrakk>
      (static_built_on_chan V x\<^sub>c y) \<longrightarrow> {y} \<subseteq> Ln (IdRslt y)
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Rslt y)
  "
| BindUnit:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x Unt e)
  "
| BindMkChn:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x MkChn e)
  "
| BindSend_Evt:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>s\<^sub>c \<longrightarrow> {x\<^sub>s\<^sub>c} \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>m \<longrightarrow> {x\<^sub>m} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Atom (SendEvt x\<^sub>s\<^sub>c x\<^sub>m)) e)
  "
| BindRecv_Evt:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>r \<longrightarrow> {x\<^sub>r} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Atom (RecvEvt x\<^sub>r\<^sub>c)) e)
  "
| BindPair:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>1 \<longrightarrow> {x\<^sub>1} \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>2 \<longrightarrow> {x\<^sub>2} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Atom (Pair x\<^sub>1 x\<^sub>2)) e)
  "
| BindLeft:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Atom (Lft x\<^sub>a)) e)
  "
| BindRight:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Atom (Rht x\<^sub>a)) e)
  "
| BindFun:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<union> (Ln (tmId e\<^sub>b) - {x\<^sub>p}) \<subseteq> Ln (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>b;
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e)
  "
| BindSpawn:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<union> Ln (tmId e\<^sub>c) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>c;
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Spwn e\<^sub>c) e)
  "
| BindSync:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>e \<longrightarrow> {x\<^sub>e} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Sync x\<^sub>e) e)
  "
| BindFst:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Fst x\<^sub>a) e)
  "
| BindSnd:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Snd x\<^sub>a) e)
  "
| BindCase:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<union> (Ln (tmId e\<^sub>l) - {x\<^sub>l}) \<union> (Ln (tmId e\<^sub>r) - {x\<^sub>r}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>s \<longrightarrow> {x\<^sub>s} \<subseteq> Ln (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>l;
      static_live_chan V Ln Lx x\<^sub>c e\<^sub>r;
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  "
| BindApp:
  "
    \<lbrakk>
      (Lx (IdBind x) - {x}) \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c x\<^sub>a \<longrightarrow> {x\<^sub>a} \<subseteq> Ln (IdBind x);
      static_built_on_chan V x\<^sub>c f \<longrightarrow> {f} \<subseteq> Ln (IdBind x);
      Ln (tmId e) \<subseteq> Lx (IdBind x);
      static_live_chan V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_live_chan V Ln Lx x\<^sub>c (Bind x (App f x\<^sub>a) e)
  "

(*
inductive static_balanced :: "static_path \<Rightarrow> bool" where
  Empty:
  "
    static_balanced []
  "
| Next:
  "
    static_balanced [(IdBind x, ENext)]
  "
| CallReturn:
  "
    static_balanced path \<Longrightarrow>
    static_balanced ((IdBind x, ECall) # (path @ [(IdRslt y, EReturn)]))
  "
| Append:
  "
    path \<noteq> [] \<Longrightarrow>
    static_balanced path \<Longrightarrow>
    path' \<noteq> [] \<Longrightarrow>
    static_balanced path' \<Longrightarrow>
    static_balanced (path @ path')
  "
*)
(*
inductive static_unbalanced :: "static_path \<Rightarrow> bool" where
  Result:
  "
    static_unbalanced ((IdRslt y, EReturn) # post)
  "
| Next:
  "
    static_unbalanced post \<Longrightarrow>
    static_unbalanced ((IdBind x, ENext) # post)
  "
*)

inductive static_live_flow :: "flow_set \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> flow \<Rightarrow> bool"  where
  Next:
  "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_flow F Ln Lx (l, ENext, l')
  "
| Spawn:
  "
    (l, ESpawn, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_flow F Ln Lx (l, ESpawn, l')
  "
| Call_Live_Outer:
  "
    (l, ECall, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    static_live_flow F Ln Lx (l, ECall, l')
  "
| Call_Live_Inner:
  "
    (l, ECall, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_flow F Ln Lx (l, ECall, l')
  "
| Return:
  "
    (l, EReturn, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    static_live_flow F Ln Lx (l, EReturn, l')
  "
| Send:
  "
    ((IdBind xSend), ESend xE, (IdBind xRecv)) \<in> F \<Longrightarrow>
    {xE} \<subseteq> (Ln (IdBind xSend)) \<Longrightarrow>
    static_live_flow F Ln Lx ((IdBind xSend), ESend xE, (IdBind xRecv))
  "



inductive staticTraceable :: "flow_set \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> tm_id \<Rightarrow> (tm_id \<Rightarrow> bool) \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty:
  "
    isEnd start \<Longrightarrow>
    staticTraceable F Ln Lx start isEnd []
  "
| Edge:
  "
    staticTraceable F Ln Lx start (\<lambda> l . l = middle) path \<Longrightarrow>
    isEnd end \<Longrightarrow>

    static_live_flow F Ln Lx (middle, edge, end) \<Longrightarrow>

    staticTraceable F Ln Lx start isEnd (path @ [(middle, edge)])
  " 


(*|

  Pre_Return:
  "
    staticTraceable V F Ln Lx (IdRslt y) isEnd ((IdRslt y, EReturn) # post) \<Longrightarrow>

(* staticTraceable F (IdRslt y) (\<lambda> l . l = tmId (Rslt x)) pre *)
 (*   staticTraceable F (IdRslt y) pre \<Longrightarrow> *)
    \<not> static_balanced (pre @ [(IdRslt y, EReturn)]) \<Longrightarrow>
    \<not> Set.is_empty (Lx (IdBind x)) \<Longrightarrow>
    path = pre @ (IdRslt y, EReturn) # post \<Longrightarrow>
    staticTraceable V F Ln Lx start isEnd (path @ [(IdRslt y, EReturn)])
  " 
*)


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


inductive static_one_shot :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    every_two (staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC)) singular \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    every_two (staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
    every_two (staticTraceable F Ln Lx (IdBind xC) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    every_two (staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> bool" where
  Sync:
  "
    every_two (staticTraceable F Ln Lx (IdBind xC) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
    static_live_chan V Ln Lx xC e \<Longrightarrow>
    staticFlowsAccept V F e \<Longrightarrow>
    static_fan_in V e xC 
  "



end
