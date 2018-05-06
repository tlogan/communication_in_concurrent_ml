theory Static_Framework
  imports Main Syntax Dynamic_Semantics Static_Semantics
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

datatype node_label = NLet var | NResult var

fun nodeLabel :: "exp \<Rightarrow> node_label" where
  "nodeLabel (LET x = b in e) = NLet x" |
  "nodeLabel (RESULT y) = NResult y"

type_synonym node_set = "node_label set"

type_synonym node_map = "node_label \<Rightarrow> var set"

datatype edge_label = ENext | ECall var | EReturn var | ESpawn |  ESend var 

type_synonym flow_label = "(node_label \<times> edge_label \<times> node_label)"

type_synonym flow_set = "flow_label set"

type_synonym step_label = "(node_label \<times> edge_label)"

type_synonym static_path = "step_label list"


inductive static_flow_set :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    static_flow_set \<V> \<F> (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(NLet x , ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = SEND EVT x\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = RECV EVT x\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = LEFT x\<^sub>p in e)
  " |
  Let_Right: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = RIGHT x\<^sub>p in e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e\<^sub>b;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (NLet x, ENext, nodeLabel e),
        (NLet x, ESpawn, nodeLabel e\<^sub>c)
      } \<subseteq> \<F>;
      static_flow_set \<V> \<F> e\<^sub>c;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      (\<forall> xSC xM xC xRC y.
        {^Send_Evt xSC xM} \<subseteq> V x\<^sub>e \<longrightarrow>
        {^Chan xC} \<subseteq> V xSC \<longrightarrow>
        {^Chan xC} \<subseteq> V xRC \<longrightarrow>
        {^Recv_Evt xRC} \<subseteq> \<V> y \<longrightarrow>
        {(NLet x, ESend xM, NLet y)} \<subseteq> \<F>
      );
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = SYNC x\<^sub>e in e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = FST x\<^sub>p in e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> \<F>;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = SND x\<^sub>p in e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (NLet x, ECall x, nodeLabel e\<^sub>l),
        (NLet x, ECall x, nodeLabel e\<^sub>r),
        (NResult (\<lfloor>e\<^sub>l\<rfloor>), EReturn x, nodeLabel e),
        (NResult (\<lfloor>e\<^sub>r\<rfloor>), EReturn x, nodeLabel e)
      } \<subseteq> \<F>;
      static_flow_set \<V> \<F> e\<^sub>l;
      static_flow_set \<V> \<F> e\<^sub>r;
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow>
        {
          (NLet x, ECall x, nodeLabel e\<^sub>b),
          (NResult (\<lfloor>e\<^sub>b\<rfloor>), EReturn x, nodeLabel e)
        } \<subseteq> \<F>);
      static_flow_set \<V> \<F> e
    \<rbrakk> \<Longrightarrow>
    static_flow_set \<V> \<F> (LET x = APP f x\<^sub>a in e)
  "

inductive is_super_exp :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  Refl : "
    is_super_exp e e
  " | 
  Let: "
    is_super_exp e\<^sub>n e \<Longrightarrow>
    is_super_exp (LET x = b in e\<^sub>n) e
  " | 
  Let_Spawn_Child: "
    is_super_exp e\<^sub>c e \<Longrightarrow>
    is_super_exp (LET x = SPAWN e\<^sub>c in e\<^sub>n) e
  " |
  Let_Case_Left: "
    is_super_exp e\<^sub>l e \<Longrightarrow>
    is_super_exp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e
  " |
  Let_Case_Right: "
    is_super_exp e\<^sub>r e \<Longrightarrow>
    is_super_exp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e
  " |
  Let_Abs_Body: "
    is_super_exp e\<^sub>b e \<Longrightarrow>
    is_super_exp (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) e
  "

end