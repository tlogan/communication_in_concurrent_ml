theory Static_Communication
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
begin

datatype node_label = NLet var | NResult var

fun top_node_label :: "exp \<Rightarrow> node_label" where
  "top_node_label (Let x b e) = NLet x" |
  "top_node_label (Rslt y) = NResult y"

type_synonym node_set = "node_label set"

type_synonym node_map = "node_label \<Rightarrow> var set"

inductive static_send_node_label :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  intro: "
    {^Chan xC} \<subseteq> V xSC \<Longrightarrow>
    {^SendEvt xSC xM} \<subseteq> V xE \<Longrightarrow>
    static_reachable e (Let x (Sync xE) e') \<Longrightarrow>
    static_send_node_label V e xC (NLet x)
  "

inductive static_recv_node_label :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  intro: "
    {^Chan xC} \<subseteq> V xRC \<Longrightarrow>
    {^RecvEvt xRC} \<subseteq> V xE \<Longrightarrow>
    static_reachable e (Let x (Sync xE) e') \<Longrightarrow>
    static_recv_node_label V e xC (NLet x)
  "

end
