theory Static_Communication
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
begin

datatype label = NLet var | NResult var

fun top_label :: "exp \<Rightarrow> label" where
  "top_label (Let x b e) = NLet x" |
  "top_label (Rslt y) = NResult y"

type_synonym label_set = "label set"

type_synonym label_map = "label \<Rightarrow> var set"


inductive static_traceable :: "(label * 'a * label) set \<Rightarrow> label \<Rightarrow> (label \<Rightarrow> bool) \<Rightarrow> (label * 'a) list \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    static_traceable F start isEnd []
  " |
  Step: "
    static_traceable F start (\<lambda> l . l = middle) path \<Longrightarrow>
    isEnd end \<Longrightarrow>
    {(middle, edge, end)} \<subseteq> F \<Longrightarrow>
    static_traceable F start isEnd (path @ [(middle, edge)])
  "



inductive static_send_label :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> label \<Rightarrow> bool" where
  intro: "
    {^Chan xC} \<subseteq> V xSC \<Longrightarrow>
    {^SendEvt xSC xM} \<subseteq> V xE \<Longrightarrow>
    static_reachable e (Let x (Sync xE) e') \<Longrightarrow>
    static_send_label V e xC (NLet x)
  "

inductive static_recv_label :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> label \<Rightarrow> bool" where
  intro: "
    {^Chan xC} \<subseteq> V xRC \<Longrightarrow>
    {^RecvEvt xRC} \<subseteq> V xE \<Longrightarrow>
    static_reachable e (Let x (Sync xE) e') \<Longrightarrow>
    static_recv_label V e xC (NLet x)
  "

end
