theory Static_Communication
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication
begin

datatype tm_id = IdBind name | IdRslt name

fun tmId :: "tm \<Rightarrow> tm_id" where
  "tmId (Bind x b e) = IdBind x" |
  "tmId (Rslt y) = IdRslt y"

type_synonym tm_id_set = "tm_id set"

type_synonym tm_id_map = "tm_id \<Rightarrow> name set"

inductive staticSendSite :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> tm_id \<Rightarrow> bool" where
  intro: "
    {^Chan xC} \<subseteq> V xSC \<Longrightarrow>
    {^SendEvt xSC xM} \<subseteq> V xE \<Longrightarrow>
    staticReachable e (Bind x (Sync xE) e') \<Longrightarrow>
    staticSendSite V e xC (IdBind x)
  "

inductive staticRecvSite :: "static_env \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> tm_id \<Rightarrow> bool" where
  intro: "
    {^Chan xC} \<subseteq> V xRC \<Longrightarrow>
    {^RecvEvt xRC} \<subseteq> V xE \<Longrightarrow>
    staticReachable e (Bind x (Sync xE) e') \<Longrightarrow>
    staticRecvSite V e xC (IdBind x)
  "

end
