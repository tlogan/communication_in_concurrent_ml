theory Static_Framework
  imports Main Syntax Dynamic_Semantics Static_Semantics
      Static_Traceability
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


inductive is_super_exp :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  Refl : "
    is_super_exp e e
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
  " | 
  Let: "
    is_super_exp e\<^sub>n e \<Longrightarrow>
    is_super_exp (LET x = b in e\<^sub>n) e
  "


lemma is_super_exp_trans: "
  is_super_exp e\<^sub>z e\<^sub>y \<Longrightarrow> is_super_exp e\<^sub>y e\<^sub>x \<Longrightarrow> is_super_exp e\<^sub>z e\<^sub>x
"
proof -
  assume "is_super_exp e\<^sub>y e\<^sub>x "
  assume "is_super_exp e\<^sub>z e\<^sub>y" then
  have "(\<forall> e\<^sub>x . is_super_exp e\<^sub>y e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>z e\<^sub>x)"
  proof (induction rule: is_super_exp.induct)
    case (Refl e)
    show "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e e\<^sub>x" by simp
  next
    case (Let e\<^sub>n e x b)
    assume "is_super_exp e\<^sub>n e" "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>n e\<^sub>x"

    have "\<forall>e\<^sub>x. is_super_exp e\<^sub>n e\<^sub>x \<longrightarrow> is_super_exp (LET x = b in e\<^sub>n) e\<^sub>x" by (simp add: is_super_exp.Let) 
    with `\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>n e\<^sub>x`
    show "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp (LET x = b in e\<^sub>n) e\<^sub>x" by blast
  next
    case (Let_Spawn_Child e\<^sub>c e x e\<^sub>n)
    assume "is_super_exp e\<^sub>c e" "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>c e\<^sub>x"

    have "\<forall>e\<^sub>x. is_super_exp e\<^sub>c e\<^sub>x \<longrightarrow> is_super_exp (LET x = SPAWN e\<^sub>c in e\<^sub>n) e\<^sub>x" by (simp add: is_super_exp.Let_Spawn_Child)
    with `\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>c e\<^sub>x`
    show "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp (LET x = SPAWN e\<^sub>c in e\<^sub>n) e\<^sub>x"by blast
  next
    case (Let_Case_Left e\<^sub>l e x x\<^sub>s x\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    assume "is_super_exp e\<^sub>l e" "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>l e\<^sub>x"

    have "\<forall>e\<^sub>x. is_super_exp e\<^sub>l e\<^sub>x \<longrightarrow> is_super_exp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e\<^sub>x" by (simp add: is_super_exp.Let_Case_Left)
    with `\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>l e\<^sub>x`
    show "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e\<^sub>x" by blast
  next
    case (Let_Case_Right e\<^sub>r e x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>n)
    assume "is_super_exp e\<^sub>r e" "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>r e\<^sub>x"

    have "\<forall>e\<^sub>x. is_super_exp e\<^sub>r e\<^sub>x \<longrightarrow> is_super_exp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e\<^sub>x" by (simp add: is_super_exp.Let_Case_Right)
    with `\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>r e\<^sub>x`
    show "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) e\<^sub>x" by blast
  next
    case (Let_Abs_Body e\<^sub>b e x f x\<^sub>p e\<^sub>n)
    assume "is_super_exp e\<^sub>b e" "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>b e\<^sub>x"

    have "\<forall>e\<^sub>x. is_super_exp e\<^sub>b e\<^sub>x \<longrightarrow> is_super_exp (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) e\<^sub>x" by (simp add: is_super_exp.Let_Abs_Body)
    with `\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp e\<^sub>b e\<^sub>x`
    show "\<forall>e\<^sub>x. is_super_exp e e\<^sub>x \<longrightarrow> is_super_exp (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) e\<^sub>x" by blast
  qed 
  with `is_super_exp e\<^sub>y e\<^sub>x`
  show "is_super_exp e\<^sub>z e\<^sub>x" by blast
qed

lemma is_super_exp1: "
  is_super_exp (LET x = b in e\<^sub>n) e\<^sub>n
"
by (simp add: Let Refl)


(*
fun val_to_bind :: "val \<Rightarrow> bind" where
  "val_to_bind VUnit = \<lparr>\<rparr>" |
  "val_to_bind (VChan _) = CHAN \<lparr>\<rparr>" |
  "val_to_bind (VClosure p _) = Prim p"

theorem static_traceable_implies_is_super_exp: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . is_super_exp e\<^sub>0 (LET x = val_to_bind \<omega> in e\<^sub>n )))
  \<rbrakk> \<Longrightarrow>
  is_super_exp e\<^sub>0 e 
"
proof -
  assume "\<forall>x \<omega>. |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists>x e\<^sub>n. is_super_exp e\<^sub>0 (LET x = val_to_bind \<omega> in e\<^sub>n ))"
  assume "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e" then
  have "(\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . is_super_exp e\<^sub>0 (LET x = val_to_bind \<omega> in e\<^sub>n ))) \<longrightarrow> is_super_exp e\<^sub>0 e"
  proof (induction rule: static_traceable.induct)
    case (Start \<V> e\<^sub>0)
    then show ?case by (simp add: Refl)
  next
    thm Result
    case (Result \<V> e\<^sub>0 \<pi> x \<pi>' x\<^sub>r b e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Unit \<V> e\<^sub>0 \<pi> x e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Chan \<V> e\<^sub>0 \<pi> x e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Prim \<V> e\<^sub>0 \<pi> x p e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Spawn_Child \<V> e\<^sub>0 \<pi> x e\<^sub>c e\<^sub>n)
    then show ?case  using Refl is_super_exp.Let_Spawn_Child is_super_exp_trans by blast
  next
    case (Let_Spawn \<V> e\<^sub>0 \<pi> x e\<^sub>c e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Sync \<V> e\<^sub>0 \<pi> x x\<^sub>v e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Fst \<V> e\<^sub>0 \<pi> x p e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Snd \<V> e\<^sub>0 \<pi> x p e\<^sub>n)
    then show ?case using is_super_exp1 is_super_exp_trans by blast
  next
    case (Let_Case_Left \<V> e\<^sub>0 \<pi> x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    then show ?case using Refl is_super_exp.Let_Case_Left is_super_exp_trans by blast
  next
    case (Let_Case_Right \<V> e\<^sub>0 \<pi> x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    then show ?case using Refl is_super_exp.Let_Case_Right is_super_exp_trans by blast
  next
    case (Let_App \<V> e\<^sub>0 \<pi> x f x\<^sub>a e\<^sub>n f' x' e')
    then show ?case by (metis Let_Abs_Body Refl is_super_exp_trans val_to_bind.simps(3) value_to_abstract_value.simps(3))
  qed
  with `\<forall>x \<omega>. |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists>x e\<^sub>n. is_super_exp e\<^sub>0 (LET x = val_to_bind \<omega> in e\<^sub>n))`
  show "is_super_exp e\<^sub>0 e"
  by blast
qed
*)



end