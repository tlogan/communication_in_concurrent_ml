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

datatype edge_label = ENext | ESpawn (* | ESend var | ECall var | EReturn var *)

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

inductive is_super_exp_left :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  Refl : "
    is_super_exp_left e0 e0
  " | 
  Let_Spawn_Child: "
    is_super_exp_left e0 (LET x = SPAWN e\<^sub>c in e\<^sub>n)\<Longrightarrow>
    is_super_exp_left e0 e\<^sub>c
  " |
  Let_Case_Left: "
    is_super_exp_left e0 (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) \<Longrightarrow>
    is_super_exp_left e0 e\<^sub>l
  " |
  Let_Case_Right: "
    is_super_exp_left e0 (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n) \<Longrightarrow>
    is_super_exp_left e0 e\<^sub>r
  " |
  Let_Abs_Body: "
    is_super_exp_left e0 (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n) \<Longrightarrow>
    is_super_exp_left e0 e\<^sub>b
  " | 
  Let: "
    is_super_exp_left e0 (LET x = b in e\<^sub>n) \<Longrightarrow>
    is_super_exp_left e0 e\<^sub>n
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
by (simp add: is_super_exp.Let is_super_exp.Refl)

lemma is_super_exp_left_implies_is_super_exp: "
  is_super_exp_left e e' \<Longrightarrow> is_super_exp e e'
"
proof -
  assume "is_super_exp_left e e'"
  
  then show "is_super_exp e e'"
  proof induction
    case (Refl e0)
    show 
      "is_super_exp e0 e0" by (simp add: is_super_exp.Refl)
  next
    case (Let_Spawn_Child e0 x e\<^sub>c e\<^sub>n)
    from Let_Spawn_Child.IH show 
      "is_super_exp e0 e\<^sub>c"
    using is_super_exp.Let_Spawn_Child is_super_exp.Refl is_super_exp_trans by blast
  next
    case (Let_Case_Left e0 x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    from Let_Case_Left.IH show
      "is_super_exp e0 e\<^sub>l"
    using is_super_exp.Let_Case_Left is_super_exp.Refl is_super_exp_trans by blast
  next
    case (Let_Case_Right e0 x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    from Let_Case_Right.IH show 
      "is_super_exp e0 e\<^sub>r"
    using is_super_exp.Let_Case_Right is_super_exp.Refl is_super_exp_trans by blast
  next
    case (Let_Abs_Body e0 x f x\<^sub>p e\<^sub>b e\<^sub>n)
    from Let_Abs_Body.IH show 
      "is_super_exp e0 e\<^sub>b"
    using is_super_exp.Let_Abs_Body is_super_exp.Refl is_super_exp_trans by blast
  next
    case (Let e0 x b e\<^sub>n)
    from Let.IH show
      "is_super_exp e0 e\<^sub>n"
    using is_super_exp1 is_super_exp_trans by blast
  qed
qed


end