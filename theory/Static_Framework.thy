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

datatype edge_label = ENext | ESpawn | ECall | EReturn

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


inductive is_super_exp_over_prim :: "exp \<Rightarrow> prim \<Rightarrow> bool" where
  Send_Evt: "
    is_super_exp_over_prim e0 (Send_Evt xC xM)
  " |
  Recv_Evt: "
    is_super_exp_over_prim e0 (Recv_Evt xC)
  " |
  Pair: "
    is_super_exp_over_prim e0 (Pair x1 x2)
  " |
  Left: "
    is_super_exp_over_prim e0 (Left x)
  " |
  Right: "
    is_super_exp_over_prim e0 (Right x)
  " |
  Abs: "
    is_super_exp_left e0 e\<^sub>b \<Longrightarrow>
    is_super_exp_over_prim e0 (Abs f\<^sub>p x\<^sub>p e\<^sub>b)
  " 

inductive 
  is_super_exp_over_env :: "exp \<Rightarrow> val_env \<Rightarrow> bool" and
  is_super_exp_over_val :: "exp \<Rightarrow> val \<Rightarrow> bool"
where
  VUnit: "
    is_super_exp_over_val e0 VUnit
  " |
  VChan: "
    is_super_exp_over_val e0 (VChan c)
  " |
  VClosure: "
    is_super_exp_over_prim e0 p \<Longrightarrow>
    is_super_exp_over_env e0 \<rho>' \<Longrightarrow>
    is_super_exp_over_val e0 (VClosure p \<rho>')
  " |

  Intro: "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow> is_super_exp_over_val e0 \<omega> \<Longrightarrow>
    is_super_exp_over_env e0 \<rho>
  "

inductive is_super_exp_over_stack :: "exp \<Rightarrow> cont list \<Rightarrow> bool" where
  Empty: "
    is_super_exp_over_stack e0 []
  " |
  Nonempty: "
    is_super_exp_left e0 e\<^sub>\<kappa> \<Longrightarrow>
    is_super_exp_over_env e0 \<rho>\<^sub>\<kappa> \<Longrightarrow>
    is_super_exp_over_stack e0 \<kappa> \<Longrightarrow>
    is_super_exp_over_stack e0 (\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)
  "

inductive is_super_exp_over_state :: "exp \<Rightarrow> state \<Rightarrow> bool" where
  Intro: "
    is_super_exp_left e0 e \<Longrightarrow>
    is_super_exp_over_env e0 \<rho> \<Longrightarrow>
    is_super_exp_over_stack e0 \<kappa> \<Longrightarrow>
    is_super_exp_over_state e0 (\<langle>e;\<rho>;\<kappa>\<rangle>)
  "

lemma is_super_exp_over_state_preserved: "
  (E, H) \<rightarrow> (E', H') \<Longrightarrow>
  \<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma> \<Longrightarrow>
  E' \<pi>' = Some \<sigma>' \<Longrightarrow>
  is_super_exp_over_state e\<^sub>0 \<sigma>'
"
proof -
  assume 
    H1: "\<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>" and
    H2: "E' \<pi>' = Some \<sigma>'" and
    H3: "(E, H) \<rightarrow> (E', H')"

  from H3 show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    from H1 local.Seq_Step_Down(4)
    have L1H1: "is_super_exp_over_state e\<^sub>0 (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" by blast

    then have 
      L1H2: "is_super_exp_over_env e\<^sub>0 \<rho>" and 
      L1H3: "is_super_exp_over_stack e\<^sub>0 (\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)" by (blast dest: is_super_exp_over_state.cases)+

    then have 
      L1H4: "is_super_exp_left e\<^sub>0 e\<^sub>\<kappa>" and 
      L1H5: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>\<kappa>" and 
      L1H6: "is_super_exp_over_stack e\<^sub>0 \<kappa>" by (blast dest: is_super_exp_over_stack.cases)+

    from L1H2 L1H5 local.Seq_Step_Down(5) have L1H7: "is_super_exp_over_env e\<^sub>0 (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>))"
      by (smt is_super_exp_over_env.cases is_super_exp_over_env_is_super_exp_over_val.Intro map_upd_Some_unfold)

    with L1H4 L1H6 L1H7 have L1H8: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>);\<kappa>\<rangle>)"
      by (simp add: is_super_exp_over_state.intros)

    with H1 H2 local.Seq_Step_Down(1) show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
      by (metis map_add_empty map_add_upd map_upd_Some_unfold)
  next
    case (Seq_Step \<pi> x b el \<rho>l \<kappa>l \<omega>)

    from H1 local.Seq_Step(4) 
    have L1H1: "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      L1H2: "is_super_exp_left e\<^sub>0 (LET x = b in el)" and
      L1H3: "is_super_exp_over_env e\<^sub>0 \<rho>l" and
      L1H4: "is_super_exp_over_stack e\<^sub>0 \<kappa>l" by (blast dest: is_super_exp_over_state.cases)+

    from L1H2 have L1H5: "is_super_exp_left e\<^sub>0 el" by (blast dest: is_super_exp_left.Let)

    from local.Seq_Step(5) have 
      "is_super_exp_over_val e\<^sub>0 \<omega>"
    proof cases
      case Let_Unit
      then show "is_super_exp_over_val e\<^sub>0 \<omega>" by (simp add: VUnit)
    next
      case (Let_Prim p)

      have L2H1: "is_super_exp_over_prim e\<^sub>0 p"
      proof (cases p)
        case (Send_Evt x11 x12)
        then show "is_super_exp_over_prim e\<^sub>0 p" by (simp add: is_super_exp_over_prim.Send_Evt)
      next
        case (Recv_Evt x2)
        then show "is_super_exp_over_prim e\<^sub>0 p" by (simp add: is_super_exp_over_prim.Recv_Evt)
      next
        case (Pair x31 x32)
        then show "is_super_exp_over_prim e\<^sub>0 p" by (simp add: is_super_exp_over_prim.Pair)
      next
        case (Left x4)
        then show "is_super_exp_over_prim e\<^sub>0 p" by (simp add: is_super_exp_over_prim.Left)
      next
        case (Right x5)
        then show "is_super_exp_over_prim e\<^sub>0 p" by (simp add: is_super_exp_over_prim.Right)
      next
        case (Abs x61 x62 x63)

        with L1H2 local.Let_Prim(1) local.Abs
        show "is_super_exp_over_prim e\<^sub>0 p" by (smt is_super_exp_left.Let_Abs_Body is_super_exp_over_prim.Abs )
      qed

      have L2H3: "is_super_exp_over_env e\<^sub>0 \<rho>l" by (simp add: L1H3)

      with L2H1 have "is_super_exp_over_val e\<^sub>0 (VClosure p \<rho>l)" by (simp add: VClosure)

      with local.Let_Prim(2) show "is_super_exp_over_val e\<^sub>0 \<omega>" by simp
    next
      case (Let_Fst x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)
      then show "is_super_exp_over_val e\<^sub>0 \<omega>"
        by (metis L1H3 is_super_exp_over_env.cases is_super_exp_over_val.cases val.distinct(3) val.distinct(5) val.inject(2))
    next
      case (Let_Snd x\<^sub>p x\<^sub>1 x\<^sub>2 \<rho>\<^sub>p)
      then show "is_super_exp_over_val e\<^sub>0 \<omega>"
        by (metis L1H3 is_super_exp_over_env.cases is_super_exp_over_val.cases val.distinct(3) val.distinct(5) val.inject(2))
    qed
    
    with L1H3 have L1H6: "is_super_exp_over_env e\<^sub>0 (\<rho>l(x \<mapsto> \<omega>))"
      by (smt is_super_exp_over_env.cases is_super_exp_over_env_is_super_exp_over_val.Intro map_upd_Some_unfold)

    with L1H4 L1H5 have L1H7: "is_super_exp_over_state e\<^sub>0 (\<langle>el;\<rho>l(x \<mapsto> \<omega>);\<kappa>l\<rangle>)" by (simp add: is_super_exp_over_state.intros)
   
    with H1 H2 local.Seq_Step(1) show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
      by (metis map_add_empty map_add_upd map_upd_Some_unfold)
  next
    case (Seq_Step_Up \<pi> x b el \<rho>l \<kappa>l el' \<rho>l')

    from H1 local.Seq_Step_Up(4) have 
      L1H1: "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      L1H2: "is_super_exp_left e\<^sub>0 (LET x = b in el)" and
      L1H3: "is_super_exp_over_env e\<^sub>0 \<rho>l" and
      L1H4: "is_super_exp_over_stack e\<^sub>0 \<kappa>l" by (blast dest: is_super_exp_over_state.cases)+

    from L1H2 have 
      L1H5: "is_super_exp_left e\<^sub>0 el" by (blast dest: is_super_exp_left.Let)

    from L1H3 L1H4 L1H5 have 
      L1H6: "is_super_exp_over_stack e\<^sub>0 (\<langle>x,el,\<rho>l\<rangle> # \<kappa>l)" 
        by (simp add: is_super_exp_over_stack.Nonempty)

    from local.Seq_Step_Up(5)
    have 
      L1H7: "is_super_exp_left e\<^sub>0 el' \<and> is_super_exp_over_env e\<^sub>0 \<rho>l'"
    proof cases
      case (Let_Case_Left x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)

      from L1H2 local.Let_Case_Left(1) have 
        L2H1: "is_super_exp_left e\<^sub>0 el'" by (blast dest: is_super_exp_left.Let_Case_Left)

      from L1H3 local.Let_Case_Left(3) have 
        "is_super_exp_over_val e\<^sub>0 (VClosure (prim.Left x\<^sub>l') \<rho>\<^sub>l)"
        by (blast dest: is_super_exp_over_env.cases)

      then have "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>l" by (blast dest: is_super_exp_over_val.cases)

      with local.Let_Case_Left(4) have "is_super_exp_over_val e\<^sub>0 \<omega>\<^sub>l" by (blast dest: is_super_exp_over_env.cases)

      with L1H3 have "is_super_exp_over_env e\<^sub>0 (\<rho>l(x\<^sub>l \<mapsto> \<omega>\<^sub>l))"
        by (smt is_super_exp_over_env.cases is_super_exp_over_env_is_super_exp_over_val.Intro map_upd_Some_unfold)

      with local.Let_Case_Left(2) have 
        L2H2: "is_super_exp_over_env e\<^sub>0 \<rho>l'" by simp

      with L2H1 show "is_super_exp_left e\<^sub>0 el' \<and> is_super_exp_over_env e\<^sub>0 \<rho>l'" by simp
    next
      case (Let_Case_Right x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)

      from L1H2 local.Let_Case_Right(1) have 
        L2H1: "is_super_exp_left e\<^sub>0 el'"
          by (blast dest: is_super_exp_left.Let_Case_Right)

      from L1H3 local.Let_Case_Right(3)
      have "is_super_exp_over_val e\<^sub>0 (VClosure (prim.Right x\<^sub>r') \<rho>\<^sub>r)"
        by (blast dest: is_super_exp_over_env.cases)

      then have "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>r" by (blast dest: is_super_exp_over_val.cases)

      with L1H3 local.Let_Case_Right(2) local.Let_Case_Right(4) have 
        L2H2: "is_super_exp_over_env e\<^sub>0 \<rho>l'"
          by (auto simp: is_super_exp_over_env.simps)

      with L2H1 show "is_super_exp_left e\<^sub>0 el' \<and> is_super_exp_over_env e\<^sub>0 \<rho>l'" by simp
    next
      case (Let_App f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a)

      from L1H3 local.Let_App(3) have
        L2H1: "is_super_exp_over_val e\<^sub>0 (VClosure (Abs f\<^sub>l x\<^sub>l el') \<rho>\<^sub>l)" by (blast dest: is_super_exp_over_env.cases)

      then have 
        "is_super_exp_over_prim e\<^sub>0 (Abs f\<^sub>l x\<^sub>l el')" by (blast dest: is_super_exp_over_val.cases)

      then have L2H2: "is_super_exp_left e\<^sub>0 el'" by (blast dest: is_super_exp_over_prim.cases)

      from L2H1 have L2H3: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>l" by (blast dest: is_super_exp_over_val.cases)

      with L1H3 local.Let_App(4) have
        L2H1: "is_super_exp_over_val e\<^sub>0 \<omega>\<^sub>a" by (blast dest: is_super_exp_over_env.cases)

      with L1H3 L2H3 local.Let_App(2) local.Let_App(3) have 
        L2H4: "is_super_exp_over_env e\<^sub>0 \<rho>l'" by (auto simp: is_super_exp_over_env.simps)

       with L2H2 show "is_super_exp_left e\<^sub>0 el' \<and> is_super_exp_over_env e\<^sub>0 \<rho>l'" by simp
    qed

    with L1H6 have "is_super_exp_over_state e\<^sub>0 (\<langle>el';\<rho>l';\<langle>x,el,\<rho>l\<rangle> # \<kappa>l\<rangle>)" by (simp add: is_super_exp_over_state.intros)

    with H1 H2 local.Seq_Step_Up(1) show 
      "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (metis fun_upd_other fun_upd_same map_add_empty map_add_upd option.sel)
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)

    from H1 local.Let_Chan(4) have 
      "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)" by simp

    then have
      L1H1: "is_super_exp_left e\<^sub>0 (LET x = CHAN \<lparr>\<rparr> in e)" and
      L1H2: "is_super_exp_over_env e\<^sub>0 \<rho>" and
      L1H3: "is_super_exp_over_stack e\<^sub>0 \<kappa>" using is_super_exp_over_state.cases by blast+

    from L1H1 have
      L1H4: "is_super_exp_left e\<^sub>0 e" using is_super_exp_left.Let by blast

    from L1H2 have
      L1H5: "is_super_exp_over_env e\<^sub>0 (\<rho>(x \<mapsto> VChan (Ch \<pi> x)))" using VChan is_super_exp_over_env.simps by auto

    from L1H4 L1H5 L1H3 have
      "is_super_exp_over_state e\<^sub>0 (\<langle>e;\<rho> ++ [x \<mapsto> VChan (Ch \<pi> x)];\<kappa>\<rangle>)" using is_super_exp_over_state.intros by simp

    with H1 H2 local.Let_Chan(1) show
      "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (metis fun_upd_other fun_upd_same map_add_empty map_add_upd option.sel)
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)

    from H1 local.Let_Spawn(4) have
      "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)" by blast

    then have
      L1H1: "is_super_exp_left e\<^sub>0 (LET x = SPAWN e\<^sub>c in e)" and
      L1H2: "is_super_exp_over_env e\<^sub>0 \<rho>" and
      L1H3: "is_super_exp_over_stack e\<^sub>0 \<kappa>" using is_super_exp_over_state.cases by blast+

    from L1H1 have
      L1H4: "is_super_exp_left e\<^sub>0 e\<^sub>c" using is_super_exp_left.Let_Spawn_Child by blast

    from L1H1 have
      L1H5: "is_super_exp_left e\<^sub>0 e" using is_super_exp_left.Let by blast

    from L1H2 L1H4 have
      L1H6: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>c;\<rho>;[]\<rangle>)" by (simp add: is_super_exp_over_stack.Empty is_super_exp_over_state.intros)

    have
      L1H7: "is_super_exp_over_val e\<^sub>0 VUnit" by (simp add: VUnit)

    from L1H2 L1H3 L1H5 L1H7 have
      L1H8: "is_super_exp_over_state e\<^sub>0 (\<langle>e;\<rho>(x \<mapsto> VUnit);\<kappa>\<rangle>)" by (simp add:is_super_exp_over_env.simps is_super_exp_over_state.intros)
   
    from H1 H2 L1H6 L1H8 local.Let_Spawn(1) show
      "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (smt fun_upd_apply map_add_empty map_add_upd option.sel)

  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    from H1 local.Let_Sync(7) have 
      "is_super_exp_over_state e\<^sub>0 (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r;\<rho>\<^sub>r;\<kappa>\<^sub>r\<rangle>)" by blast

    then have 
      L1H1: "is_super_exp_left e\<^sub>0 (LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r)" and
      L1H2: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>r" and
      L1H3: "is_super_exp_over_stack e\<^sub>0 \<kappa>\<^sub>r" using is_super_exp_over_state.cases by blast+

    have 
      L1H4: "is_super_exp_left e\<^sub>0 e\<^sub>r"
      using L1H1 is_super_exp_left.Let by blast

    from H1 local.Let_Sync(4) have 
      "is_super_exp_over_state e\<^sub>0 (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)" by blast

    then have 
      L1H5: "is_super_exp_left e\<^sub>0 (LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s)" and
      L1H6: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>s" and
      L1H7: "is_super_exp_over_stack e\<^sub>0 \<kappa>\<^sub>s" using is_super_exp_over_state.cases by blast+

    from L1H6 local.Let_Sync(5) have 
      L1H8: "is_super_exp_over_val e\<^sub>0 (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e)" using is_super_exp_over_env.cases by auto

    then have 
      L1H9: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>s\<^sub>e"  using is_super_exp_over_val.cases by blast

    from L1H9 local.Let_Sync(11) have 
      L1H10: "is_super_exp_over_val e\<^sub>0 \<omega>\<^sub>m" using is_super_exp_over_env.cases by auto

    from L1H5 have 
      L1H11: "is_super_exp_left e\<^sub>0 e\<^sub>s" using is_super_exp_left.Let by blast

    have 
      L1H12: "is_super_exp_over_val e\<^sub>0 VUnit" by (simp add: VUnit)

    from L1H2 L1H3 L1H4 L1H10 L1H12 have 
      L1H13: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>r;\<rho>\<^sub>r(x\<^sub>r \<mapsto> \<omega>\<^sub>m);\<kappa>\<^sub>r\<rangle>)" by (simp add: is_super_exp_over_env.simps is_super_exp_over_state.intros)

    from L1H6 L1H7 L1H11 L1H12 have 
      L1H14: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>s;\<rho>\<^sub>s(x\<^sub>s \<mapsto> VUnit);\<kappa>\<^sub>s\<rangle>)" by (simp add: is_super_exp_over_env.simps is_super_exp_over_state.intros)

    from H1 H2 L1H13 L1H14 local.Let_Sync(1) show 
      "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (smt fun_upd_apply map_add_empty map_add_upd option.sel)

  qed
qed

lemma isnt_exp_sound_generalized: "
  (\<E>0, H0) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<Longrightarrow>
  \<E>' \<pi>' = Some \<sigma>' \<Longrightarrow>
  is_super_exp_over_state e\<^sub>0 \<sigma>'
"
proof -
  assume 
    H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and 
    H2: "\<E>' \<pi>' = Some \<sigma>'" and
    H3: "(\<E>0, H0) \<rightarrow>* (\<E>', H')"

  obtain X0 X' where
    H4: "X0 = (\<E>0, H0)" and 
    H5: "X' = (\<E>', H')" by simp

  from H3 H4 H5 have 
    H6: "star_left (op \<rightarrow>) X0 X'" by (simp add: star_implies_star_left)

  then have 
    H7: "
      \<forall> \<E>0 H0 \<E>' H' \<pi>' \<sigma>' .
      X0 = (\<E>0, H0) \<longrightarrow> X' = (\<E>', H') \<longrightarrow>
      \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
      \<E>' \<pi>' = Some \<sigma>' \<longrightarrow>
      is_super_exp_over_state e\<^sub>0 \<sigma>'
    " 
  proof (induction)
    case (refl z)

    {
      fix \<E>0 H0 \<E>' H' \<pi>' \<sigma>'
      assume 
        L1H0: "z = (\<E>0, H0)" "z = (\<E>', H')" and
        L1H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
        L1H2:  "\<E>0 \<pi>' = Some \<sigma>'"
  
      have 
        L1H3: "is_super_exp_left e\<^sub>0 e\<^sub>0" by (simp add: is_super_exp_left.Refl)
      have 
        L1H4: "is_super_exp_over_env e\<^sub>0 Map.empty" by (simp add: is_super_exp_over_env_is_super_exp_over_val.Intro)
      have 
        L1H5: "is_super_exp_over_stack e\<^sub>0 []" by (simp add: is_super_exp_over_stack.Empty)

      from L1H3 L1H4 L1H5 have 
        L1H6: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>0;Map.empty;[]\<rangle>)" by (simp add: is_super_exp_over_state.intros)

     from L1H1 L1H2 L1H6 have
        "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (metis fun_upd_apply option.distinct(1) option.sel)
    }

    then show ?case by blast
  next
    case (step x y z)
    {
      fix \<E>0 H0 \<E>' H' \<pi>' \<sigma>'
      assume 
        L1H0: "x = (\<E>0, H0)" "z = (\<E>', H')" and 
        L2H1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
        L2H2: "\<E>' \<pi>' = Some \<sigma>'"


      obtain \<E> H where L2H3: "y = (\<E>, H)" by (meson surj_pair)
      from L1H0(1) L2H1 L2H3 step.IH have 
        L2H4: "\<forall>\<pi> \<sigma>. \<E> \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>" by blast

      from L1H0(2) L2H2 L2H3 L2H4 step.hyps(2) have 
        "is_super_exp_over_state e\<^sub>0 \<sigma>'" using is_super_exp_over_state_preserved by blast

    } 

    then show ?case by blast
  qed

  from H1 H2 H4 H5 H7 show 
    "is_super_exp_over_state e\<^sub>0 \<sigma>'" by blast
qed

lemma isnt_exp_sound: "
  ([[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e'
" 
using is_super_exp_left_implies_is_super_exp is_super_exp_over_state.simps isnt_exp_sound_generalized by fastforce



end