theory Sound_Framework
  imports Main Syntax Dynamic_Semantics Static_Semantics
      Static_Framework
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin


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
  E \<rightarrow> E' \<Longrightarrow>
  \<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma> \<Longrightarrow>
  E' \<pi>' = Some \<sigma>' \<Longrightarrow>
  is_super_exp_over_state e\<^sub>0 \<sigma>'
"
proof -
  assume 
    H1: "\<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>" and
    H2: "E' \<pi>' = Some \<sigma>'" and
    H3: "E \<rightarrow> E'"

  from H3 show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    from H1 local.Seq_Step_Down(3)
    have L1H1: "is_super_exp_over_state e\<^sub>0 (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" by simp

    then have 
      L1H2: "is_super_exp_over_env e\<^sub>0 \<rho>" and 
      L1H3: "is_super_exp_over_stack e\<^sub>0 (\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)" by (blast dest: is_super_exp_over_state.cases)+

    then have 
      L1H4: "is_super_exp_left e\<^sub>0 e\<^sub>\<kappa>" and 
      L1H5: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>\<kappa>" and 
      L1H6: "is_super_exp_over_stack e\<^sub>0 \<kappa>" by (blast dest: is_super_exp_over_stack.cases)+

    from L1H2 L1H5 local.Seq_Step_Down(4) have L1H7: "is_super_exp_over_env e\<^sub>0 (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>))"
      by (smt is_super_exp_over_env.cases is_super_exp_over_env_is_super_exp_over_val.Intro map_upd_Some_unfold)

    with L1H4 L1H6 L1H7 have L1H8: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>);\<kappa>\<rangle>)"
      by (simp add: is_super_exp_over_state.intros)

    with H1 H2 local.Seq_Step_Down(1) show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
      by (metis map_add_empty map_add_upd map_upd_Some_unfold)
  next
    case (Seq_Step \<pi> x b el \<rho>l \<kappa>l \<omega>)

    from H1 local.Seq_Step(3) 
    have L1H1: "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      L1H2: "is_super_exp_left e\<^sub>0 (LET x = b in el)" and
      L1H3: "is_super_exp_over_env e\<^sub>0 \<rho>l" and
      L1H4: "is_super_exp_over_stack e\<^sub>0 \<kappa>l" by (blast dest: is_super_exp_over_state.cases)+

    from L1H2 have L1H5: "is_super_exp_left e\<^sub>0 el" by (blast dest: is_super_exp_left.Let)

    from local.Seq_Step(4) 
    have "is_super_exp_over_val e\<^sub>0 \<omega>"
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

    from H1 local.Seq_Step_Up(3) have L1H1: "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      L1H2: "is_super_exp_left e\<^sub>0 (LET x = b in el)" and
      L1H3: "is_super_exp_over_env e\<^sub>0 \<rho>l" and
      L1H4: "is_super_exp_over_stack e\<^sub>0 \<kappa>l" by (blast dest: is_super_exp_over_state.cases)+

    from L1H2 have L1H5: "is_super_exp_left e\<^sub>0 el"
      using is_super_exp_left.Let by blast

    from L1H3 L1H4 L1H5 have L1H6: "is_super_exp_over_stack e\<^sub>0 (\<langle>x,el,\<rho>l\<rangle> # \<kappa>l)" 
      by (simp add: is_super_exp_over_stack.Nonempty)

    from local.Seq_Step_Up(4)
    have 
      L1H7: "is_super_exp_left e\<^sub>0 el' \<and> is_super_exp_over_env e\<^sub>0 \<rho>l'"
    proof cases
      case (Let_Case_Left x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)

      from L1H2 local.Let_Case_Left(1) 
      have L2H1: "is_super_exp_left e\<^sub>0 el'" by (blast dest: is_super_exp_left.Let_Case_Left)

      with L1H3 local.Let_Case_Left(3) local.Let_Case_Left(4) have "is_super_exp_over_val e\<^sub>0 \<omega>\<^sub>l"
        by (metis is_super_exp_over_env.cases is_super_exp_over_val.cases val.distinct(3) val.distinct(5) val.inject(2))

      with L1H3 have "is_super_exp_over_env e\<^sub>0 (\<rho>l(x\<^sub>l \<mapsto> \<omega>\<^sub>l))"
        by (smt is_super_exp_over_env.cases is_super_exp_over_env_is_super_exp_over_val.Intro map_upd_Some_unfold)

      with local.Let_Case_Left(2) 
      have L2H2: "is_super_exp_over_env e\<^sub>0 \<rho>l'" by simp

      with L2H1 show "is_super_exp_left e\<^sub>0 el' \<and> is_super_exp_over_env e\<^sub>0 \<rho>l'" by simp
    next
      case (Let_Case_Right x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)
      then show ?thesis sorry
    next
      case (Let_App f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a)
      then show ?thesis sorry
    qed

    with L1H6 have "is_super_exp_over_state e\<^sub>0 (\<langle>el';\<rho>l';\<langle>x,el,\<rho>l\<rangle> # \<kappa>l\<rangle>)" by (simp add: is_super_exp_over_state.intros)

    with H1 H2 local.Seq_Step_Up(1)  show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (metis fun_upd_other fun_upd_same map_add_empty map_add_upd option.sel)
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)
    assume
      H3: "E' = E ++ [\<pi> ;; LNext x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VChan (Ch \<pi> x)];\<kappa>\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)"

    show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
    proof cases
      assume HX: "\<pi>' = \<pi> ;; LNext x"
      show "is_super_exp_over_state e\<^sub>0 \<sigma>'" sorry
    next
      assume HX: "\<pi>' \<noteq> \<pi> ;; LNext x"

      with H3 have "E' \<pi>' = E \<pi>'" by simp

      with H2 have "E \<pi>' = Some \<sigma>'" by simp
  
      with H1 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    assume
      H3: "E' = E ++ [\<pi> ;; LNext x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; LSpawn x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)"

    show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
    proof cases
      assume HX: "\<pi>' = \<pi> ;; LSpawn x"
      show "is_super_exp_over_state e\<^sub>0 \<sigma>'" sorry
    next
      assume HX: "\<pi>' \<noteq> \<pi> ;; LSpawn x"

      show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
      proof cases
        assume HXX: "\<pi>' = \<pi> ;; LNext x"
        show "is_super_exp_over_state e\<^sub>0 \<sigma>'" sorry
      next
        assume HXX: "\<pi>' \<noteq> \<pi> ;; LNext x"
  
        with HX H3 have "E' \<pi>' = E \<pi>'" by simp
  
        with H2 have "E \<pi>' = Some \<sigma>'" by simp
    
        with H1 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_over_state.cases)
      qed
    qed
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    assume 
      H3: "E' = E ++ [\<pi>\<^sub>s ;; LNext x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; LNext x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]" and
      H4: "leaf E \<pi>\<^sub>s" and
      H5: "E \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"

    show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
    proof cases
      assume HX: "\<pi>' = \<pi>\<^sub>r ;; LNext x\<^sub>r"
      show "is_super_exp_over_state e\<^sub>0 \<sigma>'" sorry
    next
      assume HX: "\<pi>' \<noteq> \<pi>\<^sub>r ;; LNext x\<^sub>r"

      show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
      proof cases
        assume HXX: "\<pi>' = \<pi>\<^sub>s ;; LNext x\<^sub>s"
        show "is_super_exp_over_state e\<^sub>0 \<sigma>'" sorry
      next
        assume HXX: "\<pi>' \<noteq> \<pi>\<^sub>s ;; LNext x\<^sub>s"
  
        with HX H3 have "E' \<pi>' = E \<pi>'" by simp
  
        with H2 have "E \<pi>' = Some \<sigma>'" by simp
    
        with H1 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_over_state.cases)
      qed
    qed
  qed
qed

lemma isnt_exp_sound_generalized: "
  \<E>0 \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<Longrightarrow>
  \<E>' \<pi>' = Some \<sigma>' \<Longrightarrow>
  is_super_exp_over_state e\<^sub>0 \<sigma>'
"
proof -

  assume P1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and P2: "\<E>' \<pi>' = Some \<sigma>'"

  assume "\<E>0 \<rightarrow>* \<E>'" then

  have "star_left (op \<rightarrow>) \<E>0 \<E>'" by (simp add: star_implies_star_left) then

  have "
    \<forall> \<pi>' \<sigma>' .
    \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E>' \<pi>' = Some \<sigma>' \<longrightarrow>
    is_super_exp_over_state e\<^sub>0 \<sigma>'
  " proof (induction)
    case (refl x)
    show ?case sorry
  next
    case (step E0 E E')
    assume "star_left op \<rightarrow> E0 E"
    assume "E \<rightarrow> E'"
    assume IH: "\<forall>\<pi>' \<sigma>'. E0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow> E \<pi>' = Some \<sigma>' \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>'"
    {
      fix \<pi>' \<sigma>'
      assume 
        P1: "E0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
        P2: "E' \<pi>' = Some \<sigma>'" 

      from IH and P1

      have IH2: "\<forall>\<pi>' \<sigma>'. E \<pi>' = Some \<sigma>' \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>'"  by blast
      with P2 \<open>E \<rightarrow> E'\<close>

      have "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_preserved) then

      have "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (simp add: is_super_exp_left_implies_is_super_exp)
    } then
    show ?case by blast
  qed
  with P1 and P2

  show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by blast
qed

lemma isnt_exp_sound: "
  [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e'
"
by (metis is_super_exp_left_implies_is_super_exp is_super_exp_over_state.cases isnt_exp_sound_generalized state.inject)


end
