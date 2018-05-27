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
    is_super_exp_left e0 e\<^sub>b \<Longrightarrow>
    is_super_exp_over_prim e0 p \<Longrightarrow>
    is_super_exp_over_env e0 \<rho>' \<Longrightarrow>
    is_super_exp_over_val e0 (VClosure p \<rho>')
  " |

  Intro: "
    \<forall> f \<omega> . \<rho> f = Some \<omega> \<longrightarrow> is_super_exp_over_val e0 \<omega> \<Longrightarrow>
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
    H2: "E' \<pi>' = Some \<sigma>'"

  assume "E \<rightarrow> E'"

  then show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<omega>)

    assume 
      H3: "E' = E ++ [\<pi> ;; LReturn x\<^sub>\<kappa> \<mapsto> \<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" and
      H6: "\<rho> x = Some \<omega>" 

    from H1 H5 have H7: "is_super_exp_over_state e\<^sub>0 (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" by blast

    then have 
      H8: "is_super_exp_over_env e\<^sub>0 \<rho>" and 
      H9: "is_super_exp_over_stack e\<^sub>0 (\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)" by (blast dest: is_super_exp_over_state.cases)+

    then have 
      H10: "is_super_exp_left e\<^sub>0 e\<^sub>\<kappa>" and 
      H11: "is_super_exp_over_env e\<^sub>0 \<rho>\<^sub>\<kappa>" and 
      H12: "is_super_exp_over_stack e\<^sub>0 \<kappa>" by (blast dest: is_super_exp_over_stack.cases)+

    {
      fix f f\<^sub>p x\<^sub>p e\<^sub>b \<rho>'
      assume H13: "(\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>)) f = Some (VClosure (Abs f\<^sub>p x\<^sub>p e\<^sub>b) \<rho>')"

      have "is_super_exp_left e\<^sub>0 e\<^sub>b" 
      proof cases
        assume "f = x\<^sub>\<kappa>"

        with H13 have "\<omega> = (VClosure (Abs f\<^sub>p x\<^sub>p e\<^sub>b) \<rho>')" by simp

        with H6 have "\<rho> x = Some (VClosure (Abs f\<^sub>p x\<^sub>p e\<^sub>b) \<rho>')" by simp

        with H8 show "is_super_exp_left e\<^sub>0 e\<^sub>b"
          by (metis is_super_exp_over_env.cases is_super_exp_over_prim.cases is_super_exp_over_val.cases prim.distinct(17) prim.distinct(23) prim.distinct(27) prim.distinct(29) prim.distinct(9) prim.inject(6) val.distinct(3) val.distinct(5) val.inject(2))
      next
        assume "f \<noteq> x\<^sub>\<kappa>"

        with H13 have "\<rho>\<^sub>\<kappa> f = Some (VClosure (Abs f\<^sub>p x\<^sub>p e\<^sub>b) \<rho>')" by simp

        with H11 show "is_super_exp_left e\<^sub>0 e\<^sub>b"
          by (metis is_super_exp_over_env.cases is_super_exp_over_prim.cases is_super_exp_over_val.cases prim.distinct(17) prim.distinct(23) prim.distinct(27) prim.distinct(29) prim.distinct(9) prim.inject(6) val.distinct(3) val.distinct(5) val.inject(2))
      qed
    }

    then have H13: "is_super_exp_over_env e\<^sub>0 (\<rho>\<^sub>\<kappa>(x\<^sub>\<kappa> \<mapsto> \<omega>))"
      using H11 H6 H8 is_super_exp_over_env.simps by auto

    with H10 H12 have H14: "is_super_exp_over_state e\<^sub>0 (\<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>)" by (simp add: is_super_exp_over_state.intros)

    show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
    proof cases
      assume H8: "\<pi>' = \<pi> ;; LReturn x\<^sub>\<kappa>"
      
      with H3 have "E' \<pi>' = Some (\<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>)" by simp

      with H2
      have "\<sigma>' = (\<langle>e\<^sub>\<kappa>;\<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>];\<kappa>\<rangle>)" by simp

      with H14
      show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by simp
    next
      assume H8: "\<pi>' \<noteq> \<pi> ;; LReturn x\<^sub>\<kappa>"

      with H3 have "E' \<pi>' = E \<pi>'" by simp

      with H2 have "E \<pi>' = Some \<sigma>'" by simp
  
      with H1 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Seq_Step \<pi> x b el \<rho>l \<kappa>l \<omega>)
    assume 
      H3: "E' = E ++ [\<pi> ;; LNext x \<mapsto> \<langle>el;\<rho>l(x \<mapsto> \<omega>);\<kappa>l\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" and
      H6: "seq_step (b, \<rho>l) \<omega>"

    from H1 H5 have H7: "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      H8: "is_super_exp_left e\<^sub>0 (LET x = b in el)" and
      H9: "is_super_exp_over_env e\<^sub>0 \<rho>l" and
      H10: "is_super_exp_over_stack e\<^sub>0 \<kappa>l" by (blast dest: is_super_exp_over_state.cases)+

    from H8 have H11: "is_super_exp_left e\<^sub>0 el" by (blast dest: is_super_exp_left.Let)


    with H10 H11 have H12: "is_super_exp_over_state e\<^sub>0 (\<langle>el;\<rho>l(x \<mapsto> \<omega>);\<kappa>l\<rangle>)" sorry

    show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
    proof cases
      assume H8: "\<pi>' = \<pi> ;; LNext x"
      
      with H3 have "E' \<pi>' = Some (\<langle>el;\<rho>l(x \<mapsto> \<omega>);\<kappa>l\<rangle>)" by simp

      with H2 have "\<sigma>' = (\<langle>el;\<rho>l(x \<mapsto> \<omega>);\<kappa>l\<rangle>)" by simp

      with H12 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by simp
    next
      assume H8: "\<pi>' \<noteq> \<pi> ;; LNext x"

      with H3 have "E' \<pi>' = E \<pi>'" by simp

      with H2 have "E \<pi>' = Some \<sigma>'" by simp
  
      with H1 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Seq_Step_Up \<pi> x b el \<rho>l \<kappa>l el' \<rho>l')

    assume 
      H3: "E' = E ++ [\<pi> ;; LCall x \<mapsto> \<langle>el';\<rho>l';\<langle>x,el,\<rho>l\<rangle> # \<kappa>l\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" and
      H6: "seq_step_up (b, \<rho>l) (el', \<rho>l')"

    from H1 H5 have H7: "is_super_exp_over_state e\<^sub>0 (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" by blast

    then have 
      H8: "is_super_exp_left e\<^sub>0 (LET x = b in el)" and
      H9: "is_super_exp_over_stack e\<^sub>0 \<kappa>l" by (blast dest: is_super_exp_over_state.cases)+

    from H8 have H10: "is_super_exp_left e\<^sub>0 el" by (blast dest: is_super_exp_left.Let)

    from H9 H10 have H11: "is_super_exp_over_stack e\<^sub>0 (\<langle>x,el,\<rho>l\<rangle> # \<kappa>l)"
      using H7 is_super_exp_over_stack.Nonempty is_super_exp_over_state.cases by blast

    from H6 have H12: "is_super_exp_left e\<^sub>0 el'" 
    proof cases
      case (Let_Case_Left x\<^sub>s x\<^sub>l' \<rho>\<^sub>l \<omega>\<^sub>l x\<^sub>l x\<^sub>r e\<^sub>r)
      show ?thesis using H8 is_super_exp_left.Let_Case_Left local.Let_Case_Left(1) by blast
    next
      case (Let_Case_Right x\<^sub>s x\<^sub>r' \<rho>\<^sub>r \<omega>\<^sub>r x\<^sub>l e\<^sub>l x\<^sub>r)
      show ?thesis using H8 is_super_exp_left.Let_Case_Right local.Let_Case_Right(1) by blast
    next
      case (Let_App f f\<^sub>l x\<^sub>l \<rho>\<^sub>l x\<^sub>a \<omega>\<^sub>a)
    
      assume 
        H12: "b = APP f x\<^sub>a" and
        H13: "\<rho>l' = \<rho>\<^sub>l(f\<^sub>l \<mapsto> VClosure (Abs f\<^sub>l x\<^sub>l el') \<rho>\<^sub>l, x\<^sub>l \<mapsto> \<omega>\<^sub>a)" and
        H14: "\<rho>l f = Some (VClosure (Abs f\<^sub>l x\<^sub>l el') \<rho>\<^sub>l)" and
        H15: "\<rho>l x\<^sub>a = Some \<omega>\<^sub>a"


      show "is_super_exp_left e\<^sub>0 el'" sorry
    qed

    with H11 have "is_super_exp_over_state e\<^sub>0 (\<langle>el';\<rho>l';\<langle>x,el,\<rho>l\<rangle> # \<kappa>l\<rangle>)" sorry

    show "is_super_exp_over_state e\<^sub>0 \<sigma>'"
    proof cases
      assume HX: "\<pi>' = \<pi> ;; LCall x"
      show "is_super_exp_over_state e\<^sub>0 \<sigma>'" sorry
    next
      assume HX: "\<pi>' \<noteq> \<pi> ;; LCall x"

      with H3 have "E' \<pi>' = E \<pi>'" by simp

      with H2 have "E \<pi>' = Some \<sigma>'" by simp
  
      with H1 show "is_super_exp_over_state e\<^sub>0 \<sigma>'" by (blast dest: is_super_exp_over_state.cases)
    qed
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

lemma is_super_exp_preserved: "
  E \<rightarrow> E' \<Longrightarrow>
  \<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma> \<Longrightarrow>
  E' \<pi>' = Some \<sigma>' \<Longrightarrow>
  is_super_exp_over_state e\<^sub>0 \<sigma>'
"
sorry

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
