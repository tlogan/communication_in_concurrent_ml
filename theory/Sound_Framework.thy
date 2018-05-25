theory Sound_Framework
  imports Main Syntax Dynamic_Semantics Static_Semantics
      Static_Framework
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

inductive is_super_exp_over_stack :: "exp \<Rightarrow> cont list \<Rightarrow> bool" where
  Empty: "
    is_super_exp_over_stack e0 []
  " |
  Nonempty: "
    is_super_exp_left e0 e\<^sub>\<kappa> \<Longrightarrow>
    (* is_super_exp_over_stack e0 \<kappa> \<Longrightarrow> *)
    is_super_exp_over_stack e0 (\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)
  "

inductive is_super_exp_over_state :: "exp \<Rightarrow> state \<Rightarrow> bool" where
  "
    is_super_exp_left e0 e \<Longrightarrow>
    is_super_exp_over_stack e0 \<kappa> \<Longrightarrow>
    is_super_exp_over_state e0 (\<langle>e;\<rho>;\<kappa>\<rangle>)
  "

lemma is_super_exp_preserved_over_stack: "
  E \<rightarrow> E' \<Longrightarrow>
  \<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma> \<Longrightarrow>
  E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp_over_stack e\<^sub>0 \<kappa>'
"
proof -
  assume
    A: "\<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>" and
    B: "E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"

  assume "E \<rightarrow> E'" then

  show "is_super_exp_over_stack e\<^sub>0 \<kappa>'" sorry
qed

lemma is_super_exp_preserved_over_exp: "
  E \<rightarrow> E' \<Longrightarrow>
  \<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma> \<Longrightarrow>
  E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp_left e\<^sub>0 e'
"
proof -
  assume 
    H1: "\<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>" and
    H2: "E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"

  assume "E \<rightarrow> E'"

  then show "is_super_exp_left e\<^sub>0 e'"
  proof cases
    case (Seq_Step_Down \<pi> x \<rho> x\<^sub>\<kappa> e\<^sub>\<kappa> \<rho>\<^sub>\<kappa> \<kappa> \<sigma>')

    assume 
      H3: "E' = E ++ [\<pi> ;; LReturn x\<^sub>\<kappa> \<mapsto> \<sigma>']" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" and
      H6: "\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'" 

    show "is_super_exp_left e\<^sub>0 e'"
    proof cases
      assume H7: "\<pi>' = (\<pi> ;; LReturn x\<^sub>\<kappa>)"

      from H3 have "E' (\<pi> ;; LReturn x\<^sub>\<kappa>) = Some \<sigma>'" by simp

      with H2 H7 have H8: "\<sigma>' = \<langle>e';\<rho>';\<kappa>'\<rangle>" by simp

      from H6 obtain \<omega> where
        H9: "\<sigma>' =  \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>" by (auto simp: seq_step.simps)

      with H8 have H10: "e\<^sub>\<kappa> = e'" by simp
  
      from H1 H5 have "is_super_exp_over_state e\<^sub>0 (\<langle>RESULT x;\<rho>;\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>)" by blast

      then have "is_super_exp_over_stack e\<^sub>0 (\<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)" by (blast dest: is_super_exp_over_state.cases)

      then have "is_super_exp_left e\<^sub>0 e\<^sub>\<kappa>" by (simp add: is_super_exp_over_stack.simps)

      with H10 show "is_super_exp_left e\<^sub>0 e'" by simp
    next
      assume H7: "\<pi>' \<noteq> (\<pi> ;; LReturn x\<^sub>\<kappa>)"

      with H2 H3 have "E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto

      with H1 show "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Seq_Step \<pi> x b el \<rho>l \<kappa>l el' \<rho>l')
    assume 
      H3: "E' = E ++ [\<pi> ;; LNext x \<mapsto> \<langle>el';\<rho>l';\<kappa>l\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" and
      H6: "\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle> \<hookrightarrow> \<langle>el';\<rho>l';\<kappa>l\<rangle>"

    show "is_super_exp_left e\<^sub>0 e'"
    proof cases
      assume "\<pi>' = \<pi> ;; LNext x"
      show "is_super_exp_left e\<^sub>0 e'" sorry
    next
      assume "\<pi>' \<noteq> \<pi> ;; LNext x"

      with H2 H3 have "E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto

      with H1 show "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Seq_Step_Up \<pi> x b el \<rho>l \<kappa>l el' \<rho>l')
    assume 
      H3: "E' = E ++ [\<pi> ;; LCall x \<mapsto> \<langle>el';\<rho>l';\<langle>x,el,\<rho>l\<rangle> # \<kappa>l\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle>)" and
      H6: "\<langle>LET x = b in el;\<rho>l;\<kappa>l\<rangle> \<hookrightarrow> \<langle>el';\<rho>l';\<langle>x,el,\<rho>l\<rangle> # \<kappa>l\<rangle>"

    show "is_super_exp_left e\<^sub>0 e'"
    proof cases
      assume "\<pi>' = \<pi> ;; LCall x "
      show "is_super_exp_left e\<^sub>0 e'" sorry
    next
      assume "\<pi>' \<noteq> \<pi> ;; LCall x"

      with H2 H3 have "E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto

      with H1 show "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Let_Chan \<pi> x e \<rho> \<kappa>)
    assume
      H3: "E' = E ++ [\<pi> ;; LNext x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VChan (Ch \<pi> x)];\<kappa>\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e;\<rho>;\<kappa>\<rangle>)"

    show "is_super_exp_left e\<^sub>0 e'"
    proof cases
      assume "\<pi>' = \<pi> ;; LNext x"
      show "is_super_exp_left e\<^sub>0 e'" sorry
    next
      assume "\<pi>' \<noteq> \<pi> ;; LNext x"

      with H2 H3 have "E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto

      with H1 show "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_over_state.cases)
    qed
  next
    case (Let_Spawn \<pi> x e\<^sub>c e \<rho> \<kappa>)
    assume
      H3: "E' = E ++ [\<pi> ;; LNext x \<mapsto> \<langle>e;\<rho> ++ [x \<mapsto> VUnit];\<kappa>\<rangle>, \<pi> ;; LSpawn x \<mapsto> \<langle>e\<^sub>c;\<rho>;[]\<rangle>]" and
      H4: "leaf E \<pi>" and
      H5: "E \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e;\<rho>;\<kappa>\<rangle>)"

    show "is_super_exp_left e\<^sub>0 e'"
    proof cases
      assume "\<pi>' = \<pi> ;; LSpawn x"
      show "is_super_exp_left e\<^sub>0 e'" sorry
    next
      assume H6: "\<pi>' \<noteq> \<pi> ;; LSpawn x"

      show "is_super_exp_left e\<^sub>0 e'"
      proof cases
        assume "\<pi>' = \<pi> ;; LNext x"
        show "is_super_exp_left e\<^sub>0 e'" sorry
      next
        assume "\<pi>' \<noteq> \<pi> ;; LNext x"
  
        with H2 H3 H6 have "E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto
  
        with H1 show "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_over_state.cases)
      qed
    qed
  next
    case (Let_Sync \<pi>\<^sub>s x\<^sub>s x\<^sub>s\<^sub>e e\<^sub>s \<rho>\<^sub>s \<kappa>\<^sub>s x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>s\<^sub>e \<pi>\<^sub>r x\<^sub>r x\<^sub>r\<^sub>e e\<^sub>r \<rho>\<^sub>r \<kappa>\<^sub>r x\<^sub>r\<^sub>c \<rho>\<^sub>r\<^sub>e c \<omega>\<^sub>m)

    assume 
      H3: "E' = E ++ [\<pi>\<^sub>s ;; LNext x\<^sub>s \<mapsto> \<langle>e\<^sub>s;\<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit];\<kappa>\<^sub>s\<rangle>, \<pi>\<^sub>r ;; LNext x\<^sub>r \<mapsto> \<langle>e\<^sub>r;\<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m];\<kappa>\<^sub>r\<rangle>]" and
      H4: "leaf E \<pi>\<^sub>s" and
      H5: "E \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s;\<rho>\<^sub>s;\<kappa>\<^sub>s\<rangle>)"

    show "is_super_exp_left e\<^sub>0 e'"
    proof cases
      assume "\<pi>' = \<pi>\<^sub>r ;; LNext x\<^sub>r"
      show "is_super_exp_left e\<^sub>0 e'" sorry
    next
      assume H6: "\<pi>' \<noteq> \<pi>\<^sub>r ;; LNext x\<^sub>r"

      show "is_super_exp_left e\<^sub>0 e'"
      proof cases
        assume "\<pi>' = \<pi>\<^sub>s ;; LNext x\<^sub>s"
        show "is_super_exp_left e\<^sub>0 e'" sorry
      next
        assume "\<pi>' \<noteq> \<pi>\<^sub>s ;; LNext x\<^sub>s"
  
        with H2 H3 H6 have "E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" by auto

        with H1 show "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_over_state.cases)
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
by (metis is_super_exp_over_state.simps is_super_exp_preserved_over_exp is_super_exp_preserved_over_stack state.exhaust)

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
    show ?case by (simp add: is_super_exp_left.Refl is_super_exp_over_stack.Empty is_super_exp_over_state.intros)
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
