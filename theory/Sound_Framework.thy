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
    A: "\<forall>\<pi> \<sigma>. E \<pi> = Some \<sigma> \<longrightarrow> is_super_exp_over_state e\<^sub>0 \<sigma>" and
    B: "E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"

  assume "E \<rightarrow> E'" then

  show "is_super_exp_left e\<^sub>0 e'" sorry
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
