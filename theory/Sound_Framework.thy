theory Sound_Framework
  imports Main Syntax Dynamic_Semantics Static_Semantics
      Static_Framework
      "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

inductive is_super_stack :: "cont list \<Rightarrow> exp \<Rightarrow> bool" where
  Exp: "
    is_super_exp e e' \<Longrightarrow>
    is_super_stack (\<langle>x, e, \<rho>\<rangle> # \<kappa>) e'
  " |
  Stack: "
    is_super_stack \<kappa> e' \<Longrightarrow>
    is_super_stack (\<langle>x, e, \<rho>\<rangle> # \<kappa>) e'
  "

lemma is_super_exp_preserved: "
  E \<rightarrow> E' \<Longrightarrow>
  \<forall>\<pi> e \<rho> \<kappa>. E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> is_super_exp e\<^sub>0 e \<Longrightarrow>
  E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp_left e\<^sub>0 e'
"
sorry


lemma isnt_exp_sound_generalized: "
  \<E>0 \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e'
"
proof -

  assume P1: "\<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and P2: "\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"

  assume "\<E>0 \<rightarrow>* \<E>'" then

  have "star_left (op \<rightarrow>) \<E>0 \<E>'" by (simp add: star_implies_star_left) then

  have "
    \<forall> \<pi>' e' \<rho>' \<kappa>' .
    \<E>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow>
    is_super_exp e\<^sub>0 e'
  " proof (induction)
    case (refl x)
    show ?case by (simp add: is_super_exp.Refl)
  next
    case (step E0 E E')
    assume "star_left op \<rightarrow> E0 E"
    assume "E \<rightarrow> E'"
    assume IH: "\<forall>\<pi>' e' \<rho>' \<kappa>'. E0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow> E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> is_super_exp e\<^sub>0 e'"
    {
      fix \<pi>' e' \<rho>' \<kappa>'
      assume 
        P1: "E0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>]" and
        P2: "E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" 

      from IH and P1

      have IH2: "\<forall>\<pi>' e' \<rho>' \<kappa>'. E \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> is_super_exp e\<^sub>0 e'" by blast
      with P2 \<open>E \<rightarrow> E'\<close>

      have "is_super_exp_left e\<^sub>0 e'" by (blast dest: is_super_exp_preserved) then

      have "is_super_exp e\<^sub>0 e'" by (simp add: is_super_exp_left_implies_is_super_exp)
    } then
    show ?case by blast
  qed
  with P1 and P2

  show "is_super_exp e\<^sub>0 e'"  by blast
qed

lemma isnt_exp_sound: "
  [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e'
"
sorry


end
