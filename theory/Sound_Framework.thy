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


lemma super_pool_preserved: "

\<forall> \<pi> e \<rho> \<kappa>.
  E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
  leaf E \<pi> \<longrightarrow> prefix \<pi> \<pi>' \<longrightarrow> 
  is_super_exp e e' \<or> is_super_stack \<kappa> e' \<Longrightarrow>

E0 \<rightarrow> E \<Longrightarrow> 

E0 \<pi>0 = Some (\<langle>e0;\<rho>0;\<kappa>0\<rangle>) \<Longrightarrow>
leaf E0 \<pi>0 \<Longrightarrow> 
prefix \<pi>0 \<pi>' \<Longrightarrow>

is_super_exp e0 e' \<or> is_super_stack \<kappa>0 e'
"
sorry


lemma isnt_exp_sound_generalized: "
  \<E> \<rightarrow>* \<E>' \<Longrightarrow> 
  \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  leaf \<E> \<pi> \<Longrightarrow>
  prefix \<pi> \<pi>' \<Longrightarrow>
  is_super_exp e e' \<or> is_super_stack \<kappa> e'
"
proof -
  assume "\<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>)" "\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)" 
    "leaf \<E> \<pi>" "prefix \<pi> \<pi>'"

  assume "\<E> \<rightarrow>* \<E>'" then
  have "
    \<forall> \<pi> e \<rho> \<kappa> .
      \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
      \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow>
      leaf \<E> \<pi> \<longrightarrow>
      prefix \<pi> \<pi>' \<longrightarrow>
      is_super_exp e e' \<or> is_super_stack \<kappa> e'
  "
  proof (induction rule: star.induct)
    case (refl \<E>)
    show ?case
      by (metis is_super_exp.simps leaf.cases option.distinct(1) option.inject prefix_order.dual_order.order_iff_strict state.inject)
  next
    case (step E0 E E')

    assume "E0 \<rightarrow> E" "E \<rightarrow>* E'"
    assume "
      \<forall>\<pi> e \<rho> \<kappa>.
        E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> 
        E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> 
        leaf E \<pi> \<longrightarrow> prefix \<pi> \<pi>' \<longrightarrow> 
        is_super_exp e e' \<or> is_super_stack \<kappa> e'
    "
    {
      fix \<pi>0 e0 \<rho>0 \<kappa>0
      assume "E0 \<pi>0 = Some (\<langle>e0;\<rho>0;\<kappa>0\<rangle>)" 
        "leaf E0 \<pi>0" "prefix \<pi>0 \<pi>'"

      assume "E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)"
      with \<open>
      \<forall>\<pi> e \<rho> \<kappa>.
        E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> 
        E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> 
        leaf E \<pi> \<longrightarrow> prefix \<pi> \<pi>' \<longrightarrow> 
        is_super_exp e e' \<or> is_super_stack \<kappa> e'
      \<close>

      have "
        \<forall>\<pi> e \<rho> \<kappa>.
          E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
          leaf E \<pi> \<longrightarrow> prefix \<pi> \<pi>' \<longrightarrow> 
          is_super_exp e e' \<or> is_super_stack \<kappa> e'
      " by blast 
      with \<open>E0 \<rightarrow> E\<close>
        \<open>E0 \<pi>0 = Some (\<langle>e0;\<rho>0;\<kappa>0\<rangle>)\<close> 
        \<open>leaf E0 \<pi>0\<close> \<open>prefix \<pi>0 \<pi>'\<close>

      have "is_super_exp e0 e' \<or> is_super_stack \<kappa>0 e'" by (blast dest: super_pool_preserved)

    } then

    show "
      \<forall>\<pi> e \<rho> \<kappa>. 
        E0 \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> 
        leaf E0 \<pi> \<longrightarrow> prefix \<pi> \<pi>' \<longrightarrow> 
        is_super_exp e e' \<or> is_super_stack \<kappa> e'
    " by blast

  qed
  with \<open>\<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>)\<close> \<open>\<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>)\<close> \<open>leaf \<E> \<pi>\<close> \<open>prefix \<pi> \<pi>'\<close>

  show "is_super_exp e e' \<or> is_super_stack \<kappa> e'" by blast

qed

lemma isnt_exp_sound: "
  [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e'
"
sorry


end
