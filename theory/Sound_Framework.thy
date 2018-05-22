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

lemma pool_nonempty: "
  [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E> \<Longrightarrow> 
  \<exists> \<pi> e \<rho> \<kappa> . \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>)
"
sorry


lemma super_exp_preserved: "
  \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e \<Longrightarrow>
  \<E> \<rightarrow> \<E>' \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow> 
  is_super_exp e\<^sub>0 e'
"
sorry

lemma isnt_exp_sound': "
  \<E>\<^sub>0 \<rightarrow>* \<E> \<Longrightarrow> 
  \<forall> \<pi> e \<rho> \<kappa> .
    \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
    is_super_exp e\<^sub>0 e
"
proof -
 assume "\<E>\<^sub>0 \<rightarrow>* \<E> " then
 have "star_left concur_step \<E>\<^sub>0 \<E>" by (simp add: star_implies_star_left) then
 show "
  \<forall> \<pi> e \<rho> \<kappa> .
    \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow>
    is_super_exp e\<^sub>0 e
 "
 proof (induction rule: star_left.induct)
   case (refl \<E>\<^sub>0)
   show "
     \<forall>\<pi> e \<rho> \<kappa>. 
        \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow> 
        \<E>\<^sub>0 \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> 
        is_super_exp e\<^sub>0 e
   " by (simp add: Refl)
 next
   case (step \<E>\<^sub>0 \<E> \<E>') 
   assume "star_left op \<rightarrow> \<E>\<^sub>0 \<E>"
   and "\<E> \<rightarrow> \<E>'"
   and "\<forall>\<pi> e \<rho> \<kappa>. \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow> \<E> \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> is_super_exp e\<^sub>0 e"
   then

   show "
     \<forall>\<pi>' e' \<rho>' \<kappa>'. 
       \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow> 
       \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> 
       is_super_exp e\<^sub>0 e'
   " by (metis pool_nonempty star_left_implies_star super_exp_preserved)
  qed
qed


lemma isnt_exp_sound: "
  [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  is_super_exp e\<^sub>0 e'
"
by (simp add: isnt_exp_sound')


end
