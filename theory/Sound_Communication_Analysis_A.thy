theory Sound_Communication_Analysis_A
  imports 
    Main
    Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Static_Framework Sound_Framework
    Dynamic_Communication_Analysis 
    Static_Communication_Analysis Static_Communication_Analysis_A
    Sound_Communication_Analysis
begin

(*
START just for reference

lemma inclusive_preserved: "
  \<E> \<rightarrow> \<E>' \<Longrightarrow>
  \<forall>\<pi>1. (\<exists>\<sigma>\<^sub>1. \<E> \<pi>1 = Some \<sigma>\<^sub>1) \<longrightarrow> (\<forall>\<pi>2. (\<exists>\<sigma>\<^sub>2. \<E> \<pi>2 = Some \<sigma>\<^sub>2) \<longrightarrow> \<pi>1 \<asymp> \<pi>2) \<Longrightarrow>
  \<E>' \<pi>1 = Some \<sigma>\<^sub>1 \<Longrightarrow> \<E>' \<pi>2 = Some \<sigma>\<^sub>2 \<Longrightarrow> 
  \<pi>1 \<asymp> \<pi>2
"
 apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)

   apply (case_tac "\<pi>1 = \<pi> ;; (LReturn x\<^sub>\<kappa>')"; auto; (case_tac "\<pi>2 = \<pi> ;; (LReturn x\<^sub>\<kappa>')"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)
   
   apply (case_tac "\<pi>1 = \<pi> ;; (LCall xa)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LCall xa)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LNext x)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext x)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)

   apply (case_tac "\<pi>1 = \<pi> ;; (LSpawn x)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LSpawn x)"; auto))
   apply (simp add: Ordered)
   apply (case_tac "\<pi>2 = \<pi> ;; (LNext x)"; auto)
  apply (simp add: Spawn_Left)
  apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
  apply (case_tac "\<pi>1 = \<pi> ;; (LNext x)"; auto)
  apply (simp add: Spawn_Right)
  apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict) 
   apply (case_tac "\<pi>1 = \<pi> ;; (LNext x)"; auto; (case_tac "\<pi>2 = \<pi> ;; (LNext x)"; auto))
   apply (simp add: Ordered)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.order_iff_strict prefix_snoc)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps prefix_append prefix_order.dual_order.order_iff_strict)


   apply (case_tac "\<pi>1 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (simp add: Ordered)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf.simps prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>1 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (metis inclusive.simps inclusive_preserved_under_unordered_extension leaf.simps prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (smt Ordered exp.inject(1) inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.inject prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc state.inject)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (simp add: Ordered)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>2 in spec; auto)
   apply (metis Ordered inclusive_preserved_under_unordered_extension leaf.simps option.simps(3) prefix_order.le_less prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>r ;; (LNext x\<^sub>r)"; auto)
   apply (drule_tac x = \<pi>\<^sub>r in spec; auto)
   apply (drule_tac x = \<pi>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (case_tac "\<pi>2 = \<pi>\<^sub>s ;; (LNext x\<^sub>s)"; auto)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
   apply (drule_tac x = \<pi>\<^sub>s in spec; auto)
   apply (drule_tac x = \<pi>1 in spec; auto)
   apply (metis Ordered inclusive_commut inclusive_preserved_under_unordered_extension leaf.simps option.distinct(1) prefix_order.dual_order.not_eq_order_implies_strict prefix_snoc)
 
done


lemma runtime_paths_are_inclusive': "
  \<E>\<^sub>0 \<rightarrow>* \<E> \<Longrightarrow>
  (\<forall> \<pi>1 \<pi>2 \<sigma>\<^sub>1 \<sigma>\<^sub>2.
    \<E>\<^sub>0 = [[] \<mapsto> \<langle>e\<^sub>0;Map.empty;[]\<rangle>] \<longrightarrow>
    \<E> \<pi>1 = Some \<sigma>\<^sub>1 \<longrightarrow>
    \<E> \<pi>2 = Some \<sigma>\<^sub>2 \<longrightarrow>
    \<pi>1 \<asymp> \<pi>2
  )
"
 apply (drule star_implies_star_left)
 apply (erule star_left.induct; auto)
  apply (simp add: Ordered)
 apply (rename_tac \<E> \<E>' \<pi>1 \<sigma>\<^sub>1 \<pi>2 \<sigma>\<^sub>2)
 apply (blast dest: inclusive_preserved)
done



lemma runtime_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    \<E>' \<pi>1' = Some \<sigma>\<^sub>1';
    \<E>' \<pi>2' = Some \<sigma>\<^sub>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>1' \<asymp> \<pi>2'
"
by (blast dest: runtime_paths_are_inclusive')




lemma runtime_send_paths_are_inclusive: "
  \<lbrakk>
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    is_send_path \<E>' c \<pi>1';
    is_send_path \<E>' c \<pi>2'
  \<rbrakk> \<Longrightarrow> 
  \<pi>1' \<asymp> \<pi>2'
"
apply (unfold is_send_path.simps; auto)
using runtime_paths_are_inclusive by blast


END just for reference
********** 
*)


lemma static_paths_of_same_run_inclusive_base: "
  E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "paths_congruent \<pi>1 path1" and
    H5: "paths_congruent \<pi>2 path2"
  from H1 H2 H4 show 
    "path1 \<asymp> path2"
    by (metis H3 H5 Nil_prefix Prefix2 append_is_Nil_conv fun_upd_apply list.distinct(1) paths_congruent.cases)
qed

lemma paths_equal_implies_paths_inclusive: "
  path1 = path2 \<Longrightarrow> path1 \<asymp> path2 
"
by (simp add: Prefix2)

lemma paths_cong_preserved_under_reduction: "
  paths_congruent (\<pi> ;; l) (path @ [n]) \<Longrightarrow>
  paths_congruent \<pi> path"
using paths_congruent.cases by fastforce


lemma path_state_preserved_for_non_leaf: "
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' (\<pi> ;; l) = Some \<sigma> \<Longrightarrow>
\<not> leaf E \<pi> \<Longrightarrow>
E (\<pi> ;; l) = Some \<sigma>
"
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply presburger+
  apply (metis append1_eq_conv fun_upd_other)
  apply (metis butlast_snoc fun_upd_apply)
done

lemma not_strict_prefix_preserved_under_congruent_paths: "
\<not> strict_prefix \<pi>1 \<pi>2 \<Longrightarrow>
paths_congruent \<pi>1 path1 \<Longrightarrow>
paths_congruent \<pi>2 path2 \<Longrightarrow>
\<not> strict_prefix path1 path2
"
sorry



lemma spawn_point: "
  (E, H) \<rightarrow> (E', H') \<Longrightarrow>
  leaf E \<pi> \<Longrightarrow>
  E' (\<pi> ;; l1) = \<sigma>1 \<Longrightarrow>
  E' (\<pi> ;; l2) = \<sigma>2 \<Longrightarrow>
  l1 = l2 \<or> 
  (\<exists> x . l1 = (LNext x) \<and> l2 = (LSpawn x)) \<or>
  (\<exists> x . l1 = (LSpawn x) \<and> l2 = (LNext x))
"
sorry

lemma spawn_point_preserved_under_congruent_paths: "
l1 = l2 \<or> 
(\<exists> x . l1 = (LNext x) \<and> l2 = (LSpawn x)) \<or>
(\<exists> x . l1 = (LSpawn x) \<and> l2 = (LNext x)) \<Longrightarrow>
paths_congruent [l1] [n1] \<Longrightarrow>
paths_congruent [l2] [n2] \<Longrightarrow>
n1 = n2 \<or> 
(\<exists> x . n1 = (NLet x, ENext) \<and> n2 = (NLet x, ESpawn )) \<or>
(\<exists> x . n1 = (NLet x, ESpawn ) \<and> n2 = (NLet x, ENext))
"
sorry

lemma static_paths_of_same_run_inclusive_step: "
\<forall>\<pi>1 \<pi>2 path1 path2.
  E \<pi>1 \<noteq> None \<longrightarrow>
  E \<pi>2 \<noteq> None \<longrightarrow>
  paths_congruent \<pi>1 path1 \<longrightarrow> 
  paths_congruent \<pi>2 path2 \<longrightarrow> 
  path1 \<asymp> path2 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
paths_congruent \<pi>1 path1 \<Longrightarrow> 
paths_congruent \<pi>2 path2 \<Longrightarrow>
path1 \<asymp> path2 
"
proof ((case_tac "path1 = []"; (simp add: Prefix1)), (case_tac "path2 = []", (simp add: Prefix2)))
  assume 
    H1: "
      \<forall>\<pi>1. (\<exists>y. E \<pi>1 = Some y) \<longrightarrow>
      (\<forall>\<pi>2. (\<exists>y. E \<pi>2 = Some y) \<longrightarrow>
      (\<forall>path1. paths_congruent \<pi>1 path1 \<longrightarrow>
      (\<forall>path2. paths_congruent \<pi>2 path2 \<longrightarrow> 
        path1 \<asymp> path2)))" and
    H2: "star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H)" and
    H3: "(E, H) \<rightarrow> (E', H')" and
    H4: "\<exists>y. E' \<pi>1 = Some y" and
    H5: "\<exists>y. E' \<pi>2 = Some y " and
    H6: "paths_congruent \<pi>1 path1" and
    H7: "paths_congruent \<pi>2 path2" and
    H8: "path1 \<noteq> []" and 
    H9: "path2 \<noteq> []"

  obtain \<sigma>1 where 
    H10: "E' \<pi>1 = Some \<sigma>1"
    using H4 by blast

  obtain \<sigma>2 where 
    H11: "E' \<pi>2 = Some \<sigma>2"
    using H5 by blast

  obtain \<pi>1x l1 path1x n1 where
    H12: "\<pi>1x ;; l1 = \<pi>1" and
    H13: "path1x @ [n1] = path1" and
    H14: "paths_congruent \<pi>1x path1x"
    by (metis H6 H8 paths_congruent.cases)

  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x ;; l2 = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "paths_congruent \<pi>2x path2x"
  by (metis H7 H9 paths_congruent.cases)

 
  have H22: "paths_congruent [l1] [n1]"
    by (metis H12 H13 H6 H8 Node append1_eq_conv append_eq_Cons_conv paths_congruent.simps)

  have H23: "paths_congruent [l2] [n2]"
    by (metis (no_types, lifting) Cons_eq_append_conv H15 H16 H7 H9 Node append1_eq_conv paths_congruent.simps)

  show "path1 \<asymp> path2"
  proof cases
    assume L1H1: "leaf E \<pi>1x"
    obtain \<sigma>1x where
      L1H2: "E \<pi>1x = Some \<sigma>1x" using L1H1 leaf.simps by auto
    show "path1 \<asymp> path2"
    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto


      have L2H4: "\<not> strict_prefix \<pi>1x \<pi>2x"
        by (meson L1H1 L2H1 leaf.cases)
      have L2H5: "\<not> strict_prefix \<pi>2x \<pi>1x"
        by (meson L1H1 L2H1 leaf.cases)

      have L2H6: "\<not> strict_prefix path1x path2x"
        using H14 H17 L2H4 not_strict_prefix_preserved_under_congruent_paths by auto
      have L2H7: "\<not> strict_prefix path2x path1x"
        using H14 H17 L2H5 not_strict_prefix_preserved_under_congruent_paths by blast

      have L2H8: "path1x \<asymp> path2x"
        using H1 H14 H17 L1H2 L2H2 by blast

      show "path1 \<asymp> path2"
      proof cases
        assume L3H1: "path1x = path2x"

        have L3H3: "
          l1 = l2 \<or> 
          (\<exists> x . l1 = (LNext x) \<and> l2 = (LSpawn x)) \<or>
          (\<exists> x . l1 = (LSpawn x) \<and> l2 = (LNext x))" 
          using spawn_point H3 L1H1 by auto

        have L3H4: "
          n1 = n2 \<or> 
          (\<exists> x . n1 = (NLet x, ENext) \<and> n2 = (NLet x, ESpawn )) \<or>
          (\<exists> x . n1 = (NLet x, ESpawn ) \<and> n2 = (NLet x, ENext))" 
          using H22 H23 L3H3 spawn_point_preserved_under_congruent_paths by auto

        have L3H5: "path1x @ [n1] \<asymp> path1x @ [n2]"
          using L3H4 may_be_inclusive.intros(3) may_be_inclusive.intros(4) paths_equal_implies_paths_inclusive by blast
        show "path1 \<asymp> path2"
          using H13 H16 L3H1 L3H5 by auto
      next
        assume L3H1: "path1x \<noteq> path2x"
        show "path1 \<asymp> path2"
          using H13 H16 L2H6 L2H7 L2H8 L3H1 may_be_inclusive_preserved_under_unordered_double_extension strict_prefixI by blast
      qed
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      have L2H3: "path1x \<asymp> path2"
        using H1 H14 H7 L1H2 L2H2 by blast

      have L2H8: "\<not> strict_prefix \<pi>1x \<pi>2"
        by (metis L1H1 L2H2 leaf.cases option.distinct(1))
      have L2H9: "\<not> strict_prefix path1x path2"
        using H14 H7 L2H8 not_strict_prefix_preserved_under_congruent_paths by blast
      show "path1 \<asymp> path2"
        by (metis H13 L2H3 L2H9 Prefix2 may_be_inclusive_preserved_under_unordered_extension prefix_prefix strict_prefix_def)
    qed

  next
    assume L1H1: "\<not> leaf E \<pi>1x"
      have L1H2: "E \<pi>1 = Some \<sigma>1"
        using H10 H12 H3 L1H1 path_state_preserved_for_non_leaf by blast
    show "path1 \<asymp> path2"

    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have L2H3: "path1 \<asymp> path2x"
        using H1 H17 H6 L1H2 L2H2 by blast
      have L2H8: "\<not> strict_prefix \<pi>2x \<pi>1"
        by (metis L1H2 L2H1 leaf.cases option.distinct(1))
      have L2H9: "\<not> strict_prefix path2x path1"
        using H17 H6 L2H8 not_strict_prefix_preserved_under_congruent_paths by auto
      show "path1 \<asymp> path2"
        by (metis H16 L2H3 L2H9 Prefix1 may_be_inclusive_commut may_be_inclusive_preserved_under_unordered_extension prefix_order.dual_order.not_eq_order_implies_strict prefix_prefix)
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      show "path1 \<asymp> path2"
        using H1 H6 H7 L1H2 L2H2 by blast
    qed

  qed

qed

lemma static_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
proof -
  assume
    H1: "([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "paths_congruent \<pi>1 path1" and
    H5: "paths_congruent \<pi>2 path2"

  from H1 have
    "star_left (op \<rightarrow>) ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')" by (simp add: star_implies_star_left)
  
  then obtain X0 X' where 
    H6: "X0 = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" 
        "X' = (\<E>', H')" and
    H7: "star_left (op \<rightarrow>) X0 X'" by auto

  from H7 have 
    H8: "
      \<forall> \<E>' H' \<pi>1 \<pi>2 path1 path2.
      X0 = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<longrightarrow> X' = (\<E>', H') \<longrightarrow>
      \<E>' \<pi>1 \<noteq> None \<longrightarrow>
      \<E>' \<pi>2 \<noteq> None \<longrightarrow>
      paths_congruent \<pi>1 path1 \<longrightarrow>
      paths_congruent \<pi>2 path2 \<longrightarrow>
      path1 \<asymp> path2
    "
  proof induction
    case (refl z)
    then show ?case
      using static_paths_of_same_run_inclusive_base by blast
  next
    case (step x y z)

    {
      fix \<E>' H' \<pi>1 \<pi>2 path1 path2
      assume 
        L2H1: "x = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" and
        L2H2: "z = (\<E>', H')" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "paths_congruent \<pi>1 path1" and
        L2H6: "paths_congruent \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8: "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          paths_congruent \<pi>1 path1 \<longrightarrow> 
          paths_congruent \<pi>2 path2 \<longrightarrow> 
          path1 \<asymp> path2 "
        by blast

      have 
        "path1 \<asymp> path2"
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 static_paths_of_same_run_inclusive_step step.hyps(1) step.hyps(2) by blast
    }
    then show ?case by blast
  qed

  from H2 H3 H4 H5 H6(1) H6(2) H8 show 
    "path1 \<asymp> path2" by blast
qed

lemma is_send_path_implies_nonempty_pool: "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2: "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed

lemma send_static_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
using is_send_path_implies_nonempty_pool static_paths_of_same_run_inclusive by fastforce



lemma equality_preserved_under_congruent: "
  path1 = path2 \<Longrightarrow>
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  \<pi>1 = \<pi>2
"
sorry

lemma send_static_paths_equal_exclusive_implies_dynamic_paths_equal: "
pathSync = pathSynca \<or> (\<not> pathSynca \<asymp> pathSync) \<Longrightarrow> 

([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>1 \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>2 \<Longrightarrow>

paths_congruent \<pi>\<^sub>1 pathSync \<Longrightarrow>
paths_congruent \<pi>\<^sub>2 pathSynca \<Longrightarrow>

\<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (simp add: equality_preserved_under_congruent send_static_paths_of_same_run_inclusive)

(* END *)


(* PATH SOUND *)


inductive simple_flow_set_pool :: "abstract_value_env \<Rightarrow> flow_set \<Rightarrow> trace_pool \<Rightarrow> bool"  where
  Intro: "
    (\<forall> \<pi> e \<rho> \<kappa> . E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> 
      simple_flow_set V F e \<and>
      simple_flow_set_env V F \<rho> \<and>
      simple_flow_set_stack V F \<kappa>
      ) \<Longrightarrow> 
    simple_flow_set_pool V F E
  "


lemma simple_flow_set_pool_preserved_star: "

  simple_flow_set_pool V F ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]) \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x = b in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  simple_flow_set_pool V F \<E>'
"
sorry

lemma simple_flow_set_pool_implies_may_be_path: "
  \<E>' \<pi> = Some (\<langle>LET x = b in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  simple_flow_set_pool V F \<E>' \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_congruent \<pi> path \<and>
    may_be_path V F (nodeLabel e) isEnd path
"
sorry


lemma lift_simple_flow_set_to_pool: "
  simple_flow_set V F e \<Longrightarrow>
  simple_flow_set_pool V F [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]
"
sorry

lemma isnt_path_sound: "
  \<E>' \<pi> = Some (\<langle>LET x = b in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_congruent \<pi> path \<and>
    may_be_path V F (nodeLabel e) isEnd path
"
by (metis lift_simple_flow_set_to_pool simple_flow_set_pool_implies_may_be_path simple_flow_set_pool_preserved_star)


lemma isnt_send_evt_sound: "
  \<lbrakk>
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow>
  {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> V x\<^sub>e
"
  apply (drule values_not_bound_sound; assumption?; auto)
done

lemma isnt_send_chan_sound: "
  \<lbrakk>
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi> xC));
    \<rho>\<^sub>y x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e);
    \<E>' \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>);
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H');
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan xC \<in> V x\<^sub>s\<^sub>c
"
 apply (frule may_be_static_eval_to_pool)
 apply (drule may_be_static_eval_preserved_under_concur_step_star[of _ _ _ ]; assumption?)
 apply (erule may_be_static_eval_pool.cases; auto)
 apply (drule spec[of _ \<pi>\<^sub>y], drule spec[of _ "\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>y;\<rho>\<^sub>y;\<kappa>\<^sub>y\<rangle>"], simp)
 apply (erule may_be_static_eval_state.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>e], drule spec[of _ "(VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e)"]; simp)
 apply (erule conjE)
 apply (erule may_be_static_eval_value.cases; auto)
 apply (erule may_be_static_eval_env.cases; auto)
 apply (drule spec[of _ x\<^sub>s\<^sub>c], drule spec[of _ "(VChan (Ch \<pi> xC))"]; simp)
done

lemma isnt_send_site_sound: "
  \<E>' \<pi>Sync = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>C xC)) \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  may_be_static_send_node_label V e xC (NLet x\<^sub>y)
"
 apply (unfold may_be_static_send_node_label.simps; auto)
 apply (rule exI[of _ x\<^sub>s\<^sub>c]; auto)
 apply (auto simp: isnt_send_chan_sound)
 apply (rule exI[of _ x\<^sub>m]; auto?)
 apply (rule exI[of _ x\<^sub>e]; auto?)
 apply (blast dest: isnt_send_evt_sound)
 apply (rule exI; auto?)
 apply (erule isnt_exp_sound; auto)
done


lemma isnt_send_path_sound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  \<exists> pathSync .
    (paths_congruent \<pi>Sync pathSync) \<and> 
    may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = x\<^sub>s\<^sub>c and \<pi>C = \<pi>C and \<rho>\<^sub>e = \<rho>\<^sub>e in isnt_send_site_sound; auto?)
 apply (frule isnt_path_sound; auto?)
done

(* END PATH SOUND *)



theorem one_shot_sound': "
  every_two_static_paths (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: every_two_dynamic_paths.simps every_two_static_paths.simps singular.simps; auto)

 apply (frule_tac \<pi>Sync = \<pi>\<^sub>1 in isnt_send_path_sound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>\<^sub>2 in isnt_send_path_sound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (simp add: equality_preserved_under_congruent send_static_paths_of_same_run_inclusive)
done

theorem one_shot_sound: "
  \<lbrakk>
    static_one_shot V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_shot.cases; auto)
 apply (unfold one_shot.simps)
 apply (simp add: one_shot_sound')
done


theorem noncompetitive_send_to_ordered_send: "
  every_two_static_paths (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: every_two_static_paths.simps noncompetitive.simps; auto?)
using isnt_send_path_sound static_paths_of_same_run_inclusive sorry


theorem fan_out_sound: "
  \<lbrakk>
    static_fan_out V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> xC)
"
 apply (erule static_fan_out.cases; auto)
 apply (unfold fan_out.simps)
 apply (metis noncompetitive_send_to_ordered_send)
done

lemma noncompetitive_recv_to_ordered_recv: "
   every_two_static_paths (may_be_path V F (nodeLabel e) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
   simple_flow_set V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
   every_two_dynamic_paths (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem fan_in_sound: "
  \<lbrakk>
    static_fan_in V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> xC)
"
 apply (erule static_fan_in.cases; auto)
 apply (unfold fan_in.simps)
 apply (metis noncompetitive_recv_to_ordered_recv)
done


theorem one_to_one_sound: "
  \<lbrakk>
    static_one_to_one V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_to_one.cases; auto)
 apply (unfold one_to_one.simps)
 apply (simp add: noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send)
done

end