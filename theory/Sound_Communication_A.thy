theory Sound_Communication_A
  imports Main Syntax 
    Dynamic_Semantics 
    Static_Semantics
    Sound_Semantics
    Dynamic_Communication
    Static_Communication
    Sound_Communication
    Static_Communication_A
    List
begin

lemma staticInclusiveCommut:
  "
  staticInclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> staticInclusive path\<^sub>2 path\<^sub>1
"
 apply (erule staticInclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
done


lemma staticInclusivePreservedDynamicEvalUnordExt:
  "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> 
  staticInclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> staticInclusive (path\<^sub>1 @ [l]) path\<^sub>2
"
 apply (erule staticInclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
done

lemma staticInclusivePreservedDynamicEvalUnordDoubExt:
  "
  staticInclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> staticInclusive (path\<^sub>1 @ [l1]) (path\<^sub>2 @ [l2])
"
by (metis staticInclusiveCommut staticInclusivePreservedDynamicEvalUnordExt prefix_append prefix_def)



inductive pathsCongruent :: "control_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty:
  "
    pathsCongruent [] []
  "
| Next:
  "
    pathsCongruent \<pi> path \<Longrightarrow>
    pathsCongruent (\<pi> @ [LNxt x]) (path @ [(IdBind x, ENext)])
  "
| Spawn:
  "
    pathsCongruent \<pi> path \<Longrightarrow>
    pathsCongruent (\<pi> @ [LSpwn x]) (path @ [(IdBind x, ESpawn)])
  "
| Call:
  "
    pathsCongruent \<pi> path \<Longrightarrow>
    pathsCongruent (\<pi> @ [LCall x]) (path @ [(IdBind x, ECall)])
  " 
| Return:
  "
    pathsCongruent \<pi> path \<Longrightarrow>
    pathsCongruent (\<pi> @ [LRtn x]) (path @ [(IdRslt x, EReturn)])
  " 

lemma staticInclusiveBaseSound:
  "
  E0 = [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  pathsCongruent \<pi>1 path1 \<Longrightarrow>
  pathsCongruent \<pi>2 path2 \<Longrightarrow>
  staticInclusive path1 path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> (Stt e empty [])]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "pathsCongruent \<pi>1 path1" and
    H5: "pathsCongruent \<pi>2 path2"
  
  from H4
  show "staticInclusive path1 path2"
  proof cases

    case Empty
    then show ?thesis
      by (simp add: Prefix1)
  next
    case (Next \<pi> path x)
    then show ?thesis
      using H1 H2 by auto
  next
    case (Spawn \<pi> path x)
    then show ?thesis
      using H1 H2 by auto
  next

    case (Call \<pi> path x)
    then show ?thesis
      using H1 H2 by auto
  next
    case (Return \<pi> path x)
    then show ?thesis
      using H1 H2 by auto
  qed 
qed


lemma paths_congPreservedDynamicEval_under_reduction:
  "
  pathsCongruent (\<pi> @ [l]) (path @ [n]) \<Longrightarrow>
  pathsCongruent \<pi> path"
using pathsCongruent.cases by fastforce


lemma equality_abstract_to_concrete':
  "
  pathsCongruent \<pi>1 path \<Longrightarrow>
  \<forall> \<pi>2 .  pathsCongruent \<pi>2 path \<longrightarrow> \<pi>1 = \<pi>2
"
apply (erule pathsCongruent.induct)
  using pathsCongruent.cases apply blast
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
done


lemma equality_abstract_to_concrete:
  "
  path1 = path2 \<Longrightarrow>
  pathsCongruent \<pi>1 path1 \<Longrightarrow>
  pathsCongruent \<pi>2 path2 \<Longrightarrow>
  \<pi>1 = \<pi>2
"
by (simp add: equality_abstract_to_concrete')

lemma pathsCongruentPreservedDynamicEval_under_reduction:
  "
  pathsCongruent \<pi>1 path1 \<Longrightarrow>
  pathsCongruent (butlast \<pi>1) (butlast path1) 
"
apply (erule pathsCongruent.cases; auto)
  apply (simp add: pathsCongruent.Empty)
done

lemma strict_prefixPreservedDynamicEval:
  "
pathsCongruent \<pi>1 path1 \<Longrightarrow>
pathsCongruent \<pi> path \<Longrightarrow>
strict_prefix path1 (path @ [n]) \<Longrightarrow>
\<not> strict_prefix \<pi>1 (\<pi> @ [l]) \<Longrightarrow>
strict_prefix (butlast path1) path
"
apply (erule pathsCongruent.cases; auto)
  using prefix_bot.bot.not_eq_extremum apply blast
  using prefix_order.order.strict_implies_order prefix_snocD apply fastforce
  using prefix_order.dual_order.strict_implies_order prefix_snocD apply fastforce
  using prefix_order.less_imp_le prefix_snocD apply fastforce
  using prefix_order.order.strict_implies_order prefix_snocD apply fastforce
done


lemma prefix_abstract_to_concrete':
  "

pathsCongruent \<pi>2 path2 \<Longrightarrow>
\<forall> \<pi>1 path1 .
pathsCongruent \<pi>1 path1 \<longrightarrow>
prefix path1 path2 \<longrightarrow>
prefix \<pi>1 \<pi>2
"
apply (erule pathsCongruent.induct; auto)
  apply (simp add: equality_abstract_to_concrete pathsCongruent.Empty)
  apply (simp add: equality_abstract_to_concrete pathsCongruent.Next)
  apply (simp add: equality_abstract_to_concrete' pathsCongruent.Spawn)
  apply (simp add: equality_abstract_to_concrete' pathsCongruent.Call)
  apply (simp add: equality_abstract_to_concrete' pathsCongruent.Return)
done

lemma prefix_abstract_to_concrete:
  "
pathsCongruent \<pi>2 path2 \<Longrightarrow>
pathsCongruent \<pi>1 path1 \<Longrightarrow>
prefix path1 path2 \<Longrightarrow>
prefix \<pi>1 \<pi>2
"
by (simp add: prefix_abstract_to_concrete')


lemma strict_prefix_abstract_to_concrete':
  "
pathsCongruent \<pi>2 path2 \<Longrightarrow>
\<forall> \<pi>1 path1 .
strict_prefix path1 path2 \<longrightarrow>
pathsCongruent \<pi>1 path1 \<longrightarrow>
strict_prefix \<pi>1 \<pi>2
"
apply (erule pathsCongruent.cases; auto)
  apply (metis not_Cons_self2 prefix_abstract_to_concrete prefix_snoc same_prefix_nil strict_prefix_def)+
done


lemma strict_prefix_abstract_to_concrete:
  "
strict_prefix path1 path2 \<Longrightarrow>
pathsCongruent \<pi>1 path1 \<Longrightarrow>
pathsCongruent \<pi>2 path2 \<Longrightarrow>
strict_prefix \<pi>1 \<pi>2
"
by (simp add: strict_prefix_abstract_to_concrete')


lemma equality_contcrete_to_abstract':
  "
  pathsCongruent \<pi> path1 \<Longrightarrow>
  \<forall> path2 .  pathsCongruent \<pi> path2 \<longrightarrow> path1 = path2
"
apply (erule pathsCongruent.induct)
apply auto[1]
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule pathsCongruent.cases; auto)
done

lemma equality_contcrete_to_abstract:
  "
  \<pi>1 = \<pi>2 \<Longrightarrow>
  pathsCongruent \<pi>1 path1 \<Longrightarrow>
  pathsCongruent \<pi>2 path2 \<Longrightarrow>
  path1 = path2

"
by (simp add: equality_contcrete_to_abstract')


lemma spawn_pointPreservedDynamicEval_under_congruent_paths: " 
l1 = (LNxt x) \<Longrightarrow> l2 = (LSpwn x) \<Longrightarrow>
pathsCongruent (\<pi> @ [l1]) (path @ [n1]) \<Longrightarrow>
pathsCongruent (\<pi> @ [l2]) (path @ [n2]) \<Longrightarrow>
n1 = (IdBind x, ENext) \<and> n2 = (IdBind x, ESpawn)
"
apply (erule pathsCongruent.cases; auto)
using equality_contcrete_to_abstract pathsCongruent.Spawn apply blast
done

lemma staticInclusiveStepSound:
  "
\<forall>\<pi>1 \<pi>2 path1 path2.
  env \<pi>1 \<noteq> None \<longrightarrow>
  env \<pi>2 \<noteq> None \<longrightarrow>
  pathsCongruent \<pi>1 path1 \<longrightarrow> 
  pathsCongruent \<pi>2 path2 \<longrightarrow> 
  staticInclusive path1 path2 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> (Stt e empty [])], {}) (env, H) \<Longrightarrow>
(env, H) \<rightarrow> (E', H') \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
pathsCongruent \<pi>1 path1 \<Longrightarrow> 
pathsCongruent \<pi>2 path2 \<Longrightarrow>
staticInclusive path1 path2 
"
proof ((case_tac "path1 = []"; (simp add: Prefix1)), (case_tac "path2 = []", (simp add: Prefix2)))
  assume 
    H1:
  "
      \<forall>\<pi>1. (\<exists>y. env \<pi>1 = Some y) \<longrightarrow>
      (\<forall>\<pi>2. (\<exists>y. env \<pi>2 = Some y) \<longrightarrow>
      (\<forall>path1. pathsCongruent \<pi>1 path1 \<longrightarrow>
      (\<forall>path2. pathsCongruent \<pi>2 path2 \<longrightarrow> 
        staticInclusive path1 path2)))" and
    H2: "star_left op \<rightarrow> ([[] \<mapsto> (Stt e empty [])], {}) (env, H)" and
    H3: "(env, H) \<rightarrow> (E', H')" and
    H4: "\<exists>y. E' \<pi>1 = Some y" and
    H5: "\<exists>y. E' \<pi>2 = Some y " and
    H6: "pathsCongruent \<pi>1 path1" and
    H7: "pathsCongruent \<pi>2 path2" and
    H8: "path1 \<noteq> []" and 
    H9: "path2 \<noteq> []"

  obtain \<sigma>1 where 
    H10: "E' \<pi>1 = Some \<sigma>1"
    using H4 by blast

  obtain \<sigma>2 where 
    H11: "E' \<pi>2 = Some \<sigma>2"
    using H5 by blast

  from H6
  obtain \<pi>1x l1 path1x n1 where
    H12: "\<pi>1x @ [l1] = \<pi>1" and
    H13: "path1x @ [n1] = path1" and
    H14: "pathsCongruent \<pi>1x path1x"
    apply (rule pathsCongruent.cases)
    using H8 by blast+

  from H7
  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x @ [l2] = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "pathsCongruent \<pi>2x path2x"
    apply (rule pathsCongruent.cases)
    using H9 by blast+
 
  have H22: "pathsCongruent (\<pi>1x @ [l1]) (path1x @ [n1])"
    by (simp add: H12 H13 H6)

  have H23: "pathsCongruent (\<pi>2x @ [l2]) (path2x @ [n2])"
    by (simp add: H15 H16 H7)

  show "staticInclusive path1 path2"
  proof cases
    assume L1H1: "leaf env \<pi>1x"
    obtain \<sigma>1x where
      L1H2: "env \<pi>1x = Some \<sigma>1x" using L1H1 leaf.simps by auto
    show "staticInclusive path1 path2"
    proof cases
      assume L2H1: "leaf env \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "env \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto


      have L2H4: "\<not> strict_prefix \<pi>1x \<pi>2x"
        by (meson L1H1 L2H1 leaf.cases)
      have L2H5: "\<not> strict_prefix \<pi>2x \<pi>1x"
        by (meson L1H1 L2H1 leaf.cases)

      have L2H6: "\<not> strict_prefix path1x path2x"
        using H14 H17 L2H4 strict_prefix_abstract_to_concrete by auto
      have L2H7: "\<not> strict_prefix path2x path1x"
        using H14 H17 L2H5 strict_prefix_abstract_to_concrete by blast

      have L2H8: "staticInclusive path1x path2x"
        using H1 H14 H17 L1H2 L2H2 by blast

      show "staticInclusive path1 path2"
      proof cases
        assume L3H1: "path1x = path2x"

        have L3H3:
  "
          l1 = l2 \<or> 
          (\<exists> x . l1 = (LNxt x) \<and> l2 = (LSpwn x)) \<or>
          (\<exists> x . l1 = (LSpwn x) \<and> l2 = (LNxt x))"
          using 
            H10 H11 H12 H14 H15 H16 H3 H7 L1H1 L2H4 L3H1
            strict_prefix_abstract_to_concrete 
            prefix_snoc spawn_point strict_prefixI' strict_prefix_def
          by smt

        have L3H4:
  "
          n1 = n2 \<or> 
          (\<exists> x . n1 = (IdBind x, ENext) \<and> n2 = (IdBind x, ESpawn )) \<or>
          (\<exists> x . n1 = (IdBind x, ESpawn ) \<and> n2 = (IdBind x, ENext))" 
          by (metis H12 H13 H14 H15 H16 H17 H6 H7 L3H1 L3H3 append1_eq_conv equality_abstract_to_concrete equality_contcrete_to_abstract spawn_pointPreservedDynamicEval_under_congruent_paths)

        have L3H5: "staticInclusive (path1x @ [n1]) (path1x @ [n2])"
          using L3H4 staticInclusive.intros(3) staticInclusive.intros(4) Prefix1 by blast
        show "staticInclusive path1 path2"
          using H13 H16 L3H1 L3H5 by auto
      next
        assume L3H1: "path1x \<noteq> path2x"
        show "staticInclusive path1 path2"
          using H13 H16 L2H6 L2H7 L2H8 L3H1 staticInclusivePreservedDynamicEvalUnordDoubExt strict_prefixI by blast
      qed
    next
      assume L2H1: "\<not> leaf env \<pi>2x"
      have L2H2: "env \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_statePreservedDynamicEval_for_non_leaf by blast
      have L2H3: "staticInclusive path1x path2"
        using H1 H14 H7 L1H2 L2H2 by blast

      have L2H8: "\<not> strict_prefix \<pi>1x \<pi>2"
        by (metis L1H1 L2H2 leaf.cases option.distinct(1))
      have L2H9: "\<not> strict_prefix path1x path2"
        using H14 H7 L2H8 strict_prefix_abstract_to_concrete by blast
      show "staticInclusive path1 path2"
        by (metis H13 L2H3 L2H9 Prefix2 staticInclusivePreservedDynamicEvalUnordExt prefix_prefix strict_prefix_def)
    qed

  next
    assume L1H1: "\<not> leaf env \<pi>1x"
      have L1H2: "env \<pi>1 = Some \<sigma>1"
        using H10 H12 H3 L1H1 path_statePreservedDynamicEval_for_non_leaf by blast
    show "staticInclusive path1 path2"

    proof cases
      assume L2H1: "leaf env \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "env \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have L2H3: "staticInclusive path1 path2x"
        using H1 H17 H6 L1H2 L2H2 by blast
      have L2H8: "\<not> strict_prefix \<pi>2x \<pi>1"
        by (metis L1H2 L2H1 leaf.cases option.distinct(1))
      have L2H9: "\<not> strict_prefix path2x path1"
        using H17 H6 L2H8 strict_prefix_abstract_to_concrete by auto
      show "staticInclusive path1 path2"
        by (metis H16 L2H3 L2H9 Prefix1 staticInclusiveCommut staticInclusivePreservedDynamicEvalUnordExt prefix_order.dual_order.not_eq_order_implies_strict prefix_prefix)
    next
      assume L2H1: "\<not> leaf env \<pi>2x"
      have L2H2: "env \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_statePreservedDynamicEval_for_non_leaf by blast
      show "staticInclusive path1 path2"
        using H1 H6 H7 L1H2 L2H2 by blast
    qed
  qed
qed

lemma staticInclusiveSound:
  "
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow>
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow>
  pathsCongruent \<pi>1 path1 \<Longrightarrow>
  pathsCongruent \<pi>2 path2 \<Longrightarrow>
  staticInclusive path1 path2
"
proof -
  assume
    H1: "star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "pathsCongruent \<pi>1 path1" and
    H5: "pathsCongruent \<pi>2 path2"

  from H1 have
    "star_left (op \<rightarrow>) ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')" by (simp add: star_implies_star_left)
  
  then obtain X0 X' where 
    H6: "X0 = ([[] \<mapsto> (Stt e empty [])], {})" 
        "X' = (\<E>', H')" and
    H7: "star_left (op \<rightarrow>) X0 X'" by auto

  from H7 have 
    H8:
  "
      \<forall> \<E>' H' \<pi>1 \<pi>2 path1 path2.
      X0 = ([[] \<mapsto> (Stt e empty [])], {}) \<longrightarrow> X' = (\<E>', H') \<longrightarrow>
      \<E>' \<pi>1 \<noteq> None \<longrightarrow>
      \<E>' \<pi>2 \<noteq> None \<longrightarrow>
      pathsCongruent \<pi>1 path1 \<longrightarrow>
      pathsCongruent \<pi>2 path2 \<longrightarrow>
      staticInclusive path1 path2
    "
  proof induction
    case (refl z)
    then show ?case
      using staticInclusiveBaseSound by blast
  next
    case (step x y z)

    {
      fix \<E>' H' \<pi>1 \<pi>2 path1 path2
      assume 
        L2H1: "x = ([[] \<mapsto> (Stt e empty [])], {})" and
        L2H2: "z = (\<E>', H')" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "pathsCongruent \<pi>1 path1" and
        L2H6: "pathsCongruent \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8:
  "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          pathsCongruent \<pi>1 path1 \<longrightarrow> 
          pathsCongruent \<pi>2 path2 \<longrightarrow> 
          staticInclusive path1 path2 "
        by blast

      have 
        "staticInclusive path1 path2"
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 staticInclusiveStepSound step.hyps(1) step.hyps(2) by blast
    }
    then show ?case by blast
  qed

  from H2 H3 H4 H5 H6(1) H6(2) H8 show 
    "staticInclusive path1 path2" by blast
qed


lemma is_send_path_implies_nonempty_pool:
  "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2:
  "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some ((Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>n) \<rho> \<kappa>)) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed

lemma is_recv_path_implies_nonempty_pool:
  "
  is_recv_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_recv_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2:
  "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some ((Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>n) \<rho> \<kappa>)) 
    " using is_recv_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed

inductive 
  staticFlowsAcceptEnv :: "static_env \<Rightarrow> flow_set \<Rightarrow> env \<Rightarrow> bool"  and
  staticFlowsAcceptVal :: "static_env \<Rightarrow> flow_set \<Rightarrow> val \<Rightarrow> bool"
where
  Intro:
  "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>  staticFlowsAcceptVal V F \<omega> \<Longrightarrow>
    staticFlowsAcceptEnv V F \<rho>
  "
| Unit:
  "
    staticFlowsAcceptVal V F VUnt
  "
| Chan:
  "
    staticFlowsAcceptVal V F (VChn c)
  "
| SendEvt:
  "
    staticFlowsAcceptEnv V F \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F (VClsr (SendEvt _ _) \<rho>)
  "
| RecvEvt:
  "
    staticFlowsAcceptEnv V F \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F (VClsr (RecvEvt _) \<rho>)
  "
| Left:
  "
    staticFlowsAcceptEnv V F \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F (VClsr (Lft _) \<rho>)
  "
| Right:
  "
    staticFlowsAcceptEnv V F \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F (VClsr (Rht _) \<rho>)
  "
| Fun:
  "
    staticFlowsAccept V F e \<Longrightarrow> 
    staticFlowsAcceptEnv V F  \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F (VClsr (Fun f x e) \<rho>)
  "
| Pair:
  "
    staticFlowsAcceptEnv V F \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F (VClsr (Pair _ _) \<rho>)
  " 


inductive staticFlowsAcceptStack :: "static_env \<Rightarrow> flow_set \<Rightarrow> name \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty: "staticFlowsAcceptStack V F y []"
| Nonempty:
  "
    \<lbrakk> 
      {(IdRslt y, EReturn, tmId e)} \<subseteq> F;
      staticFlowsAccept V F e;
      staticFlowsAcceptEnv V F \<rho>;
      staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>
    \<rbrakk> \<Longrightarrow> 
    staticFlowsAcceptStack V F y ((Ctn x e \<rho>) # \<kappa>)
  "

inductive staticFlowsAcceptPool :: "static_env \<Rightarrow> flow_set \<Rightarrow> trace_pool \<Rightarrow> bool"  where
  Intro:
  "
    (\<forall> \<pi> e \<rho> \<kappa> . E \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow> 
      staticFlowsAccept V F e \<and>
      staticFlowsAcceptEnv V F \<rho> \<and>
      staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>) \<Longrightarrow> 
    staticFlowsAcceptPool V F E
  "

lemma staticFlowsAcceptPoolPreservedReturnEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow>
  \<E>m pi = Some (Stt (Rslt x) env (Ctn xk ek envk # k)) \<Longrightarrow> 
  env x = Some v \<Longrightarrow> 
  staticFlowsAcceptPool V F (\<E>m(pi @ [LRtn x] \<mapsto> (Stt ek (envk(xk \<mapsto> v)) k)))
"
proof -
assume 
 H1: "staticFlowsAcceptPool V F \<E>m" and
 H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
 H3: "leaf \<E>m pi" and
 H4: "\<E>m pi = Some (Stt (Rslt x) env (Ctn xk ek envk # k))" and
 H5: "env x = Some v"


 have 
  H6: " 
    \<forall>\<pi> e \<rho> \<kappa>.
    \<E>m \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
    staticFlowsAccept V F e \<and> staticFlowsAcceptEnv V F \<rho> \<and> staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>"
  using H1 staticFlowsAcceptPool.cases by blast 

  have 
    H7: "staticFlowsAccept V F (Rslt x)" by (simp add: staticFlowsAccept.Result)
  have
     H8: "staticFlowsAcceptEnv V F env" using H4 H6 by blast
  have
     H9: "staticFlowsAcceptStack V F x ((Ctn xk ek envk) # k)" using H4 H6 by fastforce

  have 
    H10: "staticFlowsAccept V F ek \<and> staticFlowsAcceptEnv V F envk \<and> staticFlowsAcceptStack V F (\<lfloor>ek\<rfloor>) k" 
    using H9 proof cases
    case Nonempty
    then show ?thesis by blast
  qed


 show "staticFlowsAcceptPool V F (\<E>m(pi @ [LRtn x] \<mapsto> (Stt ek (envk(xk \<mapsto> v)) k)))"
   using H1 H10 H5 H8 staticFlowsAcceptEnv.simps staticFlowsAcceptPool.simps by auto
qed


lemma staticFlowsAcceptPoolPreservedSeqEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow>
  \<E>m pi = Some (Stt (Bind x b e) env k) \<Longrightarrow> 
  seqEval b env v \<Longrightarrow> 
  staticFlowsAcceptPool V F (\<E>m(pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> v)) k)))
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "leaf \<E>m pi" and
    H4: "\<E>m pi = Some (Stt (Bind x b e) env k)" and 
    H5: "seqEval b env v"

  have H6:
  "
    \<forall>\<pi> e \<rho> \<kappa>.
    \<E>m \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
    staticFlowsAccept V F e \<and> staticFlowsAcceptEnv V F \<rho> \<and> staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>"
  using H1 staticFlowsAcceptPool.cases by blast 

  have 
    H7: "staticFlowsAccept V F (Bind x b e)"
    using H4 H6 by auto
  have
     H8: "staticFlowsAcceptEnv V F env"
    using H4 H6 by blast
  have
     H9: "staticFlowsAcceptStack V F (\<lfloor>Bind x b e\<rfloor>) k"
    using H4 H6 by fastforce

  have H10: 
    "staticFlowsAccept V F e" using H7 staticFlowsAccept.cases by blast

  show "staticFlowsAcceptPool V F (\<E>m(pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> v)) k)))"
  using H5
  proof cases
    case UNIT
    then show ?thesis
    using H1 H10 H8 H9 staticFlowsAcceptEnv.simps 
      staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit 
      staticFlowsAcceptPool.simps by auto
  next
    case (PRIM p)

    have L1H1: "staticFlowsAcceptVal V F (VClsr p env)" 
    proof (cases p)
      case (SendEvt x11 x12)
      then show ?thesis
        by (simp add: H8 staticFlowsAcceptEnv_staticFlowsAcceptVal.SendEvt)
    next
      case (RecvEvt x2)
      then show ?thesis
        by (simp add: H8 staticFlowsAcceptEnv_staticFlowsAcceptVal.RecvEvt)
    next
      case (Pair x31 x32)
      then show ?thesis
        by (simp add: H8 staticFlowsAcceptEnv_staticFlowsAcceptVal.Pair)
    next
      case (Lft x4)
      then show ?thesis
        by (simp add: H8 Left)
    next
      case (Rht x5)
      then show ?thesis
        by (simp add: H8 Right)
    next
      case (Fun f' x' e')
      have L2H1: "staticFlowsAccept V F (Bind x (Atom (Fun f' x' e')) e)"
        using H7 local.Fun local.PRIM(1) by auto
      show ?thesis using L2H1
      proof cases
        case BindFun
        then show ?thesis
        by (simp add: H8 local.Fun staticFlowsAcceptEnv_staticFlowsAcceptVal.Fun)
      qed
    qed

    have L1H2: "staticFlowsAcceptEnv V F (env(x \<mapsto> v))"
      using H8 L1H1 local.PRIM(2) staticFlowsAcceptEnv.simps by auto
    show ?thesis
      using H10 H6 H9 L1H2 staticFlowsAcceptPool.simps by auto
  next
    case (FST xp x1 x2 envp)

    have L1H1: "staticFlowsAcceptVal V F (VClsr (atom.Pair x1 x2) envp)" 
    using H8 staticFlowsAcceptEnv.cases
          using FST(2) by blast

    have L1H2: "staticFlowsAcceptEnv V F envp" using L1H1 
    proof cases
      case Pair
      then show ?thesis by auto
    qed

    have L1H3: "staticFlowsAcceptVal V F v"
      using L1H2 local.FST(3) staticFlowsAcceptEnv.cases by blast

    have L1H4: "staticFlowsAcceptEnv V F (env(x \<mapsto> v))"
      using H8 L1H3 staticFlowsAcceptEnv.simps by auto

    show ?thesis using H10 H6 H9 L1H4 staticFlowsAcceptPool.intros by auto
  next
    case (SND xp x1 x2 envp)
    have L1H1: "staticFlowsAcceptVal V F (VClsr (atom.Pair x1 x2) envp)" 
    using H8 staticFlowsAcceptEnv.cases
          using SND(2) by blast

    have L1H2: "staticFlowsAcceptEnv V F envp" using L1H1 
    proof cases
      case Pair
      then show ?thesis by auto
    qed

    have L1H3: "staticFlowsAcceptVal V F v"
      using L1H2 SND(3) staticFlowsAcceptEnv.cases by blast

    have L1H4: "staticFlowsAcceptEnv V F (env(x \<mapsto> v))"
      using H8 L1H3 staticFlowsAcceptEnv.simps by auto

    show ?thesis using H10 H6 H9 L1H4 staticFlowsAcceptPool.intros by auto
  qed
qed


lemma staticFlowsAcceptPoolPreservedCallEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow>
  \<E>m pi = Some (Stt (Bind x b e) env k) \<Longrightarrow>
  callEval (b, env) (e', env') \<Longrightarrow> 
  staticFlowsAcceptPool V F (\<E>m(pi @ [LCall x] \<mapsto> (Stt e' env' ((Ctn x e env) # k))))
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "leaf \<E>m pi" and
    H4: "\<E>m pi = Some (Stt (Bind x b e) env k)" and
    H5: "callEval (b, env) (e', env')"

  have H6:
  "
    \<forall>\<pi> e \<rho> \<kappa>.
    \<E>m \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
    staticFlowsAccept V F e \<and> staticFlowsAcceptEnv V F \<rho> \<and> staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>"
  using H1 staticFlowsAcceptPool.cases by blast 

  have 
    H7: "staticFlowsAccept V F (Bind x b e)"
  using H4 H6 by blast

  have
     H8: "staticFlowsAcceptEnv V F env"
    using H4 H6 by blast
  have
     H9: "staticFlowsAcceptStack V F (\<lfloor>Bind x b e\<rfloor>) k"
    using H4 H6 by fastforce

  have H10: 
    "staticFlowsAccept V F e" using H7 staticFlowsAccept.cases by blast

  show "staticFlowsAcceptPool V F (\<E>m(pi @ [LCall x] \<mapsto> (Stt e' env' ((Ctn x e env) # k))))"
  using H5
  proof cases
    case (CaseLft xs xl' envl vl xl xr er)

    have L1H1: "staticFlowsAcceptVal V F (VClsr (Lft xl') envl)"
      using H8 local.CaseLft(3) staticFlowsAcceptEnv.cases by blast

    have L1H2: "staticFlowsAcceptEnv V F envl"
    using L1H1 
    proof cases
      case Left
      then show ?thesis by auto
    qed

    have L1H3: "staticFlowsAcceptVal V F vl"
    using L1H2  local.CaseLft(4) staticFlowsAcceptEnv.cases by blast

    have L1H4: "staticFlowsAcceptEnv V F env'"
    using H8 L1H2 local.CaseLft(2) local.CaseLft(4) staticFlowsAcceptEnv.simps by auto

    have L1H5: "staticFlowsAccept V F (Bind x (Case xs xl e' xr er) e)"
      using H7 local.CaseLft(1) by blast

    have L1H6: "staticFlowsAccept V F e'"
    using L1H5 
    proof cases
      case BindCase
      then show ?thesis
        by blast
    qed


    have L1H7: "{(IdRslt (\<lfloor>e'\<rfloor>), EReturn, tmId e)} \<subseteq> F" 
    using L1H5 proof cases
      case BindCase
      then show ?thesis by blast
    qed
    have L1H8: "staticFlowsAcceptStack V F (\<lfloor>e'\<rfloor>) (Ctn x e env # k)"
      using H10 H8 H9 L1H7 staticFlowsAcceptStack.Nonempty by auto

    show ?thesis by (simp add: H6 L1H4 L1H6 L1H8 staticFlowsAcceptPool.intros)



  next
    case (CaseRht xs xr' envr vr xl el xr)
    have L1H1: "staticFlowsAcceptVal V F (VClsr (Rht xr') envr)"
      using H8 local.CaseRht(3) staticFlowsAcceptEnv.cases by blast

    have L1H2: "staticFlowsAcceptEnv V F envr"
    using L1H1 
    proof cases
      case Right
      then show ?thesis by auto
    qed

    have L1H3: "staticFlowsAcceptVal V F vr"
    using L1H2  local.CaseRht(4) staticFlowsAcceptEnv.cases by blast

    have L1H4: "staticFlowsAcceptEnv V F env'"
    using H8 L1H2 local.CaseRht(2) local.CaseRht(4) staticFlowsAcceptEnv.simps by auto

    have L1H5: "staticFlowsAccept V F (Bind x (Case xs xl el xr e') e)"
      using H7 local.CaseRht(1) by blast

    have L1H6: "staticFlowsAccept V F e'"
    using L1H5 
    proof cases
      case BindCase
      then show ?thesis
        by blast
    qed

    have L1H7: "{(IdRslt (\<lfloor>e'\<rfloor>), EReturn, tmId e)} \<subseteq> F" 
    using L1H5 proof cases
      case BindCase
      then show ?thesis by blast
    qed
    have L1H8: "staticFlowsAcceptStack V F (\<lfloor>e'\<rfloor>) (Ctn x e env # k)"
      using H10 H8 H9 L1H7 staticFlowsAcceptStack.Nonempty by auto

    show ?thesis by (simp add: H6 L1H4 L1H6 L1H8 staticFlowsAcceptPool.intros)

  next
    case (App f fp xp envl xa va)

    have L1H1: "staticFlowsAcceptVal V F (VClsr (Fun fp xp e') envl)"
      using H8 local.App(3) staticFlowsAcceptEnv.cases by blast


    have L1H2: "staticFlowsAccept V F e'"
    using L1H1 proof cases
      case Fun
      then show ?thesis
        by simp
    qed

    have L1H3: "staticFlowsAcceptEnv V F envl"
    using L1H1 proof cases
      case Fun
      then show ?thesis
        by simp
    qed


    have L1H4: "staticFlowsAcceptVal V F va"
      using H8 local.App(4) staticFlowsAcceptEnv.cases by blast

    have L1H5: "staticFlowsAcceptEnv V F env'"
      using H8 L1H3 local.App(2) local.App(3) local.App(4) staticFlowsAcceptEnv.simps by auto


    have L1H6: "staticFlowsAccept V F (Bind x (App f xa) e)" using H7 local.App(1) by auto

    have L1H7: "staticFlowsAccept V F e'"
    using L1H6
    proof cases
      case BindApp
      then show ?thesis using L1H2 by blast
    qed

    have L1H7: "{(IdRslt (\<lfloor>e'\<rfloor>), EReturn, tmId e)} \<subseteq> F" 
    using L1H6 proof cases
      case BindApp
      then show ?thesis
        using H2 H4 local.App(3) staticEvalPoolSoundSnapshot by fastforce
    qed

    have L1H8: "staticFlowsAcceptStack V F (\<lfloor>e'\<rfloor>) (Ctn x e env # k)"
      using H10 H8 H9 L1H7 staticFlowsAcceptStack.Nonempty by auto

    show ?thesis
      by (simp add: H6 L1H2 L1H5 L1H8 staticFlowsAcceptPool.intros)
  qed
qed

lemma staticFlowsAcceptPoolPreservedMkChnEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow> 
  \<E>m pi = Some (Stt (Bind x MkChn e) env k) \<Longrightarrow> 
  staticFlowsAcceptPool V F (\<E>m(pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> VChn (Ch pi x))) k)))
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "leaf \<E>m pi" and
    H4: "\<E>m pi = Some (Stt (Bind x MkChn e) env k)"

  have H6:
  "
    \<forall>\<pi> e \<rho> \<kappa>.
    \<E>m \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
    staticFlowsAccept V F e \<and> staticFlowsAcceptEnv V F \<rho> \<and> staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>"
  using H1 staticFlowsAcceptPool.cases by blast 

  have 
    H7: "staticFlowsAccept V F (Bind x MkChn e)"
  using H4 H6 by blast


  have
     H8: "staticFlowsAcceptEnv V F env"
    using H4 H6 by blast
  have
     H9: "staticFlowsAcceptStack V F (\<lfloor>Bind x MkChn e\<rfloor>) k"
    using H4 H6 by blast

  have H10: 
    "staticFlowsAccept V F e" using H7 staticFlowsAccept.cases by blast

  show "staticFlowsAcceptPool V F (\<E>m(pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> VChn (Ch pi x))) k)))"
    using H10 H6 H8 H9 staticFlowsAcceptEnv.simps 
    staticFlowsAcceptEnv_staticFlowsAcceptVal.Chan 
    staticFlowsAcceptPool.simps by auto

qed

lemma staticFlowsAcceptPoolPreservedSpawnEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow> 
  \<E>m pi = Some (Stt (Bind x (Spwn ec) e) env k) \<Longrightarrow> 
  staticFlowsAcceptPool V F (\<E>m(pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> VUnt)) k), pi @ [LSpwn x] \<mapsto> (Stt ec env [])))
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "leaf \<E>m pi" and
    H4: "\<E>m pi = Some (Stt (Bind x (Spwn ec) e) env k)"

  have H6:
  "
    \<forall>\<pi> e \<rho> \<kappa>.
    \<E>m \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
    staticFlowsAccept V F e \<and> staticFlowsAcceptEnv V F \<rho> \<and> staticFlowsAcceptStack V F (\<lfloor>e\<rfloor>) \<kappa>"
  using H1 staticFlowsAcceptPool.cases by blast 

  have 
    H7: "staticFlowsAccept V F (Bind x (Spwn ec) e)"
  using H4 H6 by blast


  have
     H8: "staticFlowsAcceptEnv V F env"
    using H4 H6 by blast
  have
     H9: "staticFlowsAcceptStack V F (\<lfloor>Bind x (Spwn ec) e\<rfloor>) k"
    using H4 H6 by blast

  have H10: "staticFlowsAccept V F e" using H7 staticFlowsAccept.cases by blast


  have 
    H11: "staticFlowsAccept V F ec" using H7 staticFlowsAccept.cases by blast

  have 
    H12: "staticFlowsAcceptVal V F VUnt"
    by (simp add: staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit)

  have 
    H13: "staticFlowsAcceptStack V F (\<lfloor>Bind x (Spwn ec) e\<rfloor>) []"
    by (simp add: staticFlowsAcceptStack.Empty) 

  have H14: "staticFlowsAcceptEnv V F (env(x \<mapsto> VUnt))"
    using H12 H8 staticFlowsAcceptEnv.simps by auto

  show ?thesis
    using H10 H11 H13 H14 H6 H8 H9 staticFlowsAcceptPool.simps by (simp add: staticFlowsAcceptStack.Empty)

qed


lemma staticFlowsAcceptPoolPreservedSyncEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pis \<Longrightarrow>
  \<E>m pis = Some (Stt (Bind xs (Sync xse) es) envs ks) \<Longrightarrow>
  envs xse = Some (VClsr (SendEvt xsc xm) envse) \<Longrightarrow>
  leaf \<E>m pir \<Longrightarrow>
  \<E>m pir = Some (Stt (Bind xr (Sync xre) er) envr kr) \<Longrightarrow>
  envr xre = Some (VClsr (RecvEvt xrc) envre) \<Longrightarrow>
  envse xsc = Some (VChn c) \<Longrightarrow>
  envre xrc = Some (VChn c) \<Longrightarrow> 
  envse xm = Some vm \<Longrightarrow> 
  staticFlowsAcceptPool V F 
    (\<E>m(pis @ [LNxt xs] \<mapsto> (Stt es (envs(xs \<mapsto> VUnt)) ks), pir @ [LNxt xr] \<mapsto> (Stt er (envr(xr \<mapsto> vm)) kr)))
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "leaf \<E>m pis" and
    H4: "\<E>m pis = Some (Stt (Bind xs (Sync xse) es) envs ks)" and
    H5: "envs xse = Some (VClsr (SendEvt xsc xm) envse)" and
    H6: "leaf \<E>m pir" and
    H7: "\<E>m pir = Some (Stt (Bind xr (Sync xre) er) envr kr)" and
    H8: "envr xre = Some (VClsr (RecvEvt xrc) envre)" and
    H9: "envse xsc = Some (VChn c)" and
    H10: "envre xrc = Some (VChn c)" and 
    H11: "envse xm = Some vm"

  have H12:
  "
    \<forall>\<pi> e \<rho> \<kappa>.
    \<E>m \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
    staticFlowsAccept V F e \<and> staticFlowsAcceptEnv V F \<rho> \<and> staticFlowsAcceptStack V F  (\<lfloor>e\<rfloor>) \<kappa>"
  using H1 staticFlowsAcceptPool.cases by blast 

  have H13: "staticFlowsAccept V F (Bind xs (Sync xse) es)"
    using H12 H4 by blast

  have H14: "staticFlowsAcceptEnv V F envs"
    using H12 H4 by blast

  have H15: "staticFlowsAcceptStack V F (\<lfloor>Bind xs (Sync xse) es\<rfloor>) ks"
    using H12 H4 by blast


  have H16: "staticFlowsAccept V F (Bind xr (Sync xre) er)"
  using H12 H7 by blast

  have H17: "staticFlowsAcceptEnv V F envr"
    using H12 H7 by blast

  have H18: "staticFlowsAcceptStack V F (\<lfloor>Bind xr (Sync xre) er\<rfloor>) kr"
  using H12 H7 by blast


  have H19: "staticFlowsAcceptEnv V F (envs(xs \<mapsto> VUnt))"
    using H14 staticFlowsAcceptEnv.simps staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit by auto


  have H20: "staticFlowsAcceptVal V F (VClsr (SendEvt xsc xm) envse)"
    using H14 H5 staticFlowsAcceptEnv.cases by blast

  have H21: "staticFlowsAcceptEnv V F envse"
  using H20 proof cases
    case SendEvt
    then show ?thesis by simp
  qed

  have H22: "staticFlowsAcceptVal V F vm"
    using H11 H21 staticFlowsAcceptEnv.cases by blast

  have H23: "staticFlowsAcceptEnv V F (envr(xr \<mapsto> vm))"
    using H11 H17 H21 staticFlowsAcceptEnv.simps by auto


  have H24: "staticFlowsAcceptEnv V F (envs(xs \<mapsto> VUnt))"
    by (simp add: H19)

  have H27: "staticFlowsAccept V F er"
  using H16 proof cases
    case BindSync
    then show ?thesis by simp
  qed

  have H28: "staticFlowsAccept V F es"
  using H13 proof cases
    case BindSync
    then show ?thesis by simp
  qed


show "staticFlowsAcceptPool V F 
    (\<E>m(pis @ [LNxt xs] \<mapsto> (Stt es (envs(xs \<mapsto> VUnt)) ks), pir @ [LNxt xr] \<mapsto> (Stt er (envr(xr \<mapsto> vm)) kr)))"
  using H12 H23 H24 H15 H16 H27 H28 staticFlowsAcceptPool.intros H18 by auto
qed

lemma staticFlowsAcceptPoolPreservedDynamicEval:
  "
  staticFlowsAcceptPool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  dynamicEval (\<E>m, Hm) (\<E>', H') \<Longrightarrow>
  staticFlowsAcceptPool V F \<E>'
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "dynamicEval (\<E>m, Hm) (\<E>', H')"

  from H3
  show "staticFlowsAcceptPool V F \<E>'"
  proof cases
    case (Seq_Step_Down pi x env xk ek envk k v)
    then show ?thesis using H1 H2 staticFlowsAcceptPoolPreservedReturnEval by blast
  next
    case (Seq_Step pi x b e env k v)
    then show ?thesis using H1 H2 staticFlowsAcceptPoolPreservedSeqEval by auto
  next
    case (Seq_Step_Up pi x b e env k e' env')
    then show ?thesis using H1 H2 staticFlowsAcceptPoolPreservedCallEval by blast
  next
    case (BindMkChn pi x e env k)
    then show ?thesis  using H1 H2 staticFlowsAcceptPoolPreservedMkChnEval by blast
  next
    case (BindSpawn pi x ec e env k)
    then show ?thesis using H1 H2 staticFlowsAcceptPoolPreservedSpawnEval by auto
  next
    case (BindSync pis xs xse es envs ks xsc xm envse pir xr xre er envr kr xrc envre c vm)
    then show ?thesis using H1 H2 staticFlowsAcceptPoolPreservedSyncEval by auto
  qed
qed


lemma staticFlowsAcceptPoolPreserved:
  "
  staticFlowsAcceptPool V F [[] \<mapsto> (Stt e0 empty [])] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (\<E>', H') \<Longrightarrow>
  staticFlowsAcceptPool V F \<E>'
"
proof -
  assume 
    H1: "staticFlowsAcceptPool V F [[] \<mapsto> (Stt e0 empty [])]" and
    H2: "(V, C) \<Turnstile>\<^sub>e e0" and
    H4: "star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (\<E>', H')"

  obtain EH EH' where
    H6: "EH = ([[] \<mapsto> (Stt e0 empty [])], {})" and 
    H7: "EH' = (\<E>', H')" and 
    H8: "star dynamicEval EH EH'"
    by (simp add: H4)

  have H9: "star_left dynamicEval EH EH'"
    by (simp add: H4 H6 H7 star_implies_star_left)

  from H9
  have 
    H10:
  "
    \<forall> \<E>' H' .
    ([[] \<mapsto> (Stt e0 empty [])], {}) = EH \<longrightarrow> staticFlowsAcceptPool V F [[] \<mapsto> (Stt e0 empty [])] \<longrightarrow>
    (\<E>', H') = EH' \<longrightarrow> staticFlowsAcceptPool V F \<E>'" 
  proof induction
    case (refl x)
    then show ?case by blast
  next
    case (step x y z)
    {
      fix \<E>' H'
      assume 
        L1H1: "([[] \<mapsto> (Stt e0 empty [])], {}) = x" and
        L1H2: "staticFlowsAcceptPool V F [[] \<mapsto> (Stt e0 empty [])]" and
        L1H3: "(\<E>', H') = z"

      have L1H4 : "(V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> (Stt e0 empty [])]" by (simp add: H2 staticEval_to_pool)

      have 
        L1H6: "\<forall> \<E>m Hm . (\<E>m, Hm) = y \<longrightarrow> (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<longrightarrow> staticFlowsAcceptPool V F \<E>m"
        using L1H1 L1H2 L1H4 step.IH by blast

      have L1H7: "\<exists> \<E>m Hm . (\<E>m, Hm) = y \<and> (V, C) \<Turnstile>\<^sub>\<E> \<E>m "
        by (metis L1H1 L1H4 eq_fst_iff star_left_implies_star staticEvalPreserved step.hyps(1))

      have L1H8: "staticFlowsAcceptPool V F \<E>'"
        using L1H3 L1H6 L1H7 staticFlowsAcceptPoolPreservedDynamicEval step.hyps(2) by auto
    }

    then show ?case 
      by blast
  qed

  show "staticFlowsAcceptPool V F \<E>'"
    using H1 H10 H2 H6 H7 by blast

qed


lemma staticFlowsAcceptToPool:
  "
  staticFlowsAccept V F e \<Longrightarrow>
  staticFlowsAcceptPool V F [[] \<mapsto> (Stt e empty [])]
"
apply (rule staticFlowsAcceptPool.intros; auto)
apply (simp add: staticFlowsAcceptEnv_staticFlowsAcceptVal.Intro)
apply (simp add: staticFlowsAcceptStack.Empty)
done

lemma staticFlowsAcceptSoundSeqEval:
   assumes
     H1: "staticFlowsAccept V F (Bind x b e')" and
     H3: "seqEval b env v"

   shows "{(IdBind x, ENext, tmId e')} \<subseteq> F"
using H1
proof cases
  case BindUnit
  then show ?thesis by blast
next
  case BindMkChn
  then show ?thesis by simp
next
  case (BindSendEvt x\<^sub>c x\<^sub>m)
  then show ?thesis by simp
next
  case (BindRecvEvt x\<^sub>c)
  then show ?thesis by simp
next
  case (BindPair x\<^sub>1 x\<^sub>2)
  then show ?thesis by simp
next
  case (BindLeft x\<^sub>p)
  then show ?thesis by simp
next
  case (BindRight x\<^sub>p)
  then show ?thesis by simp
next
  case (BindFun e\<^sub>b f x\<^sub>p)
  then show ?thesis by simp
next
  case (BindSpawn e\<^sub>c)
  then show ?thesis by simp
next
  case (BindSync xSE)
  then show ?thesis by simp
next
  case (BindFst x\<^sub>p)
  then show ?thesis by simp
next
  case (BindSnd x\<^sub>p)
  then show ?thesis by simp
next
  case (BindCase e\<^sub>l e\<^sub>r x\<^sub>s x\<^sub>l x\<^sub>r)
  have "b \<noteq> Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r" using seqEval.cases H3 by blast
  then show ?thesis using local.BindCase(1) by blast
next
  case (BindApp f x\<^sub>a)
  have "b \<noteq> App f x\<^sub>a" using H3 seqEval.simps by auto
  then show ?thesis by (simp add: local.BindApp(1))
qed

lemma staticTraceablePoolSoundDynamicEval:
  assumes
    H1: "star_left dynamicEval EH EHm" and
    H2: "dynamicEval EHm EH'" and
    H3: "EH = ([[] \<mapsto> (Stt e empty [])], {})" and
    H4: "EH' = (E', H')" and
    H5: "E' \<pi>' = Some (Stt e' \<rho>' \<kappa>')" and
    H6: "staticFlowsAcceptPool V F E'" and
    H7: "isEnd (tmId e')" and
    H8: "(V, C) \<Turnstile>\<^sub>e e" and
    IH:
  "
    \<forall>E' H' \<pi>' e' \<rho>' \<kappa>' isEnd.
       EH = ([[] \<mapsto> (Stt e empty [])], {}) \<longrightarrow>
       EHm = (E', H') \<longrightarrow>
       E' \<pi>' = Some (Stt e' \<rho>' \<kappa>') \<longrightarrow>
       staticFlowsAcceptPool V F E' \<longrightarrow> isEnd (tmId e') \<longrightarrow> 
      (\<exists>path. pathsCongruent \<pi>' path \<and> staticTraceable F (tmId e) isEnd path)"
  shows
    "(\<exists>path. pathsCongruent \<pi>' path \<and> staticTraceable F (tmId e) isEnd path)"
proof -
  show ?thesis
  using H2
  proof cases
    case (Seq_Step_Down Em pi x env xk ek envk k v Hm)

    have L1H2: "staticFlowsAcceptPool V F Em" by (smt H2 H4 H6 local.Seq_Step_Down(1) mappingPreserved star_step1 staticFlowsAcceptPool.simps)

    have L1H3: "\<exists>path. pathsCongruent pi path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Rslt x)) path"
    by (simp add: H3 IH L1H2 local.Seq_Step_Down)

    obtain p where 
      L1H4: "pathsCongruent pi p" and
      L1H5: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Rslt x)) p"
    using L1H3 by blast

    show ?thesis
    proof cases
      assume L2H1: "\<pi>' = pi @ [LRtn x]"

      have L2H2: "staticFlowsAcceptStack V F (\<lfloor>Rslt x\<rfloor>) ((Ctn xk ek envk) # k)" 
      using local.Seq_Step_Down(4) L1H2 staticFlowsAcceptPool.cases by blast
   
      have L2H4: "{(IdRslt x, EReturn, (tmId ek))} \<subseteq> F"
      using L2H2 proof cases
        case Nonempty
        then show ?thesis by simp
      qed

      have L2H5: "ek = e'" using H4 H5 L2H1 local.Seq_Step_Down(2) by auto

      have L2H5: "{(IdRslt x, EReturn, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by auto
    
      have L2H6: "pathsCongruent (pi @ [LRtn x]) (p @ [(IdRslt x, EReturn)])" by (simp add: L1H4 Return)
      have L2H7: "staticTraceable F (tmId e) isEnd (p @ [(IdRslt x, EReturn)])" using H7 L1H5 L2H5 Step by auto
    
      show ?thesis using L2H1 L2H6 L2H7 by blast
    next
      assume "\<pi>' \<noteq> pi @ [LRtn x]"
      then show ?thesis
      using H3 H4 H5 H7 IH L1H2 local.Seq_Step_Down(1) local.Seq_Step_Down(2) by auto
    qed

  next
    case (Seq_Step Em pim xm bm em env k v Hm)

    have L1H2: "staticFlowsAcceptPool V F Em"
     using H2 H4 H6 local.Seq_Step(1) mappingPreservedDynamicEval staticFlowsAcceptPool.simps by fastforce

    have L1H3: "\<exists>path. pathsCongruent pim path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm bm em)) path"
    by (simp add: H3 IH L1H2 local.Seq_Step(1) local.Seq_Step(4))

    obtain p where 
      L1H4: "pathsCongruent pim p" and
      L1H5: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm bm em)) p"
    using L1H3 by blast

   show ?thesis
    proof cases
      assume L2H1: "\<pi>' = pim @ [LNxt xm]"

      have L2H2: "staticFlowsAccept V F (Bind xm bm em)"
        using L1H2 local.Seq_Step(4) staticFlowsAcceptPool.simps by blast 
   
      have L2H4: "{(IdBind xm, ENext, (tmId em))} \<subseteq> F"
        using H4 H6 L2H2 local.Seq_Step(2) local.Seq_Step(5) map_upd_Some_unfold 
          staticFlowsAcceptSoundSeqEval staticFlowsAcceptPool.simps by fastforce

      have L2H5: "em = e'" using H4 H5 L2H1 local.Seq_Step(2) by auto

      have L2H5: "{(IdBind xm, ENext, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by auto
    
      have L2H6: "pathsCongruent (pim @ [LNxt xm]) (p @ [(IdBind xm, ENext)])" by (simp add: L1H4 Next)
      have L2H7: "staticTraceable F (tmId e) isEnd (p @ [(IdBind xm, ENext)])" using H7 L1H5 L2H5 Step by auto
    
      show ?thesis using L2H1 L2H6 L2H7 by blast
    next
      assume "\<pi>' \<noteq> pim @ [LNxt xm]"
      then show ?thesis using H3 H4 H5 H7 IH L1H2 local.Seq_Step(1) local.Seq_Step(2) by auto
    qed
  next
    case (Seq_Step_Up Em pim xm bm em env k eu env' Hm)

    have L1H2: "staticFlowsAcceptPool V F Em"
      by (smt H2 H4 H6 local.Seq_Step_Up(1) mappingPreserved star_step1 staticFlowsAcceptPool.simps)

    have L1H3: "\<exists>path. pathsCongruent pim path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm bm em)) path"
    by (simp add: H3 IH L1H2 local.Seq_Step_Up(1) local.Seq_Step_Up(4))

    obtain p where 
      L1H4: "pathsCongruent pim p" and
      L1H5: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm bm em)) p"
    using L1H3 by blast

    show ?thesis
    proof cases
      assume L2H1: "\<pi>' = pim @ [LCall xm]"


      have L2H2: "staticFlowsAccept V F (Bind xm bm em)"
        using L1H2 local.Seq_Step_Up(4) staticFlowsAcceptPool.simps by blast

      have L2H5: "{(IdBind xm, ECall, (tmId e'))} \<subseteq> F"
      using Seq_Step_Up(5)
      proof cases
        case (CaseLft xs xl' envl vl xl xr er)
        have L3H1: "staticFlowsAccept V F (Bind xm (Case xs xl eu xr er) em)" using L2H2 local.CaseLft(1) by auto
        have L3H2: "{(IdBind xm, ECall, (tmId eu))} \<subseteq> F"
        using L3H1 proof cases
          case BindCase
          then show ?thesis by blast
        qed
        then show ?thesis using H4 H5 L2H1 local.Seq_Step_Up(2) by auto
      next
        case (CaseRht xs xr' envr vr xl er el)
        have L3H1: "staticFlowsAccept V F (Bind xm (Case xs xl er el eu) em)" using L2H2 local.CaseRht(1) by auto
        have L3H2: "{(IdBind xm, ECall, (tmId eu))} \<subseteq> F"
        using L3H1 proof cases
          case BindCase
          then show ?thesis by blast
        qed
        then show ?thesis using H4 H5 L2H1 local.Seq_Step_Up(2) by auto
      next
        case (App f fp xp envl xa va)
        have L3H1: "staticFlowsAccept V F (Bind xm (App f xa) em)"
          using L2H2 local.App(1) by auto
        have L3H2: "(V, C) \<Turnstile>\<^sub>\<E> Em" using H1 H3 H8 local.Seq_Step_Up(1) star_left_implies_star 
          staticEvalPreserved staticEval_to_pool by fastforce
        have L3H3: "(SAtm (Fun fp xp eu) \<in> V f)"
          using L3H2 local.Seq_Step_Up(4) local.App(3) 
          staticEvalPoolSoundSnapshot valToStaticVal.simps(3) by fastforce

        have L3H2: "{(IdBind xm, ECall, (tmId eu))} \<subseteq> F"
        using L3H1 proof cases
          case BindApp
          then show ?thesis using L3H3 by blast
        qed
        then show ?thesis using H4 H5 L2H1 local.Seq_Step_Up(2) by auto
      qed
    
      have L2H6: "pathsCongruent (pim @ [LNxt xm]) (p @ [(IdBind xm, ENext)])" by (simp add: L1H4 Next)
      have L2H7: "staticTraceable F (tmId e) isEnd (p @ [(IdBind xm, ECall)])" using H7 L1H5 L2H5 Step by auto
    
      show ?thesis using Call L1H4 L2H1 L2H7 by blast
    next
      assume "\<pi>' \<noteq> pim @ [LCall xm]"
      then show ?thesis using H3 H4 H5 H7 IH L1H2 local.Seq_Step_Up(1) local.Seq_Step_Up(2) by auto
    qed
  next
    case (BindMkChn Em pim xm em env k Hm)

    have L1H2: "staticFlowsAcceptPool V F Em"
     using H2 H4 H6 local.BindMkChn(1) mappingPreservedDynamicEval staticFlowsAcceptPool.simps by fastforce

    have L1H3: "\<exists>path. pathsCongruent pim path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm MkChn em)) path"
    by (simp add: H3 IH L1H2 local.BindMkChn(1) local.BindMkChn(4))

    obtain p where 
      L1H4: "pathsCongruent pim p" and
      L1H5: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm MkChn em)) p"
    using L1H3 by blast

   show ?thesis
    proof cases
      assume L2H1: "\<pi>' = pim @ [LNxt xm]"

      have L2H2: "staticFlowsAccept V F (Bind xm MkChn em)"
        using L1H2 local.BindMkChn(4) staticFlowsAcceptPool.simps by blast
   
      have L2H4: "{(IdBind xm, ENext, (tmId em))} \<subseteq> F"
      using L2H2 proof cases
        case BindMkChn
        then show ?thesis by blast
      qed

      have L2H5: "em = e'"
        using H4 H5 L2H1 local.BindMkChn(2) by auto

      have L2H5: "{(IdBind xm, ENext, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by auto
    
      have L2H6: "pathsCongruent (pim @ [LNxt xm]) (p @ [(IdBind xm, ENext)])" by (simp add: L1H4 Next)
      have L2H7: "staticTraceable F (tmId e) isEnd (p @ [(IdBind xm, ENext)])" using H7 L1H5 L2H5 Step by auto
    
      show ?thesis using L2H1 L2H6 L2H7 by blast
    next
      assume "\<pi>' \<noteq> pim @ [LNxt xm]"
      then show ?thesis using H3 H4 H5 H7 IH L1H2 local.BindMkChn(1) local.BindMkChn(2) by auto
    qed
  next
    case (BindSpawn Em pim xm ec em env k Hm)

    have L1H2: "staticFlowsAcceptPool V F Em"
     using H2 H4 H6 local.BindSpawn(1) mappingPreservedDynamicEval staticFlowsAcceptPool.simps by fastforce

    have L1H3: "\<exists>path. pathsCongruent pim path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm (Spwn ec) em)) path"
    by (simp add: H3 IH L1H2 local.BindSpawn(1) local.BindSpawn(4))


    obtain p where 
      L1H4: "pathsCongruent pim p" and
      L1H5: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xm (Spwn ec) em)) p"
    using L1H3 by blast

    have L1H6: "E' = Em(pim @ [LNxt xm] \<mapsto> (Stt em (env(xm \<mapsto> VUnt)) k), pim @ [LSpwn xm] \<mapsto> (Stt ec env []))"
      using H4 local.BindSpawn(2) by blast
    show ?thesis
    proof cases
      assume L2H0: "\<pi>' = pim @ [LSpwn xm]"

      have L2H2: "staticFlowsAccept V F (Bind xm (Spwn ec) em)"
        using L1H2 local.BindSpawn(4) staticFlowsAcceptPool.simps by blast
   
      have L2H4: "{(IdBind xm, ESpawn, (tmId ec))} \<subseteq> F"
      using L2H2 proof cases
        case BindSpawn
        then show ?thesis by blast
      qed

      have L2H5: "ec = e'" using H5 L1H6 L2H0 by auto

      have L2H6: "{(IdBind xm, ESpawn, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by blast
    
      have L2H7: "pathsCongruent (pim @ [LSpwn xm]) (p @ [(IdBind xm, ESpawn)])" by (simp add: L1H4 Spawn)
      have L2H8: "staticTraceable F (tmId e) isEnd (p @ [(IdBind xm, ESpawn)])"
        using H7 L1H5 L2H6 Step by auto
    
      show ?thesis using L2H0 L2H7 L2H8 by auto
    next
      assume L2H0: "\<pi>' \<noteq> pim @ [LSpwn xm]"
      show ?thesis
      proof cases
        assume L2H1: "\<pi>' = pim @ [LNxt xm]"

        have L2H2: "staticFlowsAccept V F (Bind xm (Spwn ec) em)"
          using L1H2 local.BindSpawn(4) staticFlowsAcceptPool.simps by blast
     
        have L2H4: "{(IdBind xm, ENext, (tmId em))} \<subseteq> F"
        using L2H2 proof cases
          case BindSpawn
          then show ?thesis by blast
        qed
  
        have L2H5: "em = e'" using H5 L1H6 L2H1 by auto
  
        have L2H5: "{(IdBind xm, ENext, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by auto
      
        have L2H6: "pathsCongruent (pim @ [LNxt xm]) (p @ [(IdBind xm, ENext)])" by (simp add: L1H4 Next)
        have L2H7: "staticTraceable F (tmId e) isEnd (p @ [(IdBind xm, ENext)])" using H7 L1H5 L2H5 Step by auto
      
        show ?thesis using L2H1 L2H6 L2H7 by blast
      next
        assume L2H1: "\<pi>' \<noteq> pim @ [LNxt xm]"
        show ?thesis using H3 H5 H7 IH L1H2 L1H6 L2H0 L2H1 local.BindSpawn(1) by auto
      qed
    qed
  next
    case (BindSync Em pis xs xse es envs ks xsc xm envse pir xr xre er envr kr xrc envre c vm Hm)

    have L1H2: "staticFlowsAcceptPool V F Em"
      by (smt H2 H4 H6 local.BindSync(1) mappingPreserved star_step1 staticFlowsAcceptPool.simps)

    have L1H3: "\<exists>path. pathsCongruent pir path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xr (Sync xre) er)) path"
    by (simp add: H3 IH L1H2 local.BindSync(1) local.BindSync(7))

    obtain pr where 
      L1H4: "pathsCongruent pir pr" and
      L1H5: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xr (Sync xre) er)) pr"
    using L1H3 by auto

    have L1H6: "\<exists>path. pathsCongruent pis path \<and> staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xs (Sync xse) es)) path"
    by (simp add: H3 IH L1H2 local.BindSync(1) local.BindSync(4))

    obtain ps where 
      L1H7: "pathsCongruent pis ps" and
      L1H8: "staticTraceable F (tmId e) (\<lambda> l . l = tmId (Bind xs (Sync xse) es)) ps"
    using L1H6 by blast


    show ?thesis
    proof cases
      assume L2H0: "\<pi>' = pir @ [LNxt xr]"

      have L2H2: "staticFlowsAccept V F (Bind xr (Sync xre) er)"
      using L1H2 local.BindSync(7) staticFlowsAcceptPool.simps by blast
   

      have L2H4: "{(IdBind xr, ENext, (tmId er))} \<subseteq> F"
      using L2H2 proof cases
        case BindSync
        then show ?thesis by blast
      qed

      have L2H5: "er = e'" using H4 H5 L2H0 local.BindSync(2) by auto

      have L2H6: "{(IdBind xr, ENext, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by auto
    
      have L2H7: "pathsCongruent (pir @ [LNxt xr]) (pr @ [(IdBind xr, ENext)])" by (simp add: L1H4 Next)
      have L2H8: "staticTraceable F (tmId e) isEnd (pr @ [(IdBind xr, ENext)])" using H7 L1H5 L2H6 Step by auto
    
      show ?thesis using L2H0 L2H7 L2H8 by auto
    next
      assume L2H0: "\<pi>' \<noteq> pir @ [LNxt xr]"
      show ?thesis
      proof cases
        assume L2H1: "\<pi>' = pis @ [LNxt xs]"
  
        have L2H2: "staticFlowsAccept V F (Bind xs (Sync xse) es)"
          using L1H2 local.BindSync(4) staticFlowsAcceptPool.simps by blast
     
  
        have L2H4: "{(IdBind xs, ENext, (tmId es))} \<subseteq> F"
        using L2H2 proof cases
          case BindSync
          then show ?thesis by blast
        qed
  
        have L2H5: "es = e'"
          using H4 H5 L2H0 L2H1 local.BindSync(2) by auto
  
        have L2H6: "{(IdBind xs, ENext, (tmId e'))} \<subseteq> F" using L2H4 L2H5 by auto
      
        have L2H7: "pathsCongruent (pis @ [LNxt xs]) (ps @ [(IdBind xs, ENext)])" by (simp add: L1H7 Next)
        have L2H8: "staticTraceable F (tmId e) isEnd (ps @ [(IdBind xs, ENext)])" using H7 L1H8 L2H6 Step by auto
      
        show ?thesis using L2H1 L2H7 L2H8 by blast
      next
        assume L2H1: "\<pi>' \<noteq> pis @ [LNxt xs]"
        show ?thesis using H3 H4 H5 H7 IH L1H2 L2H0 L2H1 local.BindSync(1) local.BindSync(2) by auto
      qed
    qed
  qed
qed

lemma staticTraceablePoolSound':
  assumes
    H1: "star_left dynamicEval EH EH'" and
    H2: "(V, C) \<Turnstile>\<^sub>e e"
  shows "
    \<forall> E' H' \<pi>' e' \<rho>' \<kappa>' isEnd.
    EH = ([[] \<mapsto> (Stt e empty [])], {}) \<longrightarrow> EH' = (E', H') \<longrightarrow>
    E' \<pi>' = Some (Stt e' \<rho>' \<kappa>') \<longrightarrow>
    staticFlowsAcceptPool V F E' \<longrightarrow>
    isEnd (tmId e') \<longrightarrow>
    (\<exists> path . 
      pathsCongruent \<pi>' path \<and>
      staticTraceable F (tmId e) isEnd path)"
using H1
proof induction
  case (refl z)
  then show ?case using pathsCongruent.Empty staticTraceable.Empty by auto
next
  case (step EH EHm EH')
  then show ?case using staticTraceablePoolSoundDynamicEval[of EH EHm EH']
    using H2 by blast
qed

lemma staticTraceablePoolSound:
  assumes
    H1: "\<E>' \<pi>' = Some (Stt (Bind x' b' e\<^sub>n) \<rho>' \<kappa>')" and 
    H2: "star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')" and
    H3: "(V, C) \<Turnstile>\<^sub>e e" and
    H4: "staticFlowsAcceptPool V F \<E>'" and
    H5: "isEnd (IdBind x')"

  shows "
    \<exists> path . 
      pathsCongruent \<pi>' path \<and>
      staticTraceable F (tmId e) isEnd path"
using staticTraceablePoolSound'[of "([[] \<mapsto> (Stt e empty [])], {})" "(\<E>', H')"]
H1 H2 H3 H4 H5 star_implies_star_left by fastforce


lemma staticTraceableSound:
  "
  \<E> \<pi> = Some ((Stt (Bind x b e') \<rho> \<kappa>)) \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (\<E>, H) \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  staticFlowsAccept V F e0 \<Longrightarrow>
  isEnd (IdBind x) \<Longrightarrow>
  \<exists> path . 
    pathsCongruent \<pi> path \<and>
    staticTraceable F (tmId e0) isEnd path
"
by (metis staticFlowsAcceptToPool staticTraceablePoolSound staticFlowsAcceptPoolPreserved)

lemma staticTraceableSendSound:
  "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  \<exists> pathSync .
    (pathsCongruent \<pi>Sync pathSync) \<and> 
    staticTraceable F (tmId e) (staticSendSite V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in staticSendSiteSound; auto?)
 apply (frule staticTraceableSound; auto?)
done

lemma staticTraceableRecvSound:
  "
  is_recv_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  \<exists> pathSync .
    (pathsCongruent \<pi>Sync pathSync) \<and> 
    staticTraceable F (tmId e) (staticRecvSite V e xC) pathSync
"
 apply (unfold is_recv_path.simps; auto)
 apply (frule_tac x\<^sub>r\<^sub>c = xrc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in staticRecvSiteSound; auto?)
 apply (frule staticTraceableSound; auto?)
done

(* END PATH SOUND *)



theorem singular_to_equal:
  "
  forEveryTwo (staticTraceable F (tmId e) (staticSendSite V e xC)) singular \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  forEveryTwo (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: forEveryTwo.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>1 in staticTraceableSendSound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>2 in staticTraceableSendSound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (metis staticInclusiveSound equality_abstract_to_concrete is_send_path_implies_nonempty_pool)
done



theorem noncompetitive_send_to_ordered_send:
  "
  forEveryTwo (staticTraceable F (tmId e) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  forEveryTwo (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: forEveryTwo.simps noncompetitive.simps; auto?)
  using staticTraceableSendSound staticInclusiveSound
  apply (meson is_send_path_implies_nonempty_pool ordered.simps prefix_abstract_to_concrete)
done


lemma noncompetitive_recv_to_ordered_recv:
  "
   forEveryTwo (staticTraceable F (tmId e) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
   staticFlowsAccept V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
   forEveryTwo (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: forEveryTwo.simps noncompetitive.simps; auto?)
  using staticTraceableRecvSound staticInclusiveSound
 apply (meson is_recv_path_implies_nonempty_pool ordered.simps prefix_abstract_to_concrete)
done



theorem staticOneShotSound:
  "
      staticOneShot V e xC \<Longrightarrow>
      one_shot e (Ch \<pi> xC)"
apply (erule staticOneShot.cases; auto)
apply (unfold one_shot.simps; auto)
using singular_to_equal apply blast
done

theorem staticOneToManySound:
  "
      staticOneToMany V e xC \<Longrightarrow>
      fan_out e (Ch \<pi> xC)" 
   apply (erule staticOneToMany.cases; auto)
   apply (unfold fan_out.simps; auto)
  using noncompetitive_send_to_ordered_send apply blast
done

theorem staticManyToOneSound:
  "
      staticManyToOne V e xC \<Longrightarrow>
      fan_in e (Ch \<pi> xC)"
   apply (erule staticManyToOne.cases; auto)
   apply (unfold fan_in.simps)
  using noncompetitive_recv_to_ordered_recv apply fastforce
done

theorem staticOneToOneSound:
  "
      staticOneToOne V e xC \<Longrightarrow>
      one_to_one e (Ch \<pi> xC)"
 apply (erule staticOneToOne.cases; auto)
 apply (unfold one_to_one.simps; auto)
using fan_in.simps fan_out.simps noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send
apply(meson star.refl)
done


end
