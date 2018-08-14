theory Sound_Communication_A
  imports Main Syntax 
    Dynamic_Semantics 
    Static_Semantics
    Sound_Semantics
    Dynamic_Communication
    Static_Communication
    Sound_Communication
    Static_Communication_A

begin

lemma static_inclusive_commut: "
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> static_inclusive path\<^sub>2 path\<^sub>1
"
 apply (erule static_inclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
done


lemma static_inclusive_preserved_under_unordered_extension: "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> 
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> static_inclusive (path\<^sub>1 @ [l]) path\<^sub>2
"
 apply (erule static_inclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
done

lemma static_inclusive_preserved_under_unordered_double_extension: "
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> static_inclusive (path\<^sub>1 @ [l1]) (path\<^sub>2 @ [l2])
"
by (metis static_inclusive_commut static_inclusive_preserved_under_unordered_extension prefix_append prefix_def)



inductive paths_correspond :: "control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    paths_correspond [] []
  " |
  Next: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LNxt x]) (path @ [(NLet x, ENext)])
  " |
  Spawn: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LSpwn x]) (path @ [(NLet x, ESpawn)])
  " |
  Call: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LCall x]) (path @ [(NLet x, ECall)])
  "  |
  Return: "
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LRtn x]) (path @ [(NResult x, EReturn)])
  " 

lemma not_static_inclusive_sound: "
  E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  paths_correspond \<pi>1 path1 \<Longrightarrow>
  paths_correspond \<pi>2 path2 \<Longrightarrow>
  static_inclusive path1 path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "paths_correspond \<pi>1 path1" and
    H5: "paths_correspond \<pi>2 path2"
  
  from H4
  show "static_inclusive path1 path2"
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


lemma paths_cong_preserved_under_reduction: "
  paths_correspond (\<pi> @ [l]) (path @ [n]) \<Longrightarrow>
  paths_correspond \<pi> path"
using paths_correspond.cases by fastforce


lemma equality_abstract_to_concrete': "
  paths_correspond \<pi>1 path \<Longrightarrow>
  \<forall> \<pi>2 .  paths_correspond \<pi>2 path \<longrightarrow> \<pi>1 = \<pi>2
"
apply (erule paths_correspond.induct)
  using paths_correspond.cases apply blast
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
done


lemma equality_abstract_to_concrete: "
  path1 = path2 \<Longrightarrow>
  paths_correspond \<pi>1 path1 \<Longrightarrow>
  paths_correspond \<pi>2 path2 \<Longrightarrow>
  \<pi>1 = \<pi>2
"
by (simp add: equality_abstract_to_concrete')

lemma paths_correspond_preserved_under_reduction: "
  paths_correspond \<pi>1 path1 \<Longrightarrow>
  paths_correspond (butlast \<pi>1) (butlast path1) 
"
apply (erule paths_correspond.cases; auto)
  apply (simp add: paths_correspond.Empty)
done

lemma strict_prefix_preserved: "
paths_correspond \<pi>1 path1 \<Longrightarrow>
paths_correspond \<pi> path \<Longrightarrow>
strict_prefix path1 (path @ [n]) \<Longrightarrow>
\<not> strict_prefix \<pi>1 (\<pi> @ [l]) \<Longrightarrow>
strict_prefix (butlast path1) path
"
apply (erule paths_correspond.cases; auto)
  using prefix_bot.bot.not_eq_extremum apply blast
  using prefix_order.order.strict_implies_order prefix_snocD apply fastforce
  using prefix_order.dual_order.strict_implies_order prefix_snocD apply fastforce
  using prefix_order.less_imp_le prefix_snocD apply fastforce
  using prefix_order.order.strict_implies_order prefix_snocD apply fastforce
done


lemma prefix_abstract_to_concrete': "

paths_correspond \<pi>2 path2 \<Longrightarrow>
\<forall> \<pi>1 path1 .
paths_correspond \<pi>1 path1 \<longrightarrow>
prefix path1 path2 \<longrightarrow>
prefix \<pi>1 \<pi>2
"
apply (erule paths_correspond.induct; auto)
  apply (simp add: equality_abstract_to_concrete paths_correspond.Empty)
  apply (simp add: equality_abstract_to_concrete paths_correspond.Next)
  apply (simp add: equality_abstract_to_concrete' paths_correspond.Spawn)
  apply (simp add: equality_abstract_to_concrete' paths_correspond.Call)
  apply (simp add: equality_abstract_to_concrete' paths_correspond.Return)
done

lemma prefix_abstract_to_concrete: "
paths_correspond \<pi>2 path2 \<Longrightarrow>
paths_correspond \<pi>1 path1 \<Longrightarrow>
prefix path1 path2 \<Longrightarrow>
prefix \<pi>1 \<pi>2
"
by (simp add: prefix_abstract_to_concrete')


lemma strict_prefix_abstract_to_concrete': "
paths_correspond \<pi>2 path2 \<Longrightarrow>
\<forall> \<pi>1 path1 .
strict_prefix path1 path2 \<longrightarrow>
paths_correspond \<pi>1 path1 \<longrightarrow>
strict_prefix \<pi>1 \<pi>2
"
apply (erule paths_correspond.cases; auto)
  apply (metis not_Cons_self2 prefix_abstract_to_concrete prefix_snoc same_prefix_nil strict_prefix_def)+
done


lemma strict_prefix_abstract_to_concrete: "
strict_prefix path1 path2 \<Longrightarrow>
paths_correspond \<pi>1 path1 \<Longrightarrow>
paths_correspond \<pi>2 path2 \<Longrightarrow>
strict_prefix \<pi>1 \<pi>2
"
by (simp add: strict_prefix_abstract_to_concrete')


lemma equality_contcrete_to_abstract': "
  paths_correspond \<pi> path1 \<Longrightarrow>
  \<forall> path2 .  paths_correspond \<pi> path2 \<longrightarrow> path1 = path2
"
apply (erule paths_correspond.induct)
apply auto[1]
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_correspond.cases; auto)
done

lemma equality_contcrete_to_abstract: "
  \<pi>1 = \<pi>2 \<Longrightarrow>
  paths_correspond \<pi>1 path1 \<Longrightarrow>
  paths_correspond \<pi>2 path2 \<Longrightarrow>
  path1 = path2

"
by (simp add: equality_contcrete_to_abstract')


lemma spawn_point_preserved_under_congruent_paths: " 
l1 = (LNxt x) \<Longrightarrow> l2 = (LSpwn x) \<Longrightarrow>
paths_correspond (\<pi> @ [l1]) (path @ [n1]) \<Longrightarrow>
paths_correspond (\<pi> @ [l2]) (path @ [n2]) \<Longrightarrow>
n1 = (NLet x, ENext) \<and> n2 = (NLet x, ESpawn)
"
apply (erule paths_correspond.cases; auto)
using equality_contcrete_to_abstract paths_correspond.Spawn apply blast
done

lemma not_static_inclusive_step: "
\<forall>\<pi>1 \<pi>2 path1 path2.
  E \<pi>1 \<noteq> None \<longrightarrow>
  E \<pi>2 \<noteq> None \<longrightarrow>
  paths_correspond \<pi>1 path1 \<longrightarrow> 
  paths_correspond \<pi>2 path2 \<longrightarrow> 
  static_inclusive path1 path2 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
paths_correspond \<pi>1 path1 \<Longrightarrow> 
paths_correspond \<pi>2 path2 \<Longrightarrow>
static_inclusive path1 path2 
"
proof ((case_tac "path1 = []"; (simp add: Prefix1)), (case_tac "path2 = []", (simp add: Prefix2)))
  assume 
    H1: "
      \<forall>\<pi>1. (\<exists>y. E \<pi>1 = Some y) \<longrightarrow>
      (\<forall>\<pi>2. (\<exists>y. E \<pi>2 = Some y) \<longrightarrow>
      (\<forall>path1. paths_correspond \<pi>1 path1 \<longrightarrow>
      (\<forall>path2. paths_correspond \<pi>2 path2 \<longrightarrow> 
        static_inclusive path1 path2)))" and
    H2: "star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H)" and
    H3: "(E, H) \<rightarrow> (E', H')" and
    H4: "\<exists>y. E' \<pi>1 = Some y" and
    H5: "\<exists>y. E' \<pi>2 = Some y " and
    H6: "paths_correspond \<pi>1 path1" and
    H7: "paths_correspond \<pi>2 path2" and
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
    H14: "paths_correspond \<pi>1x path1x"
    apply (rule paths_correspond.cases)
    using H8 by blast+

  from H7
  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x @ [l2] = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "paths_correspond \<pi>2x path2x"
    apply (rule paths_correspond.cases)
    using H9 by blast+
 
  have H22: "paths_correspond (\<pi>1x @ [l1]) (path1x @ [n1])"
    by (simp add: H12 H13 H6)

  have H23: "paths_correspond (\<pi>2x @ [l2]) (path2x @ [n2])"
    by (simp add: H15 H16 H7)

  show "static_inclusive path1 path2"
  proof cases
    assume L1H1: "leaf E \<pi>1x"
    obtain \<sigma>1x where
      L1H2: "E \<pi>1x = Some \<sigma>1x" using L1H1 leaf.simps by auto
    show "static_inclusive path1 path2"
    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto


      have L2H4: "\<not> strict_prefix \<pi>1x \<pi>2x"
        by (meson L1H1 L2H1 leaf.cases)
      have L2H5: "\<not> strict_prefix \<pi>2x \<pi>1x"
        by (meson L1H1 L2H1 leaf.cases)

      have L2H6: "\<not> strict_prefix path1x path2x"
        using H14 H17 L2H4 strict_prefix_abstract_to_concrete by auto
      have L2H7: "\<not> strict_prefix path2x path1x"
        using H14 H17 L2H5 strict_prefix_abstract_to_concrete by blast

      have L2H8: "static_inclusive path1x path2x"
        using H1 H14 H17 L1H2 L2H2 by blast

      show "static_inclusive path1 path2"
      proof cases
        assume L3H1: "path1x = path2x"

        have L3H3: "
          l1 = l2 \<or> 
          (\<exists> x . l1 = (LNxt x) \<and> l2 = (LSpwn x)) \<or>
          (\<exists> x . l1 = (LSpwn x) \<and> l2 = (LNxt x))" 
          by (smt H10 H11 H12 H14 H15 H16 H3 H7 L1H1 L2H4 L3H1 strict_prefix_abstract_to_concrete prefix_snoc spawn_point strict_prefixI' strict_prefix_def)

        have L3H4: "
          n1 = n2 \<or> 
          (\<exists> x . n1 = (NLet x, ENext) \<and> n2 = (NLet x, ESpawn )) \<or>
          (\<exists> x . n1 = (NLet x, ESpawn ) \<and> n2 = (NLet x, ENext))" 
          by (metis H12 H13 H14 H15 H16 H17 H6 H7 L3H1 L3H3 append1_eq_conv equality_abstract_to_concrete equality_contcrete_to_abstract spawn_point_preserved_under_congruent_paths)

        have L3H5: "static_inclusive (path1x @ [n1]) (path1x @ [n2])"
          using L3H4 static_inclusive.intros(3) static_inclusive.intros(4) Prefix1 by blast
        show "static_inclusive path1 path2"
          using H13 H16 L3H1 L3H5 by auto
      next
        assume L3H1: "path1x \<noteq> path2x"
        show "static_inclusive path1 path2"
          using H13 H16 L2H6 L2H7 L2H8 L3H1 static_inclusive_preserved_under_unordered_double_extension strict_prefixI by blast
      qed
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      have L2H3: "static_inclusive path1x path2"
        using H1 H14 H7 L1H2 L2H2 by blast

      have L2H8: "\<not> strict_prefix \<pi>1x \<pi>2"
        by (metis L1H1 L2H2 leaf.cases option.distinct(1))
      have L2H9: "\<not> strict_prefix path1x path2"
        using H14 H7 L2H8 strict_prefix_abstract_to_concrete by blast
      show "static_inclusive path1 path2"
        by (metis H13 L2H3 L2H9 Prefix2 static_inclusive_preserved_under_unordered_extension prefix_prefix strict_prefix_def)
    qed

  next
    assume L1H1: "\<not> leaf E \<pi>1x"
      have L1H2: "E \<pi>1 = Some \<sigma>1"
        using H10 H12 H3 L1H1 path_state_preserved_for_non_leaf by blast
    show "static_inclusive path1 path2"

    proof cases
      assume L2H1: "leaf E \<pi>2x"
      obtain \<sigma>2x where
        L2H2: "E \<pi>2x = Some \<sigma>2x" using L2H1 leaf.simps by auto
      have L2H3: "static_inclusive path1 path2x"
        using H1 H17 H6 L1H2 L2H2 by blast
      have L2H8: "\<not> strict_prefix \<pi>2x \<pi>1"
        by (metis L1H2 L2H1 leaf.cases option.distinct(1))
      have L2H9: "\<not> strict_prefix path2x path1"
        using H17 H6 L2H8 strict_prefix_abstract_to_concrete by auto
      show "static_inclusive path1 path2"
        by (metis H16 L2H3 L2H9 Prefix1 static_inclusive_commut static_inclusive_preserved_under_unordered_extension prefix_order.dual_order.not_eq_order_implies_strict prefix_prefix)
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      show "static_inclusive path1 path2"
        using H1 H6 H7 L1H2 L2H2 by blast
    qed

  qed

qed

lemma not_static_inclusive: "
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_correspond \<pi>1 path1 \<Longrightarrow>
  paths_correspond \<pi>2 path2 \<Longrightarrow>
  static_inclusive path1 path2
"
proof -
  assume
    H1: "star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "paths_correspond \<pi>1 path1" and
    H5: "paths_correspond \<pi>2 path2"

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
      paths_correspond \<pi>1 path1 \<longrightarrow>
      paths_correspond \<pi>2 path2 \<longrightarrow>
      static_inclusive path1 path2
    "
  proof induction
    case (refl z)
    then show ?case
      using not_static_inclusive_sound by blast
  next
    case (step x y z)

    {
      fix \<E>' H' \<pi>1 \<pi>2 path1 path2
      assume 
        L2H1: "x = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" and
        L2H2: "z = (\<E>', H')" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "paths_correspond \<pi>1 path1" and
        L2H6: "paths_correspond \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8: "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          paths_correspond \<pi>1 path1 \<longrightarrow> 
          paths_correspond \<pi>2 path2 \<longrightarrow> 
          static_inclusive path1 path2 "
        by blast

      have 
        "static_inclusive path1 path2"
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 not_static_inclusive_step step.hyps(1) step.hyps(2) by blast
    }
    then show ?case by blast
  qed

  from H2 H3 H4 H5 H6(1) H6(2) H8 show 
    "static_inclusive path1 path2" by blast
qed


lemma is_send_path_implies_nonempty_pool: "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2: "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>Let x\<^sub>y (Sync x\<^sub>e) e\<^sub>n;\<rho>;\<kappa>\<rangle>) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed

lemma is_recv_path_implies_nonempty_pool: "
  is_recv_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_recv_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2: "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>Let x\<^sub>y (Sync x\<^sub>e) e\<^sub>n;\<rho>;\<kappa>\<rangle>) 
    " using is_recv_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed


(* END *)


(* PATH SOUND *)

inductive 
  static_traversable_env :: "abstract_env \<Rightarrow> transition_set \<Rightarrow> env \<Rightarrow> bool"  and
  static_traversable_val :: "abstract_env \<Rightarrow> transition_set \<Rightarrow> val \<Rightarrow> bool"
where
  Intro: "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>  static_traversable_val V F \<omega> \<Longrightarrow>
    static_traversable_env V F \<rho>
  " |

  Unit: "
    static_traversable_val V F VUnt
  " |

  Chan: "
    static_traversable_val V F (VChn c)
  " |

  SendEvt: "
    static_traversable_env V F \<rho> \<Longrightarrow>
    static_traversable_val V F (VClsr (SendEvt _ _) \<rho>)
  " |

  RecvEvt: "
    static_traversable_env V F \<rho> \<Longrightarrow>
    static_traversable_val V F (VClsr (RecvEvt _) \<rho>)
  " |

  Left: "
    static_traversable_env V F \<rho> \<Longrightarrow>
    static_traversable_val V F (VClsr (Lft _) \<rho>)
  " |

  Right: "
    static_traversable_env V F \<rho> \<Longrightarrow>
    static_traversable_val V F (VClsr (Rght _) \<rho>)
  " |

  Abs: "
    static_traversable V F e \<Longrightarrow> 
    static_traversable_env V F  \<rho> \<Longrightarrow>
    static_traversable_val V F (VClsr (Abs f x e) \<rho>)
  " |

  Pair: "
    static_traversable_env V F \<rho> \<Longrightarrow>
    static_traversable_val V F (VClsr (Pair _ _) \<rho>)
  " 

inductive static_traversable_stack :: "abstract_env \<Rightarrow> transition_set \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty: "static_traversable_stack V F []" |
  Nonempty: "
    \<lbrakk> 
      static_traversable V F e;
      static_traversable_env V F \<rho>;
      static_traversable_stack V F \<kappa>
    \<rbrakk> \<Longrightarrow> 
    static_traversable_stack V F ((Ctn x e \<rho>) # \<kappa>)
  "

inductive static_traversable_pool :: "abstract_env \<Rightarrow> transition_set \<Rightarrow> trace_pool \<Rightarrow> bool"  where
  Intro: "
    (\<forall> \<pi> e \<rho> \<kappa> . E \<pi> = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<longrightarrow> 
      static_traversable V F e \<and>
      static_traversable_env V F \<rho> \<and>
      static_traversable_stack V F \<kappa>) \<Longrightarrow> 
    static_traversable_pool V F E
  "

lemma static_traversable_pool_preserved_under_seq_step_down: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow>
  \<E>m pi = Some (\<langle>Rslt x;env;Ctn xk ek envk # k\<rangle>) \<Longrightarrow> 
  env x = Some v \<Longrightarrow> 
  static_traversable_pool V F (\<E>m(pi @ [LRtn xk] \<mapsto> \<langle>ek;envk(xk \<mapsto> v);k\<rangle>))
"
sorry

lemma static_traversable_pool_preserved_under_seq_step: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow>
  \<E>m pi = Some (\<langle>exp.Let x b e;env;k\<rangle>) \<Longrightarrow> 
  seq_step (b, env) v \<Longrightarrow> 
  static_traversable_pool V F (\<E>m(pi @ [LNxt x] \<mapsto> \<langle>e;env(x \<mapsto> v);k\<rangle>))
"
sorry

lemma static_traversable_pool_preserved_under_seq_step_up: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow>
  \<E>m pi = Some (\<langle>exp.Let x b e;env;k\<rangle>) \<Longrightarrow>
  seq_step_up (b, env) (e', env') \<Longrightarrow> 
  static_traversable_pool V F (\<E>m(pi @ [LCall x] \<mapsto> \<langle>e';env';Ctn x e env # k\<rangle>))
"
sorry

lemma static_traversable_pool_preserved_under_let_chan: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow> 
  \<E>m pi = Some (\<langle>exp.Let x MkChn e;env;k\<rangle>) \<Longrightarrow> 
  static_traversable_pool V F (\<E>m(pi @ [LNxt x] \<mapsto> \<langle>e;env(x \<mapsto> VChn (Ch pi x));k\<rangle>))
"
sorry

lemma static_traversable_pool_preserved_under_let_spawn: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pi \<Longrightarrow> \<E>m pi = Some (\<langle>exp.Let x (Spwn ec) e;env;k\<rangle>) \<Longrightarrow> 
  static_traversable_pool V F (\<E>m(pi @ [LNxt x] \<mapsto> \<langle>e;env(x \<mapsto> VUnt);k\<rangle>, pi @ [LSpwn x] \<mapsto> \<langle>ec;env;[]\<rangle>))
"
sorry


lemma static_traversable_pool_preserved_under_let_sync: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  leaf \<E>m pis \<Longrightarrow>
  \<E>m pis = Some (\<langle>exp.Let xs (Sync xse) es;envs;ks\<rangle>) \<Longrightarrow>
  envs xse = Some (VClsr (SendEvt xsc xm) envse) \<Longrightarrow>
  leaf \<E>m pir \<Longrightarrow>
  \<E>m pir = Some (\<langle>exp.Let xr (Sync xre) er;envr;kr\<rangle>) \<Longrightarrow>
  envr xre = Some (VClsr (RecvEvt xrc) envre) \<Longrightarrow>
  envse xsc = Some (VChn c) \<Longrightarrow>
  envre xrc = Some (VChn c) \<Longrightarrow> 
  envse xm = Some vm \<Longrightarrow> 
  static_traversable_pool V F 
    (\<E>m(pis @ [LNxt xs] \<mapsto> \<langle>es;envs(xs \<mapsto> VUnt);ks\<rangle>, pir @ [LNxt xr] \<mapsto> \<langle>er;envr(xr \<mapsto> vm);kr\<rangle>))
"
sorry

lemma static_traversable_pool_preserved: "
  static_traversable_pool V F \<E>m \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<Longrightarrow>
  concur_step (\<E>m, Hm) (\<E>', H') \<Longrightarrow>
  static_traversable_pool V F \<E>'
"
proof -
  assume 
    H1: "static_traversable_pool V F \<E>m" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>m" and
    H3: "concur_step (\<E>m, Hm) (\<E>', H')"

  from H3
  show "static_traversable_pool V F \<E>'"
  proof cases
    case (Seq_Step_Down pi x env xk ek envk k v)
    then show ?thesis
      using H1 H2 static_traversable_pool_preserved_under_seq_step_down by auto
  next
    case (Seq_Step pi x b e env k v)
    then show ?thesis
      using H1 H2 static_traversable_pool_preserved_under_seq_step by blast
  next
    case (Seq_Step_Up pi x b e env k e' env')
    then show ?thesis
      using H1 H2 static_traversable_pool_preserved_under_seq_step_up by blast
  next
    case (Let_Chan pi x e env k)
    then show ?thesis
      using H1 H2 static_traversable_pool_preserved_under_let_chan by auto
  next
    case (Let_Spawn pi x ec e env k)
    then show ?thesis
      using H1 H2 static_traversable_pool_preserved_under_let_spawn by blast
  next
    case (Let_Sync pis xs xse es envs ks xsc xm envse pir xr xre er envr kr xrc envre c vm)
    then show ?thesis
      using H1 H2 static_traversable_pool_preserved_under_let_sync by auto
  qed


qed


lemma static_traversable_pool_preserved_star: "
  static_traversable_pool V F \<E> \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> \<E> \<Longrightarrow>
  star concur_step (\<E>, H) (\<E>', H') \<Longrightarrow>
  static_traversable_pool V F \<E>'
"
proof -
  assume 
    H1: "static_traversable_pool V F \<E>" and
    H2: "(V, C) \<Turnstile>\<^sub>\<E> \<E>" and
    H4: "star concur_step (\<E>, H) (\<E>', H')"

  obtain EH EH' where
    H6: "EH = (\<E>, H)" and 
    H7: "EH' = (\<E>', H')" and 
    H8: "star concur_step EH EH'"
    by (simp add: H4)

  have H9: "star_left concur_step EH EH'"
    by (simp add: H4 H6 H7 star_implies_star_left)

  from H9
  have 
    H10: "
    \<forall> \<E> H \<E>' H' .
    (V, C) \<Turnstile>\<^sub>\<E> \<E> \<longrightarrow>
    (\<E>, H) = EH \<longrightarrow> static_traversable_pool V F \<E> \<longrightarrow>
    (\<E>', H') = EH' \<longrightarrow> static_traversable_pool V F \<E>'" 
  proof induction
    case (refl x)
    then show ?case by blast
  next
    case (step x y z)
    {
      fix \<E> H \<E>' H'
      assume 
        L1H1: "(\<E>, H) = x" and
        L1H2: "static_traversable_pool V F \<E>" and
        L1H3: "(\<E>', H') = z" and 
        L1H4: "(V, C) \<Turnstile>\<^sub>\<E> \<E>"


      have 
        L1H6: "\<forall> \<E>m Hm . (\<E>m, Hm) = y \<longrightarrow> (V, C) \<Turnstile>\<^sub>\<E> \<E>m \<longrightarrow> static_traversable_pool V F \<E>m"
        using L1H1 L1H2 L1H4 step.IH by blast

      have L1H7: "\<exists> \<E>m Hm . (\<E>m, Hm) = y \<and> (V, C) \<Turnstile>\<^sub>\<E> \<E>m " 
        by (metis L1H1 L1H4 eq_fst_iff star_left_implies_star static_eval_preserved_under_concur_step_star step.hyps(1))

      have L1H8: "static_traversable_pool V F \<E>'"
        using L1H3 L1H6 L1H7 static_traversable_pool_preserved step.hyps(2) by auto
    }

    then show ?case 
      by blast
  qed

  show "static_traversable_pool V F \<E>'"
    using H1 H10 H2 H6 H7 by blast

qed


lemma static_traversable_pool_implies_static_traceable: "
  \<E>' \<pi> = Some (\<langle>Let x b e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_traversable_pool V F \<E>' \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_correspond \<pi> path \<and>
    static_traceable V F (top_label e) isEnd path
"
sorry
(*
proof -
  assume 
    H1: "\<E>' \<pi> = Some (\<langle>Let x b e\<^sub>n;\<rho>;\<kappa>\<rangle>)" and 
    H2: "star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')" and
    H3: "(V, C) \<Turnstile>\<^sub>e e" and
    H4: "static_traversable_pool V F \<E>'" and
    H5: "isEnd (NLet x)"

  have H6: "(V, C) \<Turnstile>\<^sub>\<E> \<E>'" 
    using H2 H3 static_eval_preserved_under_concur_step_star static_eval_to_pool 
    by blast

  show "\<exists>path. paths_correspond \<pi> path \<and> static_traceable V F (top_label e) isEnd path" sorry
qed
*)


lemma lift_traversable_to_pool: "
  static_traversable V F e \<Longrightarrow>
  static_traversable_pool V F [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]
"
apply (erule static_traversable.cases; auto)
  apply (simp add: static_traversable.Result static_traversable_env.simps static_traversable_pool.Intro static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Unit static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Chan static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_SendEvt static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_RecvEvt static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Pair static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Left static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Right static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Abs static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Spawn static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Sync static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Fst static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Snd static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_Case static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
  apply (simp add: static_traversable.Let_App static_traversable_env.simps static_traversable_pool.intros static_traversable_stack.Empty)
done

lemma path_not_traceable_sound: "
  \<E>' \<pi> = Some (\<langle>Let x b e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_correspond \<pi> path \<and>
    static_traceable V F (top_label e) isEnd path
"
by (metis lift_traversable_to_pool static_eval_to_pool static_traversable_pool_implies_static_traceable static_traversable_pool_preserved_star)

lemma send_path_not_traceable_sound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  \<exists> pathSync .
    (paths_correspond \<pi>Sync pathSync) \<and> 
    static_traceable V F (top_label e) (static_send_label V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in label_not_send_site_sound; auto?)
 apply (frule path_not_traceable_sound; auto?)
done

lemma recv_path_not_traceable_sound: "
  is_recv_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  \<exists> pathSync .
    (paths_correspond \<pi>Sync pathSync) \<and> 
    static_traceable V F (top_label e) (static_recv_label V e xC) pathSync
"
 apply (unfold is_recv_path.simps; auto)
 apply (frule_tac x\<^sub>r\<^sub>c = xrc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in label_not_recv_site_sound; auto?)
 apply (frule path_not_traceable_sound; auto?)
done

(* END PATH SOUND *)



theorem singular_to_equal: "
  every_two (static_traceable V F (top_label e) (static_send_label V e xC)) singular \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: every_two.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>1 in send_path_not_traceable_sound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>2 in send_path_not_traceable_sound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (metis not_static_inclusive equality_abstract_to_concrete is_send_path_implies_nonempty_pool)
done



theorem noncompetitive_send_to_ordered_send: "
  every_two (static_traceable V F (top_label e) (static_send_label V e xC)) noncompetitive \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: every_two.simps noncompetitive.simps; auto?)
  using send_path_not_traceable_sound not_static_inclusive 
  apply (meson is_send_path_implies_nonempty_pool ordered.simps prefix_abstract_to_concrete)
done


lemma noncompetitive_recv_to_ordered_recv: "
   every_two (static_traceable V F (top_label e) (static_recv_label V e xC)) noncompetitive \<Longrightarrow>
   static_traversable V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
   every_two (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: every_two.simps noncompetitive.simps; auto?)
  using recv_path_not_traceable_sound not_static_inclusive 
 apply (meson is_recv_path_implies_nonempty_pool ordered.simps prefix_abstract_to_concrete)
done



lemma static_communication_classification_sound:
  "Sound_Communication.communication_sound static_one_shot static_fan_out static_fan_in static_one_to_one"
proof -
 show "communication_sound static_one_shot static_fan_out static_fan_in static_one_to_one" 
   apply (unfold_locales)
   apply (erule static_one_shot.cases; auto)
   apply (unfold one_shot.simps)
   apply (simp add: singular_to_equal)
  
   apply (erule static_fan_out.cases; auto)
   apply (unfold fan_out.simps)
   apply (metis noncompetitive_send_to_ordered_send)
  
   apply (erule static_fan_in.cases; auto)
   apply (unfold fan_in.simps)
   apply (metis noncompetitive_recv_to_ordered_recv)
  
   apply (erule static_one_to_one.cases; auto)
   apply (unfold one_to_one.simps)
   apply (simp add: fan_in.simps fan_out.simps noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send)
  done
qed

end