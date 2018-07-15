theory Static_Communication_Analysis_A
  imports Main Syntax 
    Dynamic_Semantics 
    Static_Semantics
    Dynamic_Communication_Analysis
    Static_Communication_Analysis
begin

datatype edge_label = ENext | ESpawn | ECall | EReturn

type_synonym flow_label = "(node_label \<times> edge_label \<times> node_label)"

type_synonym flow_set = "flow_label set"

type_synonym step_label = "(node_label \<times> edge_label)"

type_synonym abstract_path = "step_label list"


inductive simple_flow_set :: "abstract_env \<Rightarrow> (node_label * edge_label * node_label) set \<Rightarrow> exp \<Rightarrow> bool"  where
  Result: "
    simple_flow_set V F (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {(NLet x , ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = SEND EVT x\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = RECV EVT x\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = LEFT x\<^sub>p in e)
  " |
  Let_Right: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = RIGHT x\<^sub>p in e)
  " |
  Let_Abs: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e\<^sub>b;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (NLet x, ENext, nodeLabel e),
        (NLet x, ESpawn, nodeLabel e\<^sub>c)
      } \<subseteq> F;
      simple_flow_set V F e\<^sub>c;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = SYNC xSE in e)
  " |
  Let_Fst: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = FST x\<^sub>p in e)
  " |
  Let_Snd: "
    \<lbrakk>
      {(NLet x, ENext, nodeLabel e)} \<subseteq> F;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = SND x\<^sub>p in e)
  " |
  Let_Case: "
    \<lbrakk>
      {
        (NLet x, ECall, nodeLabel e\<^sub>l),
        (NLet x, ECall, nodeLabel e\<^sub>r),
        (NResult (\<lfloor>e\<^sub>l\<rfloor>), EReturn, nodeLabel e),
        (NResult (\<lfloor>e\<^sub>r\<rfloor>), EReturn, nodeLabel e)
      } \<subseteq> F;
      simple_flow_set V F e\<^sub>l;
      simple_flow_set V F e\<^sub>r;
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow>
        {
          (NLet x, ECall, nodeLabel e\<^sub>b),
          (NResult (\<lfloor>e\<^sub>b\<rfloor>), EReturn, nodeLabel e)
        } \<subseteq> F);
      simple_flow_set V F e
    \<rbrakk> \<Longrightarrow>
    simple_flow_set V F (LET x = APP f x\<^sub>a in e)
  "



inductive may_be_path :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> node_label \<Rightarrow> (node_label \<Rightarrow> bool) \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    may_be_path V F start isEnd []
  " |
  Edge: "
    isEnd end \<Longrightarrow>
    {(start, edge, end)} \<subseteq> F \<Longrightarrow>
    may_be_path V F start isEnd [(start, edge)]
  " |
  Step: "
    may_be_path V F middle isEnd ((middle, edge') # path) \<Longrightarrow>
    {(start, edge, middle)} \<subseteq> F \<Longrightarrow>
    may_be_path V F start isEnd ((start, edge) # (middle, edge') # path)
  "


inductive may_be_inclusive :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Prefix1: "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
  Prefix2: "
    prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
  Spawn1: "
    \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Spawn2: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>2
  "

lemma may_be_inclusive_commut: "
  path\<^sub>1 \<asymp> path\<^sub>2 \<Longrightarrow> path\<^sub>2 \<asymp> path\<^sub>1
"
 apply (erule may_be_inclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
done


lemma may_be_inclusive_preserved_under_unordered_extension: "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> path\<^sub>1 \<asymp> path\<^sub>2 \<Longrightarrow> path\<^sub>1 @ [l] \<asymp> path\<^sub>2
"
 apply (erule may_be_inclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
done

lemma may_be_inclusive_preserved_under_unordered_double_extension: "
  path\<^sub>1 \<asymp> path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> path\<^sub>1 @ [l1] \<asymp> path\<^sub>2 @ [l2]
"
by (metis may_be_inclusive_commut may_be_inclusive_preserved_under_unordered_extension prefix_append prefix_def)


inductive singular :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  equal: "
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow> 
    singular \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive noncompetitive :: "abstract_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  ordered: "
    ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  exclusive: "
    \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2) \<Longrightarrow> 
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  "

inductive static_one_shot :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
    simple_flow_set V F e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    every_two (may_be_path V F (nodeLabel e) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    simple_flow_set V F e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    simple_flow_set V F e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two (may_be_path V F (nodeLabel e) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    simple_flow_set V F e \<Longrightarrow>
    static_fan_in V e xC 
  "



inductive paths_congruent :: "control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Empty: "
    paths_congruent [] []
  " |
  Next: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> @ [LNext x]) (path @ [(NLet x, ENext)])
  " |
  Spawn: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> @ [LSpawn x]) (path @ [(NLet x, ESpawn)])
  " |
  Call: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> @ [LCall x]) (path @ [(NLet x, ECall)])
  "  |
  Return: "
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (\<pi> @ [LReturn x]) (path @ [(NResult x, EReturn)])
  " 

lemma abstract_paths_of_same_run_inclusive_base: "
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
  
  from H4
  show "path1 \<asymp> path2"
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

lemma paths_equal_implies_paths_inclusive: "
  path1 = path2 \<Longrightarrow> path1 \<asymp> path2 
"
by (simp add: Prefix2)

lemma paths_cong_preserved_under_reduction: "
  paths_congruent (\<pi> @ [l]) (path @ [n]) \<Longrightarrow>
  paths_congruent \<pi> path"
using paths_congruent.cases by fastforce


lemma equality_abstract_to_concrete': "
  paths_congruent \<pi>1 path \<Longrightarrow>
  \<forall> \<pi>2 .  paths_congruent \<pi>2 path \<longrightarrow> \<pi>1 = \<pi>2
"
apply (erule paths_congruent.induct)
  using paths_congruent.cases apply blast
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast \<pi>2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
done


lemma equality_abstract_to_concrete: "
  path1 = path2 \<Longrightarrow>
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  \<pi>1 = \<pi>2
"
by (simp add: equality_abstract_to_concrete')

lemma paths_congruent_preserved_under_reduction: "
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent (butlast \<pi>1) (butlast path1) 
"
apply (erule paths_congruent.cases; auto)
  apply (simp add: paths_congruent.Empty)
done

lemma strict_prefix_preserved: "
paths_congruent \<pi>1 path1 \<Longrightarrow>
paths_congruent \<pi> path \<Longrightarrow>
strict_prefix path1 (path @ [n]) \<Longrightarrow>
\<not> strict_prefix \<pi>1 (\<pi> @ [l]) \<Longrightarrow>
strict_prefix (butlast path1) path
"
apply (erule paths_congruent.cases; auto)
  using prefix_bot.bot.not_eq_extremum apply blast
  using prefix_order.order.strict_implies_order prefix_snocD apply fastforce
  using prefix_order.dual_order.strict_implies_order prefix_snocD apply fastforce
  using prefix_order.less_imp_le prefix_snocD apply fastforce
  using prefix_order.order.strict_implies_order prefix_snocD apply fastforce
done


lemma prefix_abstract_to_concrete': "

paths_congruent \<pi>2 path2 \<Longrightarrow>
\<forall> \<pi>1 path1 .
paths_congruent \<pi>1 path1 \<longrightarrow>
prefix path1 path2 \<longrightarrow>
prefix \<pi>1 \<pi>2
"
apply (erule paths_congruent.induct; auto)
  apply (simp add: equality_abstract_to_concrete paths_congruent.Empty)
  apply (simp add: equality_abstract_to_concrete paths_congruent.Next)
  apply (simp add: equality_abstract_to_concrete' paths_congruent.Spawn)
  apply (simp add: equality_abstract_to_concrete' paths_congruent.Call)
  apply (simp add: equality_abstract_to_concrete' paths_congruent.Return)
done

lemma prefix_abstract_to_concrete: "
paths_congruent \<pi>2 path2 \<Longrightarrow>
paths_congruent \<pi>1 path1 \<Longrightarrow>
prefix path1 path2 \<Longrightarrow>
prefix \<pi>1 \<pi>2
"
by (simp add: prefix_abstract_to_concrete')


lemma strict_prefix_abstract_to_concrete': "
paths_congruent \<pi>2 path2 \<Longrightarrow>
\<forall> \<pi>1 path1 .
strict_prefix path1 path2 \<longrightarrow>
paths_congruent \<pi>1 path1 \<longrightarrow>
strict_prefix \<pi>1 \<pi>2
"
apply (erule paths_congruent.induct; auto)
  apply (metis not_Cons_self2 prefix_abstract_to_concrete prefix_snoc same_prefix_nil strict_prefix_def)+
done


lemma strict_prefix_abstract_to_concrete: "
strict_prefix path1 path2 \<Longrightarrow>
paths_congruent \<pi>1 path1 \<Longrightarrow>
paths_congruent \<pi>2 path2 \<Longrightarrow>
strict_prefix \<pi>1 \<pi>2
"
by (simp add: strict_prefix_abstract_to_concrete')


lemma equality_contcrete_to_abstract': "
  paths_congruent \<pi> path1 \<Longrightarrow>
  \<forall> path2 .  paths_congruent \<pi> path2 \<longrightarrow> path1 = path2
"
apply (erule paths_congruent.induct)
apply auto[1]
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
apply (rule allI, rule impI)
apply (drule_tac x = "butlast path2" in spec)
apply (rotate_tac)
apply (erule paths_congruent.cases; auto)
done

lemma equality_contcrete_to_abstract: "
  \<pi>1 = \<pi>2 \<Longrightarrow>
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  path1 = path2

"
by (simp add: equality_contcrete_to_abstract')




lemma spawn_point_preserved_under_congruent_paths: " 
l1 = (LNext x) \<Longrightarrow> l2 = (LSpawn x) \<Longrightarrow>
paths_congruent (\<pi> @ [l1]) (path @ [n1]) \<Longrightarrow>
paths_congruent (\<pi> @ [l2]) (path @ [n2]) \<Longrightarrow>
n1 = (NLet x, ENext) \<and> n2 = (NLet x, ESpawn)
"
apply (erule paths_congruent.cases; auto)
using equality_contcrete_to_abstract paths_congruent.Spawn apply blast
done

lemma abstract_paths_of_same_run_inclusive_step: "
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

  from H6
  obtain \<pi>1x l1 path1x n1 where
    H12: "\<pi>1x @ [l1] = \<pi>1" and
    H13: "path1x @ [n1] = path1" and
    H14: "paths_congruent \<pi>1x path1x"
    apply (rule paths_congruent.cases)
    using H8 by blast+

  from H7
  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x @ [l2] = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "paths_congruent \<pi>2x path2x"
    apply (rule paths_congruent.cases)
    using H9 by blast+
 
  have H22: "paths_congruent (\<pi>1x @ [l1]) (path1x @ [n1])"
    by (simp add: H12 H13 H6)

  have H23: "paths_congruent (\<pi>2x @ [l2]) (path2x @ [n2])"
    by (simp add: H15 H16 H7)

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
        using H14 H17 L2H4 strict_prefix_abstract_to_concrete by auto
      have L2H7: "\<not> strict_prefix path2x path1x"
        using H14 H17 L2H5 strict_prefix_abstract_to_concrete by blast

      have L2H8: "path1x \<asymp> path2x"
        using H1 H14 H17 L1H2 L2H2 by blast

      show "path1 \<asymp> path2"
      proof cases
        assume L3H1: "path1x = path2x"

        have L3H3: "
          l1 = l2 \<or> 
          (\<exists> x . l1 = (LNext x) \<and> l2 = (LSpawn x)) \<or>
          (\<exists> x . l1 = (LSpawn x) \<and> l2 = (LNext x))" 
          by (smt H10 H11 H12 H14 H15 H16 H3 H7 L1H1 L2H4 L3H1 strict_prefix_abstract_to_concrete prefix_snoc spawn_point strict_prefixI' strict_prefix_def)

        have L3H4: "
          n1 = n2 \<or> 
          (\<exists> x . n1 = (NLet x, ENext) \<and> n2 = (NLet x, ESpawn )) \<or>
          (\<exists> x . n1 = (NLet x, ESpawn ) \<and> n2 = (NLet x, ENext))" 
          by (metis H12 H13 H14 H15 H16 H17 H6 H7 L3H1 L3H3 append1_eq_conv equality_abstract_to_concrete equality_contcrete_to_abstract spawn_point_preserved_under_congruent_paths)

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
        using H14 H7 L2H8 strict_prefix_abstract_to_concrete by blast
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
        using H17 H6 L2H8 strict_prefix_abstract_to_concrete by auto
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

lemma abstract_paths_of_same_run_inclusive: "
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
      using abstract_paths_of_same_run_inclusive_base by blast
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
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 abstract_paths_of_same_run_inclusive_step step.hyps(1) step.hyps(2) by blast
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

lemma is_recv_path_implies_nonempty_pool: "
  is_recv_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_recv_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2: "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) 
    " using is_recv_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed

lemma send_abstract_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  paths_congruent \<pi>1 path1 \<Longrightarrow>
  paths_congruent \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
using is_send_path_implies_nonempty_pool abstract_paths_of_same_run_inclusive by fastforce


lemma send_abstract_paths_equal_exclusive_implies_dynamic_paths_equal: "
pathSync = pathSynca \<or> (\<not> pathSynca \<asymp> pathSync) \<Longrightarrow> 

([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>1 \<Longrightarrow>
is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>2 \<Longrightarrow>

paths_congruent \<pi>\<^sub>1 pathSync \<Longrightarrow>
paths_congruent \<pi>\<^sub>2 pathSynca \<Longrightarrow>

\<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (simp add: equality_abstract_to_concrete send_abstract_paths_of_same_run_inclusive)

(* END *)


(* PATH SOUND *)

inductive 
  simple_flow_set_env :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> val_env \<Rightarrow> bool"  and
  simple_flow_set_val :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> val \<Rightarrow> bool"
where
  Intro: "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow> {|\<omega>|} \<subseteq> \<V> x \<and> simple_flow_set_val V F \<omega> \<Longrightarrow>
    simple_flow_set_env V F \<rho>
  " |

  Unit: "
    simple_flow_set_val V F VUnit
  " |

  Chan: "
    simple_flow_set_val V F (VChan c)
  " |

  Send_Evt: "
    simple_flow_set_env V F \<rho> \<Longrightarrow>
    simple_flow_set_val V F (VClosure (Send_Evt _ _) \<rho>)
  " |

  Recv_Evt: "
    simple_flow_set_env V F \<rho> \<Longrightarrow>
    simple_flow_set_val V F (VClosure (Recv_Evt _) \<rho>)
  " |

  Left: "
    simple_flow_set_env V F \<rho> \<Longrightarrow>
    simple_flow_set_val V F (VClosure (Left _) \<rho>)
  " |

  Right: "
    simple_flow_set_env V F \<rho> \<Longrightarrow>
    simple_flow_set_val V F (VClosure (Right _) \<rho>)
  " |

  Abs: "
    simple_flow_set V F e \<Longrightarrow> 
    simple_flow_set_env V F  \<rho> \<Longrightarrow>
    simple_flow_set_val V F (VClosure (Abs f x e) \<rho>)
  " |

  Pair: "
    simple_flow_set_env V F \<rho> \<Longrightarrow>
    simple_flow_set_val V F (VClosure (Pair _ _) \<rho>)
  " 

inductive simple_flow_set_stack :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> cont list \<Rightarrow> bool" where
  Empty: "simple_flow_set_stack V F []" |
  Nonempty: "
    \<lbrakk> 
      simple_flow_set V F e;
      simple_flow_set_env V F \<rho>;
      simple_flow_set_stack V F \<kappa>
    \<rbrakk> \<Longrightarrow> 
    simple_flow_set_stack V F (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive simple_flow_set_pool :: "abstract_env \<Rightarrow> flow_set \<Rightarrow> trace_pool \<Rightarrow> bool"  where
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
apply (erule simple_flow_set.cases; auto)
  apply (simp add: simple_flow_set.Result simple_flow_set_env.simps simple_flow_set_pool.Intro simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Unit simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Chan simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Send_Evt simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Recv_Evt simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Pair simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Left simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Right simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Abs simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Spawn simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Sync simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Fst simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Snd simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_Case simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
  apply (simp add: simple_flow_set.Let_App simple_flow_set_env.simps simple_flow_set_pool.intros simple_flow_set_stack.Empty)
done

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
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in isnt_send_site_sound; auto?)
 apply (frule isnt_path_sound; auto?)
done

lemma isnt_recv_path_sound: "
  is_recv_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  \<exists> pathSync .
    (paths_congruent \<pi>Sync pathSync) \<and> 
    may_be_path V F (nodeLabel e) (may_be_static_recv_node_label V e xC) pathSync
"
 apply (unfold is_recv_path.simps; auto)
 apply (frule_tac x\<^sub>r\<^sub>c = xrc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in isnt_recv_site_sound; auto?)
 apply (frule isnt_path_sound; auto?)
done

(* END PATH SOUND *)



theorem one_shot_sound': "
  every_two (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: every_two.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>1 in isnt_send_path_sound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>2 in isnt_send_path_sound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (simp add: equality_abstract_to_concrete send_abstract_paths_of_same_run_inclusive)
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
  every_two (may_be_path V F (nodeLabel e) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  simple_flow_set V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: every_two.simps noncompetitive.simps; auto?)
  using isnt_send_path_sound abstract_paths_of_same_run_inclusive 
  apply (meson is_send_path_implies_nonempty_pool ordered.simps prefix_abstract_to_concrete)
done

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
   every_two (may_be_path V F (nodeLabel e) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
   simple_flow_set V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
   every_two (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
apply (simp add: every_two.simps noncompetitive.simps; auto?)
  using isnt_recv_path_sound abstract_paths_of_same_run_inclusive 
 apply (meson is_recv_path_implies_nonempty_pool ordered.simps prefix_abstract_to_concrete)
done


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
 apply (simp add: fan_in.simps fan_out.simps noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send)
done

end
