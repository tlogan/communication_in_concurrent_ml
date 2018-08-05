theory Sound_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Dynamic_Communication Static_Communication Sound_Communication
    Static_Communication_B
begin

lemma static_inclusive_commut: "
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> static_inclusive path\<^sub>2 path\<^sub>1
"
 apply (erule static_inclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
  apply (simp add: Send2)
  apply (simp add: Send1)
done


lemma static_inclusive_preserved_under_unordered_extension: "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> 
  static_inclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> static_inclusive (path\<^sub>1 @ [l]) path\<^sub>2
"
 apply (erule static_inclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
  apply (simp add: Send1)
  apply (simp add: Send2)
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
    paths_correspond \<pi> (path @ (NLet x, ECall) # path') \<Longrightarrow>
    static_balanced path' \<Longrightarrow>
    paths_correspond (\<pi> @ [LRtn y]) (path @ (NLet x, ECall) # path' @ [(NResult y, EReturn x)])
  " 



inductive 
  dynamic_built_on_chan_var :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> var \<Rightarrow> bool" and
  dynamic_built_on_chan_prim :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> prim \<Rightarrow> bool" and
  dynamic_built_on_chan_bound_exp :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> bind \<Rightarrow> bool" and
  dynamic_built_on_chan_exp :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> exp \<Rightarrow> bool" 
where
  Chan: "
    \<rho> x = Some (VChn c) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |
  Closure: "
    dynamic_built_on_chan_prim \<rho>' c p \<Longrightarrow>
    \<rho> x = Some (VClsr p \<rho>') \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |


  Send_Evt: "
    dynamic_built_on_chan_var \<rho> c xSC \<or> dynamic_built_on_chan_var \<rho> c xM \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (SendEvt xSC xM)
  " |
  Recv_Evt: "
    dynamic_built_on_chan_var \<rho> c xRC \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (RecvEvt xRC)
  " |
  Pair: "
    dynamic_built_on_chan_var \<rho> c x1 \<or> dynamic_built_on_chan \<rho> c x2 \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Pair x1 x2)
  " |
  Left: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Lft xSum)
  " |
  Right: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Rght xSum)
  " |
  Abs: "
    dynamic_built_on_chan_exp \<rho>' c e \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Abs f x e)
  " |

  Prim: "
    dynamic_built_on_chan_prim \<rho> c p \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Prim p)
  " |
  Spawn: "
    dynamic_built_on_chan_exp \<rho> c eCh \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Spwn eCh)
  " |
  Sync: "
    dynamic_built_on_chan_var \<rho> c xY \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Sync xY)
  " |
  Fst: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Fst xP)
  " |
  Snd: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Snd xP)
  " |
  Case: "
    dynamic_built_on_chan_var \<rho> c xS \<or> 
    dynamic_built_on_chan_exp \<rho> c eL \<or> dynamic_built_on_chan_exp \<rho> c eR \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Case xS xL eL xR eR)
  " |
  App: "
    dynamic_built_on_chan_var \<rho> c f \<or>
    dynamic_built_on_chan_var \<rho> c xA \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (App f xA)
  " |

  Result: "
    dynamic_built_on_chan_var \<rho> c x \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (Rslt x)
  " |
  Let: "
    dynamic_built_on_chan_bound_exp \<rho> c b \<or> dynamic_built_on_chan_exp \<rho> c e \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (Let x b e)
  "

inductive paths_correspond_mod_chan :: 
  "trace_pool * cmmn_set \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
  Unordered: "
    paths_correspond \<pi> pathx \<Longrightarrow>
    \<not> (prefix pathx path) \<Longrightarrow>
    \<not> (prefix path pathx) \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c \<pi> path
  " |
  Chan: "
    paths_correspond ((LNxt xC) # \<pi>Suff) path \<Longrightarrow>
    \<E> (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path
  " |
  Sync: "
    paths_correspond \<pi>Suffix pathSuffix \<Longrightarrow>
    \<E> (\<pi>R @ (LNxt xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
    dynamic_built_on_chan_var \<rho>RY c xR \<Longrightarrow>
    \<E> \<pi>S = Some (\<langle>(Let xS (Sync xSE) eSY);\<rho>SY;\<kappa>SY\<rangle>) \<Longrightarrow>
    \<E> \<pi>R = Some (\<langle>(Let xR (Sync xRE) eRY);\<rho>RY;\<kappa>RY\<rangle>) \<Longrightarrow>
    {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c \<pi>S pathPre \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c (\<pi>R @ (LNxt xR) # \<pi>Suffix) (pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # pathSuffix)
  " 

lemma no_empty_paths_correspond_mod_chan: "
  \<not> (paths_correspond_mod_chan EH c [] path)"
  apply (rule notI)
  apply (erule paths_correspond_mod_chan.cases; auto)
  apply (erule paths_correspond.cases; auto)
done


lemma not_static_inclusive_sound_base: "
  E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow> 
  paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_inclusive path1 path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_correspond_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2"
  from H1 H2 H4 show 
    "static_inclusive path1 path2" 
    by (metis fun_upd_apply no_empty_paths_correspond_mod_chan)
qed

lemma paths_equal_implies_paths_inclusive: "
  path1 = path2 \<Longrightarrow> static_inclusive path1 path2 
"
by (simp add: Prefix2)


(*
lemma equal_concrete_paths_implies_unordered_or_equal_abstract_paths: "
paths_correspond_mod_chan EH c \<pi> path1 \<Longrightarrow>
paths_correspond_mod_chan EH c \<pi> path2 \<Longrightarrow>
path1 = path2 \<or> (\<not> prefix path1 path2 \<and> \<not> prefix path2 path1)
"
sorry
*)

lemma paths_cong_mod_chan_preserved_under_reduction: "
paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) (\<pi> @ [l]) (path @ [n]) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path
"
sorry



lemma leaf_prefix_exists: "
  leaf E' (\<pi> @ [l]) \<Longrightarrow>
  (E, H) \<rightarrow> (E', H') \<Longrightarrow>
  E \<pi> \<noteq> None
"
sorry


lemma path_state_preserved_for_non_leaf: "
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' (\<pi> @ [l]) = Some \<sigma> \<Longrightarrow>
\<not> leaf E \<pi> \<Longrightarrow>
E (\<pi> @ [l]) = Some \<sigma>
"
apply (erule concur_step.cases; auto; (erule seq_step.cases; auto)?)
  apply presburger+
  apply (metis append1_eq_conv fun_upd_other)
  apply (metis butlast_snoc fun_upd_apply)
done


lemma not_static_inclusive_sound_step: "
\<forall>\<pi>1 \<pi>2 path1 path2.
  E \<pi>1 \<noteq> None \<longrightarrow>
  E \<pi>2 \<noteq> None \<longrightarrow>
  paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1 \<longrightarrow> 
  paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2 \<longrightarrow> 
  static_inclusive path1 path2 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H) \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>1 path1 \<Longrightarrow> 
paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>2 path2 \<Longrightarrow>
static_inclusive path1 path2 
"
proof ((case_tac "path1 = []"; (simp add: Prefix1)), (case_tac "path2 = []", (simp add: Prefix2)))
  assume 
    H1: "
      \<forall>\<pi>1. (\<exists>y. E \<pi>1 = Some y) \<longrightarrow>
      (\<forall>\<pi>2. (\<exists>y. E \<pi>2 = Some y) \<longrightarrow>
      (\<forall>path1. paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1 \<longrightarrow>
      (\<forall>path2. paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2 \<longrightarrow> 
        static_inclusive path1 path2)))" and
    H2: "star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H)" and
    H3: "(E, H) \<rightarrow> (E', H')" and
    H4: "\<exists>y. E' \<pi>1 = Some y" and
    H5: "\<exists>y. E' \<pi>2 = Some y " and
    H6: "paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>1 path1" and
    H7: "paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>2 path2" and
    H8: "path1 \<noteq> []" and 
    H9: "path2 \<noteq> []"

  obtain \<sigma>1 where 
    H10: "E' \<pi>1 = Some \<sigma>1"
    using H4 by blast

  obtain \<sigma>2 where 
    H11: "E' \<pi>2 = Some \<sigma>2"
    using H5 by blast

  obtain \<pi>1x l1 path1x n1 where
    H12: "\<pi>1x @ [l1] = \<pi>1" and
    H13: "path1x @ [n1] = path1" and
    H14: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1x path1x" 
  by (metis H3 H6 H8 append_butlast_last_id paths_cong_mod_chan_preserved_under_reduction no_empty_paths_correspond_mod_chan)

  obtain \<pi>2x l2 path2x n2 where
    H15: "\<pi>2x @ [l2] = \<pi>2" and
    H16: "path2x @ [n2] = path2" and
    H17: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2x path2x"
  by (metis H3 H7 H9 append_butlast_last_id paths_cong_mod_chan_preserved_under_reduction no_empty_paths_correspond_mod_chan)


  have H18: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>1 path1" sorry

  have H19: "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi>2 path2" sorry

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
      have "static_inclusive path1x path2x"
        using H1 H14 H17 L1H2 L2H2 by blast
      show "static_inclusive path1 path2" sorry
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      have L2H3: "static_inclusive path1x path2"
        using H1 H14 H19 L1H2 L2H2 by auto

      have L2H4: "\<not> strict_prefix \<pi>1x \<pi>2"
        by (metis L1H1 L2H2 leaf.cases option.distinct(1))
      show "static_inclusive path1 path2"
      proof cases
        assume L3H1: "prefix path1x path2"
       (* inclusive definition fails in case of non-unique variable bindings *)
        show "static_inclusive path1 path2" sorry
      next
        assume L3H1: "\<not> prefix path1x path2"
        show "static_inclusive path1 path2"
          by (metis H13 L2H3 L3H1 Prefix2 static_inclusive_preserved_under_unordered_extension prefix_prefix)
      qed
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
        using H1 H17 H18 L1H2 L2H2 by auto
      show "static_inclusive path1 path2"
      proof cases
        assume L3H1: "prefix path2x path1"
        show "static_inclusive path1 path2" sorry
      next
        assume L3H1: "\<not> prefix path2x path1"
        show "static_inclusive path1 path2"
          by (metis H16 L2H3 L3H1 Prefix1 static_inclusive_commut static_inclusive_preserved_under_unordered_extension prefix_prefix)
      qed
    next
      assume L2H1: "\<not> leaf E \<pi>2x"
      have L2H2: "E \<pi>2 = Some \<sigma>2"
        using H11 H15 H3 L2H1 path_state_preserved_for_non_leaf by blast
      show "static_inclusive path1 path2"
        using H1 H18 H19 L1H2 L2H2 by blast
    qed

  qed

qed


lemma not_static_inclusive_sound: "
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_inclusive path1 path2
"
proof -
  assume
    H1: "star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

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
      paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow>
      paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow>
      static_inclusive path1 path2
    "
  proof induction
    case (refl z)
    then show ?case
      using not_static_inclusive_sound_base by blast
  next
    case (step x y z)

    {
      fix \<E>' H' \<pi>1 \<pi>2 path1 path2
      assume 
        L2H1: "x = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {})" and
        L2H2: "z = (\<E>', H')" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
        L2H6: "paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8: "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          paths_correspond_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow> 
          paths_correspond_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow> 
          static_inclusive path1 path2 "
        by blast

      have 
        "static_inclusive path1 path2"
        using L2H1 L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 not_static_inclusive_sound_step step.hyps(1) step.hyps(2) by blast
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
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (\<langle>(Let x\<^sub>y (Sync x\<^sub>e) e\<^sub>n);\<rho>;\<kappa>\<rangle>) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed


lemma static_equality_sound: "
  path1 = path2 \<Longrightarrow>
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None   \<Longrightarrow> 
  \<pi>1 = \<pi>2
"
sorry


(* PATH SOUND *)

lemma not_static_traceable_sound: "
  \<E>' \<pi> = Some (\<langle>(Let x b e\<^sub>n);\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> z \<noteq> None \<Longrightarrow>
  dynamic_built_on_chan_var \<rho> (Ch \<pi>C xC) z \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_correspond_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi> path \<and>
    static_live_traceable V F Ln Lx (NLet xC) isEnd path
"
sorry



inductive balanced :: "control_path \<Rightarrow> bool" where
  Empty: "
    balanced []
  " |
  Next: "
    balanced [LNxt x]
  " |
  CallReturn: "
    balanced \<pi> \<Longrightarrow>
    balanced ((LCall x) # (\<pi> @ [LRtn x]))
  " |
  Append: "
    balanced \<pi> \<Longrightarrow> balanced \<pi>' \<Longrightarrow>
    balanced (\<pi> @ \<pi>')
  "

lemma call_return_balanced: "
   balanced [LCall x, LRtn x]
"
using balanced.CallReturn balanced.Empty by fastforce



lemma send_not_static_traceable_sound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  \<exists> pathSync .
    (paths_correspond_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in node_not_send_site_sound; auto?)
 apply (frule not_static_traceable_sound; auto?)
  apply (auto simp: 
    dynamic_built_on_chan_var.simps 
    dynamic_built_on_chan_var_dynamic_built_on_chan_prim_dynamic_built_on_chan_bound_exp_dynamic_built_on_chan_exp.Send_Evt 
  )
done

(* END PATH SOUND *)


theorem one_shot_sound': "
  every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) singular \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  every_two (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: every_two.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>1 in send_not_static_traceable_sound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>2 in send_not_static_traceable_sound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (metis is_send_path_implies_nonempty_pool not_static_inclusive_sound static_equality_sound)
done

theorem one_shot_sound: "
  \<lbrakk>
    static_one_shot V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_shot.cases; auto)
 apply (unfold one_shot.simps)
 apply (simp add: one_shot_sound')
done


(*
TO DO LATER:
*)

theorem noncompetitive_send_to_ordered_send: "
  every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry
(*
apply (simp add: every_two.simps noncompetitive.simps; auto)
using send_not_static_traceable_sound runtime_send_paths_are_inclusive by blast
*)

theorem fan_out_sound: "
  \<lbrakk>
    static_fan_out V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> xC)
"
 apply (erule static_fan_out.cases; auto)
 apply (unfold fan_out.simps)
 apply (metis noncompetitive_send_to_ordered_send)
done

lemma noncompetitive_recv_to_ordered_recv: "
   every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
   static_traversable V F (static_recv_node_label V e) e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
   every_two (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem fan_in_sound: "
  \<lbrakk>
    static_fan_in V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
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
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_to_one.cases; auto)
 apply (unfold one_to_one.simps)
 apply (metis fan_in_sound fan_out.intros noncompetitive_send_to_ordered_send static_fan_in.intros)
done

interpretation communication_sound_B
proof -
 show "communication_sound_B" sorry
qed

(*



lemma paths_cong_preserved_under_reduction: "
  paths_correspond (\<pi> @ [l) (path @ [n]) \<Longrightarrow>
  paths_correspond \<pi> path"
using paths_correspond.cases by fastforce


lemma paths_cong_mod_chan_preserved_under_reduction: "
(suffix \<pi> (\<pi>C @ [LNxt xC)) \<and> suffix path [(NLet xC, ENext)] \<or>
  True) \<Longrightarrow>
paths_correspond_mod_chan EH' (Ch \<pi>C xC) (\<pi> @ [l) (path @ [n]) \<Longrightarrow>
E \<pi> \<noteq> None \<Longrightarrow>
paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"
proof -
  assume
    H1: "E \<pi> \<noteq> None" and
    H2: "\<pi> \<noteq> []" "path \<noteq> []" and
    H3: "paths_correspond_mod_chan EH' c (\<pi> @ [l) (path @ [n])"

  from H3
  show "paths_correspond_mod_chan (E, H) c \<pi> path"
  proof cases

    case (Chan xC \<pi>X E' \<pi>C H')

    have 
      H4: "\<pi> @ [l = \<pi>C @ (butlast (LNxt xC # \<pi>X)) @ [l"
      by (metis butlast_append butlast_snoc list.simps(3) local.Chan(3))
    
    have 
      H5: "paths_correspond ((butlast (LNxt xC # \<pi>X)) @ [l) (path @ [n])"
      by (metis append_butlast_last_id last_ConsL last_appendR list.simps(3) local.Chan(3) local.Chan(4))

    have 
      H6: "butlast (LNxt xC # \<pi>X) \<noteq> []"
      by (metis H2(2) H5 paths_correspond.cases snoc_eq_iff_butlast)

    have 
      H7: "paths_correspond (butlast (LNxt xC # \<pi>X)) path"
      using H2(2) H5 H6 paths_cong_preserved_under_reduction by blast

    have 
      H8: "paths_correspond (LNxt xC # (butlast \<pi>X)) path"
      by (metis H6 H7 butlast.simps(2))

    have L2H10: "\<pi> = \<pi>C @ butlast (LNxt xC # \<pi>X)"
    using H4 by blast

    have "paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"
    using H1 H6 H8 L2H10 paths_correspond_mod_chan.Chan by auto
     
    then show "paths_correspond_mod_chan (E, H) c \<pi> path"
    by (simp add: local.Chan(2))

  next
    case (Sync \<pi>Suffix pathSuffix E' \<pi>R xR \<rho>RY \<pi>S xS xSE eSY \<rho>SY \<kappa>SY xRE eRY \<kappa>RY H' pathPre)

    
    then show "paths_correspond_mod_chan (E, H) c \<pi> path"
    proof cases
      assume L1H1: "pathSuffix = []"

      have L1H2: "path = pathPre @ [(NLet xS, ESend xSE)]"
        using L1H1 local.Sync(3) by auto

      have L1H3: "\<pi>Suffix = []"
        using L1H1 local.Sync(4) paths_correspond.cases by blast

      have L1H3: "\<pi> = \<pi>R"
        using L1H3 local.Sync(2) by blast

      have "paths_correspond_mod_chan (E, H) c \<pi>R (pathPre @ [(NLet xS, ESend xSE)])" sorry

      then show ?thesis sorry
    next
      assume L1H1: "pathSuffix \<noteq> []"

      have 
        L1H2: "path = pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # (butlast pathSuffix)"
        by (metis L1H1 butlast.simps(2) butlast_append butlast_snoc list.simps(3) local.Sync(3))
      
      have L1H3: "\<pi>Suffix \<noteq> []"
        using local.Sync(4) paths_correspond.cases sorry

      have L1H4: "\<pi> = \<pi>R @ LNxt xR # (butlast \<pi>Suffix)"
        by (metis L1H3 butlast.simps(2) butlast_append butlast_snoc list.distinct(1) local.Sync(2))

      show ?thesis
      proof cases
        assume 
          L2H1: "(butlast pathSuffix) = []"

        have 
          L2H2: "path = pathPre @ [(NLet xS, ESend xSE), (NLet xR, ENext)]"
          by (simp add: L1H2 L2H1)

        have 
          L2H3: "(butlast \<pi>Suffix) = []" sorry

        have L2H4: "\<pi> = \<pi>R @ [LNxt xR]" by (simp add: L1H4 L2H3)

        have 
          "paths_correspond_mod_chan (E, H) c (\<pi>R @ [LNxt xR]) (pathPre @ [(NLet xS, ESend xSE), (NLet xR, ENext)])" sorry

        then show ?thesis
          by (simp add: L2H2 L2H4)
      next
        assume "(butlast pathSuffix) \<noteq> []"
        then show ?thesis sorry
      qed
    qed
  (*next
    third case
  *)
  qed
qed
*)


(*
lemma paths_cong_mod_chan_preserved_under_reduction_chan: "
  paths_correspond ((LNxt xC) # \<pi>Suff @ [l) (path @ [n]) \<Longrightarrow>
  E (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
  paths_correspond_mod_chan (E, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path"
using paths_cong_preserved_under_reduction paths_correspond_mod_chan.Chan by blast

lemma  paths_cong_mod_chan_preserved_under_reduction_sync: "
  paths_correspond (\<pi>Suffix @ [l) (pathSuffix @ [n]) \<Longrightarrow>
  \<E> (\<pi>R @ (LNxt xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
  dynamic_built_on_chan_var \<rho>RY c xR \<Longrightarrow>
  \<E> \<pi>S = Some (\<langle>(Let xS (Sync xSE) eSY);\<rho>SY;\<kappa>SY\<rangle>) \<Longrightarrow>
  \<E> \<pi>R = Some (\<langle>(Let xR (Sync xRE) eRY);\<rho>RY;\<kappa>RY\<rangle>) \<Longrightarrow>
  {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
  paths_correspond_mod_chan (\<E>, H) c \<pi>Severy_two pathPre \<Longrightarrow>
  paths_correspond_mod_chan (\<E>, H) c (\<pi>R @ (LNxt xR) # \<pi>Suffix) (pathPre @ (NLet xS, ESend xSE) # (NLet xR, ENext) # pathSuffix)"
by (meson paths_cong_preserved_under_reduction paths_correspond_mod_chan.Sync)
*)





end
