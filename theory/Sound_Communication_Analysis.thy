theory Sound_Communication_Analysis
  imports 
    Main
    Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Static_Framework Sound_Framework
    Dynamic_Communication_Analysis Static_Communication_Analysis
begin

(*


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


*)

inductive 
  dynamic_built_on_chan_var :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> var \<Rightarrow> bool" and
  dynamic_built_on_chan_prim :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> prim \<Rightarrow> bool" and
  dynamic_built_on_chan_bindee :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> bind \<Rightarrow> bool" and
  dynamic_built_on_chan_exp :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> exp \<Rightarrow> bool" 
where
  Chan: "
    \<rho> x = Some (VChan c) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |
  Closure: "
    dynamic_built_on_chan_prim \<rho>' c p \<Longrightarrow>
    \<rho> x = Some (VClosure p \<rho>') \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |


  Send_Evt: "
    dynamic_built_on_chan_var \<rho> c xSC \<or> dynamic_built_on_chan_var \<rho> c xM \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Send_Evt xSC xM)
  " |
  Recv_Evt: "
    dynamic_built_on_chan_var \<rho> c xRC \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Recv_Evt xRC)
  " |
  Pair: "
    dynamic_built_on_chan_var \<rho> c x1 \<or> dynamic_built_on_chan \<rho> c x2 \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Pair x1 x2)
  " |
  Left: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Left xSum)
  " |
  Right: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Right xSum)
  " |
  Abs: "
    dynamic_built_on_chan_exp \<rho>' c e \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Abs f x e)
  " |

  Prim: "
    dynamic_built_on_chan_prim \<rho> c p \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (Prim p)
  " |
  Spawn: "
    dynamic_built_on_chan_exp \<rho> c eCh \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (SPAWN eCh)
  " |
  Sync: "
    dynamic_built_on_chan_var \<rho> c xY \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (SYNC xY)
  " |
  Fst: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (FST xP)
  " |
  Snd: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (SND xP)
  " |
  Case: "
    dynamic_built_on_chan_var \<rho> c xS \<or> 
    dynamic_built_on_chan_exp \<rho> c eL \<or> dynamic_built_on_chan_exp \<rho> c eR \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (CASE xS LEFT xL |> eL RIGHT xR |> eR)
  " |
  App: "
    dynamic_built_on_chan_var \<rho> c f \<or>
    dynamic_built_on_chan_var \<rho> c xA \<Longrightarrow>
    dynamic_built_on_chan_bindee \<rho> c (APP f xA)
  " |

  Result: "
    dynamic_built_on_chan_var \<rho> c x \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (RESULT x)
  " |
  Let: "
    dynamic_built_on_chan_bindee \<rho> c b \<or> dynamic_built_on_chan_exp \<rho> c e \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (LET x = b in e)
  "


inductive nodes_congruent :: "control_label \<Rightarrow> step_label \<Rightarrow> bool" where
  Next: "
    nodes_congruent (LNext x) (NLet x, ENext)" |
  Call: "
    nodes_congruent (LCall x) (NLet x, ECall x)" |
  Return: "
    nodes_congruent (LReturn y) (NResult y, EReturn x)" |
  Spawn: "
    nodes_congruent (LSpawn x) (NLet x, ESpawn)"


inductive paths_congruent :: "control_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Node: "
    nodes_congruent l n \<Longrightarrow>
    paths_congruent [l] [n]
  " |
  List: "
    \<pi> \<noteq> [] \<Longrightarrow> path \<noteq> [] \<Longrightarrow>
    nodes_congruent l n \<Longrightarrow>
    paths_congruent \<pi> path \<Longrightarrow>
    paths_congruent (l # \<pi>) (n # path)
  "

inductive paths_congruent_mod_chan :: "trace_pool * com_set \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Chan: "
    paths_congruent ((LNext xC) # \<pi>) path \<Longrightarrow>
    \<E> (\<pi>C @ (LNext xC) # \<pi>) \<noteq> None \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) (Ch \<pi>C xC) (\<pi>C @ (LNext xC) # \<pi>) path
  " |
  Sync: "
    paths_congruent \<pi>Suffix pathSuffix \<Longrightarrow>
    \<E> (\<pi>R @ (LNext xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
    dynamic_built_on_chan_var \<rho>RY c xR \<Longrightarrow>
    \<E> \<pi>S = Some (\<langle>LET xS = SYNC xSE in eSY;\<rho>SY;\<kappa>SY\<rangle>) \<Longrightarrow>
    \<E> \<pi>R = Some (\<langle>LET xR = SYNC xRE in eRY;\<rho>RY;\<kappa>RY\<rangle>) \<Longrightarrow>
    {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) c \<pi>S path \<Longrightarrow>
    paths_congruent_mod_chan (\<E>, H) c (\<pi>R @ (LNext xR) # \<pi>Suffix) (path @ (NLet xS, ESend xSE) # (NLet xR, ENext) # pathSuffix)
  "


lemma no_empty_paths_congruent_mod_chan: "
  \<not> (paths_congruent_mod_chan EH c [] path)"
  apply (rule notI)
  apply (erule paths_congruent_mod_chan.cases; auto)
done

lemma static_paths_of_same_run_inclusive_base: "
  E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<Longrightarrow>
  E0 \<pi>1 \<noteq> None \<Longrightarrow>
  E0 \<pi>2 \<noteq> None \<Longrightarrow>
  paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow> 
  paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
proof -
  assume 
    H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H2: "E0 \<pi>1 \<noteq> None" and
    H3: "E0 \<pi>2 \<noteq> None" and
    H4: "paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_congruent_mod_chan (E0, {}) (Ch \<pi> xC) \<pi>2 path2"
  from H1 H2 H4 show 
    "path1 \<asymp> path2" 
    by (metis fun_upd_apply no_empty_paths_congruent_mod_chan)
qed

lemma paths_equal_implies_paths_inclusive: "
  path1 = path2  \<Longrightarrow> path1 \<asymp> path2 
"
by (simp add: Prefix2)

lemma "
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
\<pi> \<noteq> [] \<Longrightarrow> path \<noteq> [] \<Longrightarrow>
paths_congruent_mod_chan (E', H') (Ch \<pi>C xC) (\<pi> ;; l) (path @ [node]) \<Longrightarrow>
paths_congruent_mod_chan (E, H) (Ch \<pi>C xC) \<pi> path"


apply (erule paths_congruent_mod_chan.cases; auto)
apply (erule paths_congruent.cases; auto)
apply (erule nodes_congruent.cases; auto)
apply (case_tac "\<pi> \<noteq> \<pi>C @ LNext xC # (butlast \<pi>')"; auto?)
apply (metis butlast.simps(2) butlast_append butlast_snoc list.simps(3))
apply (case_tac "path \<noteq> (NLet xC, ENext) # (butlast patha)"; auto?)
apply (metis butlast.simps(2) butlast_snoc)
apply (erule paths_congruent.cases; auto)
defer
thm paths_congruent.intros

sorry


lemma static_paths_of_same_run_inclusive_step: "
star_left op \<rightarrow> ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (E, H) \<Longrightarrow>
\<forall>\<pi>1 \<pi>2 path1 path2.
  \<pi>1 \<noteq> \<pi>2 \<longrightarrow>
  E \<pi>1 \<noteq> None \<longrightarrow>
  E \<pi>2 \<noteq> None \<longrightarrow>
  paths_congruent_mod_chan (E, H) (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow> 
  paths_congruent_mod_chan (E, H) (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow> 
  path1 \<asymp> path2 \<Longrightarrow>
(E, H) \<rightarrow> (E', H') \<Longrightarrow>
\<pi>1 \<noteq> \<pi>2 \<Longrightarrow>
E' \<pi>1 \<noteq> None \<Longrightarrow>
E' \<pi>2 \<noteq> None \<Longrightarrow>
paths_congruent_mod_chan (E', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow> 
paths_congruent_mod_chan (E', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
path1 \<asymp> path2 
"
sorry

lemma static_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  \<pi>1 \<noteq> \<pi>2 \<Longrightarrow>
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  path1 \<asymp> path2
"
proof -

  assume
    H0: "\<pi>1 \<noteq> \<pi>2" and
    H1: "([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H')" and
    H2: "\<E>' \<pi>1 \<noteq> None" and
    H3: "\<E>' \<pi>2 \<noteq> None" and
    H4: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

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
      \<pi>1 \<noteq> \<pi>2 \<longrightarrow>
      \<E>' \<pi>1 \<noteq> None \<longrightarrow>
      \<E>' \<pi>2 \<noteq> None \<longrightarrow>
      paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow>
      paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow>
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
        L2H2A: "\<pi>1 \<noteq> \<pi>2" and
        L2H3: "\<E>' \<pi>1 \<noteq> None" and
        L2H4: "\<E>' \<pi>2 \<noteq> None" and
        L2H5: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1" and
        L2H6: "paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2"

      obtain \<E> H where 
        L2H7: "y = (\<E>, H)" by (meson surj_pair)

      from L2H1 L2H7 step.IH have 
        L2H8: "
          \<forall> \<pi>1 \<pi>2 path1 path2 . 
          \<pi>1 \<noteq> \<pi>2 \<longrightarrow>
          \<E> \<pi>1 \<noteq> None \<longrightarrow>
          \<E> \<pi>2 \<noteq> None \<longrightarrow>
          paths_congruent_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow> 
          paths_congruent_mod_chan (\<E>, H) (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow> 
          path1 \<asymp> path2 "
        by blast

      from L2H2 L2H3 L2H4 L2H5 L2H6 L2H7 L2H8 L2H1 L2H2A step.hyps(1) step.hyps(2) have 
        "path1 \<asymp> path2" using static_paths_of_same_run_inclusive_step by presburger
    }
    then show ?case by blast
  qed

  from H0 H2 H3 H4 H5 H6(1) H6(2) H8 show 
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



lemma equal_concrete_implies_equal_abstract_paths: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  paths_congruent_mod_chan (E', H') c \<pi> path1 \<Longrightarrow>
  paths_congruent_mod_chan (E', H') c \<pi> path2 \<Longrightarrow>
  path1 = path2"
sorry

lemma send_static_paths_of_same_run_inclusive: "
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow> 
  path1 \<asymp> path2
"
apply (case_tac "\<pi>1 = \<pi>2")
  apply (simp add: equal_concrete_implies_equal_abstract_paths paths_equal_implies_paths_inclusive)
  apply (simp add: is_send_path_implies_nonempty_pool static_paths_of_same_run_inclusive)
done

lemma send_path_equality_sound: "
  path1 = path2 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow> 
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  \<pi>1 = \<pi>2
"
sorry



lemma send_static_paths_equal_exclusive_implies_dynamic_paths_equal: "
  path1 = path2 \<or> \<not> path1 \<asymp> path2 \<Longrightarrow> 
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>\<^sub>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>\<^sub>2 path2 \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>1 \<Longrightarrow>
  is_send_path \<E>' (Ch \<pi> xC) \<pi>\<^sub>2 \<Longrightarrow>
  \<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (simp add: send_static_paths_of_same_run_inclusive send_path_equality_sound)


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

lemma isnt_path_sound: "
  \<E>' \<pi> = Some (\<langle>LET x = b in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> z \<noteq> None \<Longrightarrow>
  dynamic_built_on_chan_var \<rho> (Ch \<pi>C xC) z \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_congruent_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi> path \<and>
    may_be_static_live_path V F Ln Lx (NLet xC) isEnd path
"
sorry

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
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  \<exists> pathSync .
    (paths_congruent_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = x\<^sub>s\<^sub>c and \<pi>C = \<pi>C and \<rho>\<^sub>e = \<rho>\<^sub>e in isnt_send_site_sound; auto?)
 apply (frule isnt_path_sound; auto?)
  apply (auto simp: 
    dynamic_built_on_chan_var.simps 
    dynamic_built_on_chan_var_dynamic_built_on_chan_prim_dynamic_built_on_chan_bindee_dynamic_built_on_chan_exp.Send_Evt 
  )
done


theorem one_shot_sound': "
  every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) singular \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
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
 apply (simp add: send_static_paths_equal_exclusive_implies_dynamic_paths_equal)
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

(*
TO DO LATER:
*)
(*
theorem noncompetitive_send_to_ordered_send: "
  every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<rightarrow>* (\<E>', H') \<Longrightarrow>
  every_two_dynamic_paths (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry
(*
apply (simp add: every_two_dynamic_paths.simps noncompetitive.simps; auto)
using isnt_send_path_sound runtime_send_paths_are_inclusive by blast
*)

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
   every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
   static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
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
*)

end