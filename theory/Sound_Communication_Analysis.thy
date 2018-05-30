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

inductive is_live_split :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  Empty: "
    is_live_split \<E> (Ch \<pi>C xC) \<pi> [] \<pi>
  " | 
  Chan: "
    \<E> \<pi>C = Some (\<langle>LET xC = CHAN \<lparr>\<rparr> in e;r;k\<rangle>) \<Longrightarrow>
    \<E> (\<pi>C @ (LNext xC) # \<pi>) = Some \<sigma> \<Longrightarrow>
    is_live_split \<E> (Ch \<pi>C xC) \<pi>C ((LNext xC) # \<pi>) (\<pi>C @ (LNext xC) # \<pi>)
  " | 
  Sync_Recv: "
    \<rho>Y xE = Some (VClosure (Recv_Evt xRC) \<rho>Recv) \<Longrightarrow>
    \<E> \<pi>Pre = Some (\<langle>LET xR = SYNC xE in eY;\<rho>Y;\<kappa>Y\<rangle>) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c xR \<Longrightarrow>
    \<E> (\<pi>Pre ;; (LNext xR)) = Some (\<langle>e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
    \<E> (\<pi>Pre @ (LNext xR) # \<pi>) = Some \<sigma> \<Longrightarrow>
    is_live_split \<E> c \<pi>Pre ((LNext xR) # \<pi>) (\<pi>Pre @ (LNext xR) # \<pi>) 
  "

inductive paths_congruent :: "trace_pool \<Rightarrow> control_path \<Rightarrow> control_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty: "
    paths_congruent \<E> \<pi>Pre [] []
  " |
  Next: "
    paths_congruent \<E> \<pi>Pre \<pi> path \<Longrightarrow>
    b = SYNC xE \<longrightarrow> \<rho> xE \<noteq> Some (VClosure (Send_Evt xSC xM) \<rho>Send) \<Longrightarrow>
    \<E> (\<pi>Pre) = Some (\<langle>LET x = b in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
    \<E> (\<pi>Pre @ (LNext x # \<pi>)) = Some \<sigma> \<Longrightarrow>
    paths_congruent \<E> \<pi>Pre (LNext x # \<pi>) ((NLet x, ENext) # path)
  " |
  Call: "
    paths_congruent \<E> \<pi>Pre \<pi> path \<Longrightarrow>
    \<E> (\<pi>Pre @ (LCall x # \<pi>)) = Some \<sigma> \<Longrightarrow>
    paths_congruent \<E> \<pi>Pre (LCall x # \<pi>) ((NLet x, ECall x) # path)
  " |
  Return: "
    paths_congruent \<E> \<pi>Pre \<pi> path \<Longrightarrow>
    \<E> (\<pi>Pre @ (LReturn x # \<pi>)) = Some \<sigma> \<Longrightarrow>
    paths_congruent \<E> \<pi>Pre (LReturn x # \<pi>) ((NLet x, EReturn x) # path)
  " |
  Spawn: "
    paths_congruent \<E> \<pi>Pre \<pi> path \<Longrightarrow>
    \<E> (\<pi>Pre @ (LSpawn x # \<pi>)) = Some \<sigma> \<Longrightarrow>
    paths_congruent \<E> \<pi>Pre (LSpawn x # \<pi>) ((NLet x, ESpawn) # path)
  " |
  Send: "
    paths_congruent \<E> \<pi>Pre \<pi> path \<Longrightarrow>
    \<rho> xE = Some (VClosure (Send_Evt xSC xM) \<rho>Send) \<Longrightarrow>
    \<E> \<pi>Pre = Some (\<langle>LET x = SYNC xE in e;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
    \<E> (\<pi>Pre @ (LNext x # \<pi>)) = Some \<sigma> \<Longrightarrow>
    paths_congruent \<E> \<pi>Pre (LNext x # \<pi>) ((NLet x, ESend xM) # path)
  "


inductive paths_congruent_mod_chan :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> static_path \<Rightarrow> bool" where
  Intro: "
    suffix pathSuffix path \<Longrightarrow>
    paths_congruent \<E> \<pi>Pre \<pi>Suffix pathSuffix \<Longrightarrow>
    is_live_split \<E> (Ch \<pi>C xC) \<pi>Pre \<pi>Suffix \<pi> \<Longrightarrow>
    paths_congruent_mod_chan \<E> (Ch \<pi>C xC) \<pi> path
  "

inductive is_sync_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro: "
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x\<^sub>e \<Longrightarrow>
    is_sync_path \<E> c \<pi>\<^sub>y
  "

lemma static_paths_of_same_run_inclusive: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 

  is_sync_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_sync_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 

  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
(*
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow> 
*)
  path1 \<asymp> path2
"
proof -

  assume
    H1: "[[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'" and
    H2: "is_sync_path \<E>' (Ch \<pi> xC) \<pi>1" and
    H3: "is_sync_path \<E>' (Ch \<pi> xC) \<pi>2" and
    H4: "paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>1 path1" and
    H5: "paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>2 path2"

  from H1 have
    "star_left (op \<rightarrow>) [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<E>'" by (simp add: star_implies_star_left)

  then obtain E0 where 
    H6: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
    H7: "star_left (op \<rightarrow>) E0 \<E>'" by auto

  from H7 have 
    H8: "
      \<forall> \<pi>1 \<pi>2 path1 path2.
      E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<longrightarrow>
      is_sync_path \<E>' (Ch \<pi> xC) \<pi>1 \<longrightarrow>
      is_sync_path \<E>' (Ch \<pi> xC) \<pi>2 \<longrightarrow>
      paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>1 path1 \<longrightarrow>
      paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>2 path2 \<longrightarrow>
      path1 \<asymp> path2
    "
  proof induction
    case (refl E0)
    {
      fix \<pi>1 \<pi>2 path1 path2 
      assume 
        L2H1: "E0 = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]" and
        L2H2: "is_sync_path E0 (Ch \<pi> xC) \<pi>1" and
        L2H3: "is_sync_path E0 (Ch \<pi> xC) \<pi>2" and
        L2H4: "paths_congruent_mod_chan E0 (Ch \<pi> xC) \<pi>1 path1" and
        L2H5: "paths_congruent_mod_chan E0 (Ch \<pi> xC) \<pi>2 path2"

       have "path1 \<asymp> path2" sorry
    }

    then show ?case by blast
  next
    case (step E0 E E')
    then show ?case sorry
  qed

  from H2 H3 H4 H5 H6 H8 show 
    "path1 \<asymp> path2" by simp
qed

lemma is_send_path_to_sync_path: "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  is_sync_path \<E> (Ch \<pi>C xC) \<pi>
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  from H1
  have
    "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e . 
      \<E> \<pi> = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<and> 
      \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<and> 
      \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>C xC))
    " using is_send_path.simps by auto

  then obtain x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e where
    H2: "\<E> \<pi> = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) " and
    H3: "\<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e)" and
    H4: "\<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>C xC))" by blast

  from H4 have
    H5: "dynamic_built_on_chan_var \<rho>\<^sub>e (Ch \<pi>C xC) x\<^sub>s\<^sub>c"
  by (simp add: dynamic_built_on_chan_var_dynamic_built_on_chan_prim_dynamic_built_on_chan_bindee_dynamic_built_on_chan_exp.Chan)

  from H5 have
    H6: "dynamic_built_on_chan_prim \<rho>\<^sub>e (Ch \<pi>C xC) (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m)"
  by (simp add: dynamic_built_on_chan_var_dynamic_built_on_chan_prim_dynamic_built_on_chan_bindee_dynamic_built_on_chan_exp.Send_Evt)

  from H3 H6 have
    H7: "dynamic_built_on_chan_var \<rho> (Ch \<pi>C xC) x\<^sub>e" using Closure by blast

  from H2 H7 show 
    "is_sync_path \<E> (Ch \<pi>C xC) \<pi>" by (simp add: is_sync_path.intros)
qed

lemma send_static_paths_of_same_run_inclusive: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow> 
  path1 \<asymp> path2
"
by (metis is_send_path_to_sync_path static_paths_of_same_run_inclusive)


lemma send_path_equality_sound: "
  path1 = path2 \<Longrightarrow>
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow> 
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>1 \<Longrightarrow> 
  is_send_path \<E>' (Ch \<pi> xC) \<pi>2 \<Longrightarrow> 
  \<pi>1 = \<pi>2
"
sorry


lemma send_static_paths_equal_exclusive_implies_dynamic_paths_equal: "
  path1 = path2 \<or> \<not> path1 \<asymp> path2 \<Longrightarrow> 
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>\<^sub>1 path1 \<Longrightarrow>
  paths_congruent_mod_chan \<E>' (Ch \<pi> xC) \<pi>\<^sub>2 path2 \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
    (V, C) \<Turnstile>\<^sub>e e
  \<rbrakk> \<Longrightarrow> 
  ^Chan xC \<in> V x\<^sub>s\<^sub>c
"
 apply (frule may_be_static_eval_to_pool)
 apply (drule may_be_static_eval_preserved_under_concur_step_star[of _ _ _ \<E>']; assumption?)
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>';
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
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_congruent_mod_chan \<E>' (Ch \<pi>C xC) \<pi> path \<and>
    may_be_static_live_path V F Ln Lx (NLet xC) isEnd path
"
sorry

lemma isnt_send_site_sound: "
  \<E>' \<pi>Sync = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n;\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<Longrightarrow>
  \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan (Ch \<pi>C xC)) \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
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
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  \<exists> pathSync .
    (paths_congruent_mod_chan \<E>' (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
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
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow> 
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_shot.cases; auto)
 apply (unfold one_shot.simps)
 apply (simp add: one_shot_sound')
done


theorem noncompetitive_send_to_ordered_send: "
  every_two_static_paths (may_be_static_live_path V F Ln Lx (NLet xC) (may_be_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
  static_chan_liveness V Ln Lx xC e \<Longrightarrow>
  static_flow_set V F (may_be_static_recv_node_label V e) e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
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
   [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
   every_two_dynamic_paths (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem fan_in_sound: "
  \<lbrakk>
    static_fan_in V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
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
    [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_to_one.cases; auto)
 apply (unfold one_to_one.simps)
 apply (simp add: noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send)
done


end