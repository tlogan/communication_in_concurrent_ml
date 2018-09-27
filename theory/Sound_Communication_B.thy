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
    paths_correspond \<pi> path \<Longrightarrow>
    paths_correspond (\<pi> @ [LRtn y]) (path @ [(NResult y, EReturn)])
  " 


inductive paths_correspond_mod_chan :: 
  "trace_pool * cmmn_set \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> abstract_path \<Rightarrow> bool" where
(*
is unordered necessary?
  Unordered: "
    paths_correspond \<pi> pathx \<Longrightarrow>
    \<not> (prefix pathx path) \<Longrightarrow>
    \<not> (prefix path pathx) \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) c \<pi> path
  " | *)
  Chan: "
    paths_correspond ((LNxt xC) # \<pi>Suff) path \<Longrightarrow>
    \<E> (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
    paths_correspond_mod_chan (\<E>, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path
  " |
(*  inducts on the strict prefix up to channel passing point*)
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


lemma not_static_inclusive_sound: "
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>

  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC) path1 \<Longrightarrow>
  
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC) path2 \<Longrightarrow>

  static_inclusive path1 path2
"
sorry

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

  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC) path1 \<Longrightarrow>
  
  paths_correspond_mod_chan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC) path2 \<Longrightarrow>
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 

  \<pi>1 = \<pi>2
"
  sorry

(* PATH SOUND *)

lemma not_static_traceable_sound': 

assumes
  H1: "star_left concur_step EH EH'" and
  H2: "(V, C) \<Turnstile>\<^sub>e e" and
  H3: "static_live_chan V Ln Lx xC e" and
  H4: "static_traversable V F e"
shows "
  \<forall> E' H' \<pi>' e' \<rho>' \<kappa>' isEnd.
  EH = ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) \<longrightarrow> EH' = (E', H') \<longrightarrow>
  E' \<pi>' = Some (\<langle>e';\<rho>';\<kappa>'\<rangle>) \<longrightarrow> isEnd (top_label e') \<longrightarrow>
  (\<exists> path . 
    paths_correspond_mod_chan (E', H') (Ch \<pi>C xC) \<pi>' path \<and>
    static_live_traceable V F Ln Lx (NLet xC) isEnd path)"
  sorry

lemma not_static_traceable_sound: "
  \<E>' \<pi> = Some (\<langle>(Let x b e\<^sub>n);\<rho>;\<kappa>\<rangle>) \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  isEnd (NLet x) \<Longrightarrow>
  \<exists> path . 
    paths_correspond_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi> path \<and>
    static_live_traceable V F Ln Lx (NLet xC) isEnd path
"
  sorry
(*  use induction on star_left concur_step along with deep definition of static_traversable *)



lemma send_not_static_traceable_sound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  \<exists> pathSync .
    (paths_correspond_mod_chan (\<E>', H') (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC) pathSync"
 apply (unfold is_send_path.simps; auto)
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in label_not_send_site_sound; auto?)
  apply (frule not_static_traceable_sound; auto?)
done

(* END PATH SOUND *)


theorem static_one_shot_sound': "
  every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC)) singular \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
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

theorem static_one_shot_sound: "
  \<lbrakk>
    static_one_shot V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_shot.cases; auto)
 apply (unfold one_shot.simps)
 apply (simp add: static_one_shot_sound')
done


(*
TO DO LATER:
*)

theorem noncompetitive_send_to_ordered_send: "
  every_two (static_live_traceable V F Ln Lx (NLet xC) (static_send_label V e xC)) noncompetitive \<Longrightarrow>
  static_live_chan V Ln Lx xC e \<Longrightarrow>
  static_traversable V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
  every_two (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry
(*
apply (simp add: every_two.simps noncompetitive.simps; auto)
using send_not_static_traceable_sound runtime_send_paths_are_inclusive by blast
*)

theorem static_fan_out_sound: "
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
   every_two (static_live_traceable V F Ln Lx (NLet xC) (static_recv_label V e xC)) noncompetitive \<Longrightarrow>
   static_traversable V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H') \<Longrightarrow>
   every_two (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem static_fan_in_sound: "
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


theorem static_one_to_one_sound: "
  \<lbrakk>
    static_one_to_one V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star concur_step ([[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule static_one_to_one.cases; auto)
  apply (unfold one_to_one.simps)
  apply (metis static_fan_in.intros static_fan_in_sound static_fan_out.intros static_fan_out_sound)
done

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
