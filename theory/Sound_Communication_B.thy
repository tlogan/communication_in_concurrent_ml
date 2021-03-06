theory Sound_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Dynamic_Communication Static_Communication Sound_Communication
    Static_Communication_B
begin


inductive 
  staticFlowsAcceptEnv :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> env \<Rightarrow> bool"  and
  staticFlowsAcceptVal :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> val \<Rightarrow> bool"
where
  StaticFlowsAcceptEnv:
  "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>  staticFlowsAcceptVal V F t0 \<omega> \<Longrightarrow>
    staticFlowsAcceptEnv V F t0 \<rho>
  "
| Unit:
  "
    staticFlowsAcceptVal V F t0 VUnt
  "
| Chan:
  "
    staticFlowsAcceptVal V F t0 (VChn c)
  "
| SendEvt:
  "
    staticFlowsAcceptEnv V F t0 \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F t0 (VClsr (SendEvt _ _) \<rho>)
  "
| RecvEvt:
  "
    staticFlowsAcceptEnv V F t0 \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F t0 (VClsr (RecvEvt _) \<rho>)
  "
| Left:
  "
    staticFlowsAcceptEnv V F t0 \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F t0 (VClsr (Lft _) \<rho>)
  "
| Right:
  "
    staticFlowsAcceptEnv V F t0 \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F t0 (VClsr (Rht _) \<rho>)
  "
| Fun:
  "
    staticFlowsAcceptTm V F t0 e \<Longrightarrow> 
    staticFlowsAcceptEnv V F t0 \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F t0 (VClsr (Fun f x e) \<rho>)
  "
| Pair:
  "
    staticFlowsAcceptEnv V F t0 \<rho> \<Longrightarrow>
    staticFlowsAcceptVal V F t0 (VClsr (Pair _ _) \<rho>)
  " 


inductive staticFlowsAcceptStack :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> name \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty: "staticFlowsAcceptStack V F t0 y []"
| Nonempty:
  "
    \<lbrakk> 
      {(IdRslt y, EReturn, tmId e)} \<subseteq> F;
      staticFlowsAcceptTm V F t0 e;
      staticFlowsAcceptEnv V F t0 \<rho>;
      staticFlowsAcceptStack V F t0 (\<lfloor>e\<rfloor>) \<kappa>
    \<rbrakk> \<Longrightarrow> 
    staticFlowsAcceptStack V F t0 y ((Ctn x e \<rho>) # \<kappa>)
  "

inductive staticFlowsAcceptPool :: "static_env \<Rightarrow> flow_set \<Rightarrow> tm \<Rightarrow> trace_pool \<Rightarrow> bool"  where
  Intro:
  "
    (\<forall> \<pi> e \<rho> \<kappa> . E \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow> 
      staticFlowsAcceptTm V F t0 e \<and>
      staticFlowsAcceptEnv V F t0 \<rho> \<and>
      staticFlowsAcceptStack V F t0 (\<lfloor>e\<rfloor>) \<kappa>) \<Longrightarrow> 
    staticFlowsAcceptPool V F t0 E
  "

inductive 
  staticLiveChanEnv :: "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> env \<Rightarrow> bool"  and
  staticLiveChanVal :: "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> val \<Rightarrow> bool"
where
  StaticLiveChanEnv:
  "
    \<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>  staticLiveChanVal V Ln Lx x\<^sub>c \<omega> \<Longrightarrow>
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho>
  "
| StaticLiveChanUnit:
  "
    staticLiveChanVal V Ln Lx x\<^sub>c VUnt
  "
| StaticLiveChan:
  "
    staticLiveChanVal V Ln Lx x\<^sub>c (VChn c)
  "
| StaticLiveChanSendEvt:
  "
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<Longrightarrow>
    staticLiveChanVal V Ln Lx x\<^sub>c (VClsr (SendEvt _ _) \<rho>)
  "
| StaticLiveChanRecvEvt:
  "
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<Longrightarrow>
    staticLiveChanVal V Ln Lx x\<^sub>c (VClsr (RecvEvt _) \<rho>)
  "
| StaticLiveChanLeft:
  "
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<Longrightarrow>
    staticLiveChanVal V Ln Lx x\<^sub>c (VClsr (Lft _) \<rho>)
  "
| StaticLiveChanRight:
  "
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<Longrightarrow>
    staticLiveChanVal V Ln Lx x\<^sub>c (VClsr (Rht _) \<rho>)
  "
| StaticLiveChanFun:
  "
    staticLiveChan V Ln Lx x\<^sub>c e \<Longrightarrow> 
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<Longrightarrow>
    staticLiveChanVal V Ln Lx x\<^sub>c (VClsr (Fun f x e) \<rho>)
  "
| StaticLiveChanPair:
  "
    staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<Longrightarrow>
    staticLiveChanVal V Ln Lx x\<^sub>c (VClsr (Pair _ _) \<rho>)
  " 


inductive staticLiveChanStack :: "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> name \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty: "staticLiveChanStack V Ln Lx x\<^sub>c x\<^sub>r []"
| Nonempty:
  "
    \<lbrakk> 
      \<not> Set.is_empty (Lx (IdRslt x\<^sub>r));
      \<not> Set.is_empty (Ln (tmId e));
      staticLiveChan V Ln Lx x\<^sub>c e;
      staticLiveChanEnv V Ln Lx x\<^sub>c \<rho>; 
      staticLiveChanStack V Ln Lx x\<^sub>c (resultName e) \<kappa>
    \<rbrakk> \<Longrightarrow> 
    staticLiveChanStack V Ln Lx x\<^sub>c x\<^sub>r ((Ctn x e \<rho>) # \<kappa>)
  "


inductive staticLiveChanPool ::  "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> trace_pool \<Rightarrow> bool"  where
  Intro:
  "
    (\<forall> \<pi> e \<rho> \<kappa> . pool \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
      staticLiveChan V Ln Lx x\<^sub>c e \<and>
      staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<and>
      staticLiveChanStack V Ln Lx x\<^sub>c (resultName e) \<kappa>) \<Longrightarrow>
    staticLiveChanPool V Ln Lx x\<^sub>c pool
  "

lemma staticInclusive_commut: "
  staticInclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> staticInclusive path\<^sub>2 path\<^sub>1
"
 apply (erule staticInclusive.cases; auto)
  apply (simp add: Prefix2)
  apply (simp add: Prefix1)
  apply (simp add: Spawn2)
  apply (simp add: Spawn1)
  apply (simp add: Send2)
  apply (simp add: Send1)
done


lemma staticInclusivePreservedDynamicEval_under_unordered_extension: "
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> 
  staticInclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  staticInclusive (path\<^sub>1 @ [l]) path\<^sub>2
"
 apply (erule staticInclusive.cases; auto)
  apply (simp add: Spawn1)
  apply (simp add: Spawn2)
  apply (simp add: Send1)
  apply (simp add: Send2)
done

lemma staticInclusivePreservedDynamicEval_under_unordered_double_extension: "
  staticInclusive path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  \<not> prefix path\<^sub>1 path\<^sub>2 \<Longrightarrow> 
  \<not> prefix path\<^sub>2 path\<^sub>1 \<Longrightarrow> 
  staticInclusive (path\<^sub>1 @ [l1]) (path\<^sub>2 @ [l2])
"
by (metis staticInclusive_commut staticInclusivePreservedDynamicEval_under_unordered_extension prefix_append prefix_def)


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
    pathsCongruent (\<pi> @ [LRtn y]) (path @ [(IdRslt y, EReturn)])
  "


inductive pathsCongruentModChan :: 
  "tm \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> static_path \<Rightarrow> bool" 
where
  Chan:
  "
    pathsCongruent ((LNxt xC) # \<pi>Suff) path \<Longrightarrow>
    pathsCongruentModChan t0 (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path
  "
| Sync:
  "
    star dynamicEval ([[] \<mapsto> (Stt t0 empty [])], {}) (\<E>, comm) \<Longrightarrow>
    \<E> \<pi>S = Some (Stt (Bind xS (Sync xSE) eSY) \<rho>SY \<kappa>SY) \<Longrightarrow>
    \<E> \<pi>R = Some (Stt (Bind xR (Sync xRE) eRY) \<rho>RY \<kappa>RY) \<Longrightarrow>
    {(\<pi>S, c_c, \<pi>R)} \<subseteq> comm \<Longrightarrow> 
    \<rho>RY xR = Some vR \<Longrightarrow>
    dynamicBuiltOnChanVal vR c \<Longrightarrow>
    pathsCongruentModChan t0 c \<pi>S pathPre \<Longrightarrow>
    pathsCongruent \<pi>Suffix pathSuffix \<Longrightarrow>
    pathsCongruentModChan t0 c 
      (\<pi>R @ (LNxt xR) # \<pi>Suffix) 
      (pathPre @ (IdBind xS, ESend xSE) # (IdBind xR, ENext) # pathSuffix)
  "

lemma pathsCongruentModChanPreservedSnoc:
  "
    pathsCongruentModChan t0 c \<pi> path \<Longrightarrow>
    pathsCongruent [site] [step] \<Longrightarrow>
    pathsCongruentModChan t0 c (\<pi> @ [site]) (path @ [step])
  "
sorry


lemma staticInclusiveSound: "
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>

  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  pathsCongruentModChan e (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC) path1 \<Longrightarrow>
  
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  pathsCongruentModChan e (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC) path2 \<Longrightarrow>

  staticInclusive path1 path2
"
sorry

lemma is_send_path_implies_nonempty_pool: "
  is_send_path \<E> (Ch \<pi>C xC) \<pi> \<Longrightarrow> 
  \<E> \<pi> \<noteq> None
"
proof -
  assume H1: "is_send_path \<E> (Ch \<pi>C xC) \<pi>"
  
  then have
    H2:
  "
      \<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<rho> \<kappa>. \<E> \<pi> = Some (Stt (Bind x\<^sub>y (Sync x\<^sub>e) e\<^sub>n) \<rho> \<kappa>) 
    " using is_send_path.simps by auto

  then show 
    "\<E> \<pi> \<noteq> None" by blast
qed


lemma static_equalitySound: "
  path1 = path2 \<Longrightarrow>

  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  
  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  pathsCongruentModChan e (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC) path1 \<Longrightarrow>
  
  pathsCongruentModChan e (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC) path2 \<Longrightarrow>
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 

  \<pi>1 = \<pi>2
"
  sorry

(* PATH SOUND *)

lemma staticFlowsAcceptPoolPreservedReturn: 
"
  staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left dynamicEval ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticFlowsAcceptPool V F e0 [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Rslt x) env (Ctn xk ek envk # k)) \<Longrightarrow>
  env x = Some v \<Longrightarrow>
  staticFlowsAcceptPool V F e0 (Em(pi @ [LRtn x] \<mapsto> Stt ek (envk(xk \<mapsto> v)) k))
"
apply (rule staticFlowsAcceptPool.Intro; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptStack.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)
  apply (drule spec[of _ x]; auto)
  apply (erule staticFlowsAcceptStack.cases; auto)
  apply (simp add: staticFlowsAcceptEnv.simps)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptStack.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)+
done

lemma staticFlowsAcceptPoolPreservedSeqEval:
"
staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
(V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
staticFlowsAcceptPool V F e0 [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
leaf Em pi \<Longrightarrow>
Em pi = Some (Stt (Bind x b e) env k) \<Longrightarrow>
seqEval b env v \<Longrightarrow>
staticFlowsAcceptPool V F e0 (Em(pi @ [LNxt x] \<mapsto> Stt e (env(x \<mapsto> v)) k))
"
apply (rule staticFlowsAcceptPool.Intro; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (frule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule seqEval.cases; auto)

    apply (simp add: staticFlowsAcceptEnv.simps staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit)

    apply (erule staticFlowsAcceptTm.cases; auto)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (rotate_tac -2)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (smt map_upd_Some_unfold staticFlowsAcceptEnv.cases StaticFlowsAcceptEnv staticFlowsAcceptEnv_staticFlowsAcceptVal.SendEvt)
      
      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (rotate_tac -2)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (smt map_upd_Some_unfold staticFlowsAcceptEnv.cases StaticFlowsAcceptEnv staticFlowsAcceptEnv_staticFlowsAcceptVal.RecvEvt)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (rotate_tac -2)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (smt map_upd_Some_unfold staticFlowsAcceptEnv.cases StaticFlowsAcceptEnv staticFlowsAcceptEnv_staticFlowsAcceptVal.Pair)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (rotate_tac -2)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (smt map_upd_Some_unfold staticFlowsAcceptEnv.cases StaticFlowsAcceptEnv staticFlowsAcceptEnv_staticFlowsAcceptVal.Left)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (rotate_tac -2)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (smt map_upd_Some_unfold staticFlowsAcceptEnv.cases StaticFlowsAcceptEnv staticFlowsAcceptEnv_staticFlowsAcceptVal.Right)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (rotate_tac -2)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (smt map_upd_Some_unfold staticFlowsAcceptEnv.cases staticFlowsAcceptEnv_staticFlowsAcceptVal.Fun StaticFlowsAcceptEnv)


   apply (frule staticFlowsAcceptPool.cases; auto)
   apply (drule spec[of _pi]; auto)
   apply (erule staticFlowsAcceptEnv.cases; auto)
   apply (drule_tac x = "xp" in spec; auto)
   apply (erule staticFlowsAcceptVal.cases; auto)
   apply (rename_tac xp envp x1 x2)
   apply (erule staticFlowsAcceptEnv.cases; auto)
   apply (drule_tac x = "x1" in spec; auto)
   apply (erule staticFlowsAcceptPool.cases; auto)
   apply (drule spec[of _pi]; auto)
   apply (simp add: staticFlowsAcceptEnv.simps)

   apply (frule staticFlowsAcceptPool.cases; auto)
   apply (drule spec[of _pi]; auto)
   apply (erule staticFlowsAcceptEnv.cases; auto)
   apply (drule_tac x = "xp" in spec; auto)
   apply (erule staticFlowsAcceptVal.cases; auto)
   apply (rename_tac xp envp x1 x2)
   apply (erule staticFlowsAcceptEnv.cases; auto)
   apply (drule_tac x = "x2" in spec; auto)
   apply (erule staticFlowsAcceptPool.cases; auto)
   apply (drule spec[of _pi]; auto)
   apply (simp add: staticFlowsAcceptEnv.simps)

 apply (erule staticFlowsAcceptPool.cases; auto)
 apply (drule spec[of _pi]; auto)

 apply (erule staticFlowsAcceptPool.cases; auto)+

done

lemma staticFlowsAcceptPoolPreservedCallEval:
"
staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
(V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
staticFlowsAcceptPool V F e0 [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
leaf Em pi \<Longrightarrow>
Em pi = Some (Stt (Bind x b e) env k) \<Longrightarrow>
callEval (b, env) (e', env') \<Longrightarrow>
staticFlowsAcceptPool V F e0 (Em(pi @ [LCall x] \<mapsto> Stt e' env' (Ctn x e env # k)))
"
apply (rule staticFlowsAcceptPool.Intro; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule callEval.cases; auto)
    apply (erule staticFlowsAcceptTm.cases; auto)
    apply (erule staticFlowsAcceptTm.cases; auto)
    apply (erule staticFlowsAcceptEnv.cases; auto)
    apply (drule_tac x = "f" in spec; auto)
    apply (erule staticFlowsAcceptVal.cases; auto)
  apply (erule callEval.cases; auto)
    apply (erule staticFlowsAcceptPool.cases; auto)
    apply (drule spec[of _ pi]; auto)
    apply (frule staticFlowsAcceptEnv.cases; auto)
    apply (drule_tac x = "xs" in spec; auto)
    apply (erule staticFlowsAcceptVal.cases; auto)
    apply (rename_tac xs vl xl xr er envl xl')
    apply (rotate_tac -1)
    apply (erule staticFlowsAcceptEnv.cases; auto)
    apply (rename_tac xs vl xl xr er xl' envl)
    apply (drule_tac x = "xl'" in spec; auto)
    apply (simp add: staticFlowsAcceptEnv.simps)

    apply (erule staticFlowsAcceptPool.cases; auto)
    apply (drule spec[of _ pi]; auto)
    apply (frule staticFlowsAcceptEnv.cases; auto)
    apply (drule_tac x = "xs" in spec; auto)
    apply (erule staticFlowsAcceptVal.cases; auto)
    apply (rename_tac xs vl xl xr er envr xr')
    apply (rotate_tac -1)
    apply (erule staticFlowsAcceptEnv.cases; auto)
    apply (rename_tac xs vl xl xr er xr' envr)
    apply (drule_tac x = "xr'" in spec; auto)
    apply (simp add: staticFlowsAcceptEnv.simps)

    apply (rule StaticFlowsAcceptEnv; auto)
      
      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptEnv.cases; auto)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptEnv.cases; auto)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptEnv.cases; auto)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptEnv.cases; auto)
      apply (drule_tac x = "f" in spec; auto)
      apply (erule staticFlowsAcceptVal.cases; auto)
      apply (erule staticFlowsAcceptEnv.cases; auto)

    apply (erule callEval.cases; auto)
      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (simp add: staticFlowsAcceptStack.Nonempty)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (simp add: staticFlowsAcceptStack.Nonempty)

      apply (erule staticFlowsAcceptPool.cases; auto)
      apply (drule spec[of _ pi]; auto)
      apply (erule staticFlowsAcceptTm.cases; auto)
      apply (drule_tac x = "fp" in spec)
      apply (drule_tac x = "xp" in spec)
      apply (drule spec[of _ e'])
      apply (drule staticEval_to_pool)
      apply (rotate_tac -1)
      apply (drule staticEvalPreserved[of V C _ "{}" Em Hm]; auto)
      apply (simp add: star_left_implies_star)+
        apply (erule notE)
        apply (rotate_tac -1)
        apply (erule staticEvalPool.cases; auto)
        apply (drule spec[of _ pi]; auto)
        apply (erule staticEvalState.cases; auto)
        apply (erule staticEvalEnv.cases; auto)
        apply (drule_tac x = "fa" in spec; auto)
      apply (simp add: staticFlowsAcceptStack.Nonempty)

  apply (erule staticFlowsAcceptPool.cases; auto)+

done

lemma staticFlowsAcceptPoolPreservedMkChan:
"
staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
(V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
staticFlowsAcceptPool V F e0 [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
leaf Em pi \<Longrightarrow>
Em pi = Some (Stt (Bind x MkChn e) env k) \<Longrightarrow>
staticFlowsAcceptPool V F e0 (Em(pi @ [LNxt x] \<mapsto> Stt e (env(x \<mapsto> VChn (Ch pi x))) k))
"
apply (rule staticFlowsAcceptPool.Intro; auto)
 
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (rule StaticFlowsAcceptEnv; auto)
  apply (simp add: staticFlowsAcceptEnv_staticFlowsAcceptVal.Chan)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)+
done
  
lemma staticFlowsAcceptPoolPreservedSpawn:
"
  staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticFlowsAcceptPool V F e0 [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Bind x (Spwn ec) e) env k) \<Longrightarrow>
  staticFlowsAcceptPool V F e0 (Em(pi @ [LNxt x] \<mapsto> Stt e (env(x \<mapsto> VUnt)) k, pi @ [LSpwn x] \<mapsto> Stt ec env []))
"
apply (rule staticFlowsAcceptPool.Intro; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (rule StaticFlowsAcceptEnv; auto)
  using staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit apply blast
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)

  apply (erule notE)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)

  using staticFlowsAcceptStack.Empty apply blast

  apply (erule staticFlowsAcceptPool.cases; auto)+
done

lemma staticFlowsAcceptPoolPreservedSync:
"
  staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticFlowsAcceptPool V F e0 [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  leaf Em pis \<Longrightarrow>
  Em pis = Some (Stt (Bind xs (Sync xse) es) envs ks) \<Longrightarrow>
  envs xse = Some (VClsr (SendEvt xsc xm) envse) \<Longrightarrow>
  leaf Em pir \<Longrightarrow>
  Em pir = Some (Stt (Bind xr (Sync xre) er) envr kr) \<Longrightarrow>
  envr xre = Some (VClsr (RecvEvt xrc) envre) \<Longrightarrow>
  envse xsc = Some (VChn c) \<Longrightarrow>
  envre xrc = Some (VChn c) \<Longrightarrow>
  envse xm = Some vm \<Longrightarrow>
  staticFlowsAcceptPool V F e0 (Em(pis @ [LNxt xs] \<mapsto> Stt es (envs(xs \<mapsto> VUnt)) ks, pir @ [LNxt xr] \<mapsto> Stt er (envr(xr \<mapsto> vm)) kr))
"
apply (rule staticFlowsAcceptPool.Intro; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (rule StaticFlowsAcceptEnv; auto)
  using staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit apply blast
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (rule StaticFlowsAcceptEnv; auto)
  using staticFlowsAcceptEnv_staticFlowsAcceptVal.Unit apply blast
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)

  apply (erule notE)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (erule notE)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (erule staticFlowsAcceptTm.cases; auto)

  apply (rule StaticFlowsAcceptEnv; auto)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)
  apply (drule spec[of _ xse]; auto)
  apply (erule staticFlowsAcceptVal.cases; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pir]; auto)

  apply (rule StaticFlowsAcceptEnv; auto)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)
  apply (drule spec[of _ xse]; auto)
  apply (erule staticFlowsAcceptVal.cases; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (erule staticFlowsAcceptEnv.cases; auto)

  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  
  apply (erule staticFlowsAcceptPool.cases; auto)+
done

lemma staticFlowsAcceptPoolPreservedDynamicEval:
"
  staticFlowsAcceptPool V F e0 Em \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (Em, Hm) \<Longrightarrow>
  dynamicEval (Em, Hm) (E', H') \<Longrightarrow>
  staticFlowsAcceptPool V F e0 [[] \<mapsto> (Stt e0 empty [])] \<Longrightarrow> 
  staticFlowsAcceptPool V F e0 E'
"
apply (erule dynamicEval.cases; auto)
  apply (simp add: staticFlowsAcceptPoolPreservedReturn)
  apply (simp add: staticFlowsAcceptPoolPreservedSeqEval)
  apply (simp add: staticFlowsAcceptPoolPreservedCallEval)
  apply (simp add: staticFlowsAcceptPoolPreservedMkChan)
  apply (simp add: staticFlowsAcceptPoolPreservedSpawn)
  apply (simp add: staticFlowsAcceptPoolPreservedSync)
done


lemma staticFlowsAcceptPoolPreserved':
"
  star_left dynamicEval EH0 EH' \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  \<forall> E' H' .
  EH0 = ([[] \<mapsto> (Stt e0 empty [])], {}) \<longrightarrow> 
  EH' = (E', H') \<longrightarrow>
  staticFlowsAcceptPool V F e0 [[] \<mapsto> (Stt e0 empty [])] \<longrightarrow>
  staticFlowsAcceptPool V F e0 E'
"
apply (erule star_left.induct; clarify)
using staticFlowsAcceptPoolPreservedDynamicEval apply metis
done

lemma staticFlowsAcceptPoolPreserved:
"
  staticFlowsAcceptPool V F e0 [[] \<mapsto> (Stt e0 empty [])] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (E', H') \<Longrightarrow>
  staticFlowsAcceptPool V F e0 E'
"
using star_implies_star_left staticFlowsAcceptPoolPreserved' by fastforce


lemma staticFlowsAcceptToPool:
  "
  staticFlowsAccept V F e \<Longrightarrow>
  staticFlowsAcceptPool V F e [[] \<mapsto> (Stt e empty [])]
"
apply (rule staticFlowsAcceptPool.intros; auto)
  using staticFlowsAccept.cases apply blast
  apply (simp add: staticFlowsAcceptEnv_staticFlowsAcceptVal.intros(1))
  apply (simp add: staticFlowsAcceptStack.Empty)
done

lemma staticLiveChanPoolPreservedReturn: 
"
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Rslt x) env (Ctn xk ek envk # k)) \<Longrightarrow>
  env x = Some v \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC (Em(pi @ [LRtn x] \<mapsto> Stt ek (envk(xk \<mapsto> v)) k))
"
  apply (rule staticLiveChanPool.intros; clarify)
  apply (case_tac "\<pi> = pi @ [LRtn x]"; auto)

    apply (rotate_tac 1)
    apply (erule staticLiveChanPool.cases; auto)
    apply (drule spec[of _ pi]; auto)
    apply (erule staticLiveChanStack.cases; auto)

    apply (rotate_tac 1)
    apply (erule staticLiveChanPool.cases; auto)
    apply (drule spec[of _ pi]; auto)
    apply (erule staticLiveChanStack.cases; auto)
    apply (erule staticLiveChanEnv.cases; auto)
    apply (drule spec[of _ x])
    apply (drule spec[of _ v]; clarsimp)
    apply (erule staticLiveChanEnv.cases; auto)
    apply (rule StaticLiveChanEnv; auto)  

    apply (rotate_tac 1)
    apply (erule staticLiveChanPool.cases; auto)
    apply (drule spec[of _ pi]; auto)
    apply (erule staticLiveChanStack.cases; auto)

    apply (rotate_tac 1)
    apply (erule staticLiveChanPool.cases; auto)

    apply (rotate_tac 1)
    apply (erule staticLiveChanPool.cases; auto)

    apply (rotate_tac 1)
    apply (erule staticLiveChanPool.cases; auto)
done

lemma staticLiveChanPoolPreservedSeqEval:
"
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Bind x b e) env k) \<Longrightarrow>
  seqEval b env v \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC (Em(pi @ [LNxt x] \<mapsto> Stt e (env(x \<mapsto> v)) k))
"
apply (rule staticLiveChanPool.intros; clarify)
apply (case_tac "\<pi> = pi @ [LNxt x]"; auto)
  apply (rotate_tac 1; erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 1; erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule seqEval.cases; auto)
    apply (simp add: StaticLiveChanUnit staticLiveChanEnv.simps)
    apply (erule staticLiveChan.cases; clarsimp)
      apply (simp add: StaticLiveChanSendEvt staticLiveChanEnv.simps)
      apply (simp add: StaticLiveChanRecvEvt staticLiveChanEnv.simps)
      apply (simp add: StaticLiveChanPair staticLiveChanEnv.simps)
      apply (simp add: StaticLiveChanLeft staticLiveChanEnv.simps)
      apply (simp add: StaticLiveChanRight staticLiveChanEnv.simps)
      apply (simp add: StaticLiveChanFun staticLiveChanEnv.simps)
    
    apply (frule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "xp" in spec; auto)
    apply (erule staticLiveChanVal.cases; auto)
    apply (rename_tac xp envp x1 x2)
    apply (rotate_tac -1)
    apply (erule staticLiveChanEnv.cases; auto)
    apply (simp add: staticLiveChanEnv.simps)

    apply (frule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "xp" in spec; auto)
    apply (erule staticLiveChanVal.cases; auto)
    apply (rename_tac xp envp x1 x2)
    apply (rotate_tac -1)
    apply (erule staticLiveChanEnv.cases; auto)
    apply (simp add: staticLiveChanEnv.simps)
  
  apply (rotate_tac -4)
  apply (erule staticLiveChanPool.cases; auto)
  
  apply (rotate_tac -4)
  apply (erule staticLiveChanPool.cases; auto)

(*
  apply (rotate_tac -4)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

done
*)
sorry

lemma staticLiveChanPoolPreservedCall:
"       
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Bind x b e) env k) \<Longrightarrow>
  callEval (b, env) (e', env') \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC (Em(pi @ [LCall x] \<mapsto> Stt e' env' (Ctn x e env # k)))
"
apply (rotate_tac 3)
apply (frule staticLiveChanPool.cases; auto)
apply (drule spec[of _ pi]; auto)
apply (erule callEval.cases; auto; rule staticLiveChanPool.intros; clarify; (case_tac "\<pi> = pi @ [LCall x]"; auto))

    apply (erule staticLiveChan.cases; auto)
   
    apply (frule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "xs" in spec; auto)
    apply (erule staticLiveChanVal.cases; auto)
    apply (rename_tac xs vl xl xr er envl xl')
    apply (rotate_tac -1)
    apply (erule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "xl'" in spec; auto)
    apply (simp add: staticLiveChanEnv.simps)


    apply (erule staticLiveChan.cases; auto)
(*
    apply (simp add: staticLiveChanStack.Nonempty)
    apply (simp add: staticLiveChanStack.Nonempty)

  apply (frule staticLiveChanPool.cases; auto)
  apply (frule staticLiveChanPool.cases; auto)
  apply (frule staticLiveChanPool.cases; auto)

   apply (erule staticLiveChan.cases; auto)
 
    apply (frule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "xs" in spec; auto)
    apply (erule staticLiveChanVal.cases; auto)
    apply (rename_tac xs vl xl xr er envr xr')
    apply (rotate_tac -1)
    apply (erule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "xr'" in spec; auto)
    apply (simp add: staticLiveChanEnv.simps)
  
    
    apply (erule staticLiveChan.cases; auto)
      apply (simp add: staticLiveChanStack.Nonempty)
      apply (simp add: staticLiveChanStack.Nonempty)
  
    apply (frule staticLiveChanPool.cases; auto)
    apply (frule staticLiveChanPool.cases; auto)
    apply (frule staticLiveChanPool.cases; auto)

    apply (erule staticLiveChanEnv.cases; auto)
    apply (drule_tac x = "f" in spec; auto)
    apply (erule staticLiveChanVal.cases; auto)

    
    apply (rule StaticLiveChanEnv; auto)
      apply (erule staticLiveChanEnv.cases; auto)
      apply (erule staticLiveChanEnv.cases; auto)
      apply (erule staticLiveChanEnv.cases; auto)
      apply (erule staticLiveChanEnv.cases; auto)
      apply (drule_tac x = "f" in spec; auto)
      apply (erule staticLiveChanVal.cases; auto)
      apply (simp add: staticLiveChanEnv.simps)

    
    apply (erule staticLiveChan.cases; auto; simp add: staticLiveChanStack.Nonempty)
    apply (erule staticLiveChanPool.cases; auto)+
done
*)
sorry

lemma staticLiveChanPreservedMkChan:
"
staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
(V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
leaf Em pi \<Longrightarrow>
Em pi = Some (Stt (Bind x MkChn e) env k) \<Longrightarrow>
staticLiveChanPool V Ln Lx xC (Em(pi @ [LNxt x] \<mapsto> Stt e (env(x \<mapsto> VChn (Ch pi x))) k))
"
apply (rule staticLiveChanPool.Intro; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (simp add: StaticLiveChan staticLiveChanEnv.simps)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

(*
  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

done
*)
sorry

lemma staticLiveChanPoolPreservedSpawn:
"
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Bind x (Spwn ec) e) env k) \<Longrightarrow> 
  staticLiveChanPool V Ln Lx xC (Em(pi @ [LNxt x] \<mapsto> Stt e (env(x \<mapsto> VUnt)) k, pi @ [LSpwn x] \<mapsto> Stt ec env []))
"
apply (rule staticLiveChanPool.Intro; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (simp add: StaticLiveChanUnit staticLiveChanEnv.simps)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (simp add: StaticLiveChanUnit staticLiveChanEnv.simps)

(*
  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (simp add: staticLiveChanStack.Empty)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

done
*)
sorry

(* this might make a nice proof demonstration *)
lemma staticLiveChanPoolPreservedSync:
"
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
  leaf Em pis \<Longrightarrow>
  Em pis = Some (Stt (Bind xs (Sync xse) es) envs ks) \<Longrightarrow>
  envs xse = Some (VClsr (SendEvt xsc xm) envse) \<Longrightarrow>
  leaf Em pir \<Longrightarrow>
  Em pir = Some (Stt (Bind xr (Sync xre) er) envr kr) \<Longrightarrow>
  envr xre = Some (VClsr (RecvEvt xrc) envre) \<Longrightarrow>
  envse xsc = Some (VChn c) \<Longrightarrow>
  envre xrc = Some (VChn c) \<Longrightarrow>
  envse xm = Some vm \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC (Em(pis @ [LNxt xs] \<mapsto> Stt es (envs(xs \<mapsto> VUnt)) ks, pir @ [LNxt xr] \<mapsto> Stt er (envr(xr \<mapsto> vm)) kr))
"
apply (rule staticLiveChanPool.Intro; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticLiveChan.cases; auto)
  
  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (simp add: StaticLiveChanUnit staticLiveChanEnv.simps)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

(*
  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (simp add: StaticLiveChanUnit staticLiveChanEnv.simps)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (erule staticLiveChan.cases; auto)

  apply (rotate_tac 3)
  apply (frule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (rotate_tac -2)
  apply (erule staticLiveChanEnv.cases; auto)
  apply (drule spec[of _ xse]; auto)
  apply (rotate_tac -1)
  apply (erule staticLiveChanVal.cases; auto)
  apply (rotate_tac -1)
  apply (erule staticLiveChanEnv.cases; auto)
  apply (drule spec[of _ xm]; auto)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (simp add: staticLiveChanEnv.simps)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)


  apply (rotate_tac 3)
  apply (frule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pis]; auto)
  apply (rotate_tac -2)
  apply (erule staticLiveChanEnv.cases; auto)
  apply (drule spec[of _ xse]; auto)
  apply (rotate_tac -1)
  apply (erule staticLiveChanVal.cases; auto)
  apply (rotate_tac -1)
  apply (erule staticLiveChanEnv.cases; auto)
  apply (drule spec[of _ xm]; auto)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pir]; auto)
  apply (simp add: staticLiveChanEnv.simps)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

  apply (rotate_tac 3)
  apply (erule staticLiveChanPool.cases; auto)

done
*)
sorry

lemma staticLiveChanPoolPreservedDynamicEval: 
"
staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e0 Map.empty []] \<Longrightarrow>
(V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e0 Map.empty []], {}) (Em, Hm) \<Longrightarrow>
staticLiveChanPool V Ln Lx xC Em \<Longrightarrow>
dynamicEval (Em, Hm) (E, H)  \<Longrightarrow> 
staticLiveChanPool V Ln Lx xC E
"
apply (erule dynamicEval.cases; auto)
  apply (simp add: staticLiveChanPoolPreservedReturn)
  apply (simp add: staticLiveChanPoolPreservedSeqEval)
  apply (simp add: staticLiveChanPoolPreservedCall)
  apply (simp add: staticLiveChanPreservedMkChan)
  apply (simp add: staticLiveChanPoolPreservedSpawn)
  apply (simp add: staticLiveChanPoolPreservedSync)
done


lemma staticLiveChanPoolPreserved':
"
  star_left dynamicEval EH0 EH \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e0 empty [])] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  \<forall> E H .
    EH0 = ([[] \<mapsto> (Stt e0 empty [])], {}) \<longrightarrow>
    EH = (E, H) \<longrightarrow>
    staticLiveChanPool V Ln Lx xC E
"
apply (erule star_left.induct; blast?)
apply (metis surj_pair staticLiveChanPoolPreservedDynamicEval)
done

lemma staticLiveChanPoolPreserved:
  "
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e0 empty [])] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (\<E>', H') \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC \<E>'
"
using star_implies_star_left staticLiveChanPoolPreserved' by fastforce


lemma staticLiveChanToPool:
  "
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e empty [])]
"
apply (rule staticLiveChanPool.intros; auto)
apply (simp add: staticLiveChanEnv.simps)
apply (simp add: staticLiveChanStack.Empty)
done




lemma staticBuiltOnChanSound:
"
  dynamicBuiltOnChanVal v (Ch \<pi>C xC) \<Longrightarrow>
  \<rho> n = Some v \<Longrightarrow>
  pool pi = Some (Stt e' \<rho>' \<kappa>') \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> pool \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC pool \<Longrightarrow>
  staticFlowsAcceptPool V F e0 pool \<Longrightarrow>
  staticBuiltOnChan V xC n
"
sorry


lemma staticPathLivePoolSoundReturn: 
"
(V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
staticFlowsAcceptPool V F e [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e Map.empty []], {}) (Em, Hm) \<Longrightarrow>

\<forall>\<pi>' e' env' stack' isEnd.
  ([[] \<mapsto> Stt e Map.empty []], {}) = ([[] \<mapsto> Stt e Map.empty []], {}) \<longrightarrow>
  Em \<pi>' = Some (Stt e' env' stack') \<longrightarrow>
  dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<longrightarrow>
  isEnd (tmId e') \<longrightarrow> (\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path) \<Longrightarrow>
(Em(pi @ [LRtn x] \<mapsto> Stt ek (envk(xk \<mapsto> v)) k)) \<pi>' = Some (Stt e' env' stack') \<Longrightarrow>
dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<Longrightarrow>
isEnd (tmId e') \<Longrightarrow>
 leaf Em pi \<Longrightarrow> 
Em pi = Some (Stt (Rslt x) env (Ctn xk ek envk # k)) \<Longrightarrow>
env x = Some v \<Longrightarrow>
\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path
"

apply (case_tac "\<pi>' = pi @ [LRtn x]"; auto)
  apply (drule spec[of _ pi]; clarify?)
  apply (drule spec[of _ "Rslt x"]; clarify?)
  apply (drule spec[of _ "env"]; clarify?)
  apply (drule spec[of _ "(Ctn xk ek envk # k)"]; clarify?)
  apply (erule impE)

  apply (erule dynamicBuiltOnChanState.cases; auto)
  apply (erule dynamicBuiltOnChanEnv.cases; auto)
  
  apply (case_tac "n = xk"; auto)
  apply (rule dynamicBuiltOnChanState.Env)
  apply (rule dynamicBuiltOnChanEnv_intro; auto)
  apply (rule dynamicBuiltOnChanState.Stack)
  apply (rule dynamicBuiltOnChanStack.Env)
  apply (rule dynamicBuiltOnChanEnv_intro; auto)
  apply (rule dynamicBuiltOnChanState.Stack)
  apply (erule dynamicBuiltOnChanStack.Stack)
  apply (drule_tac x = "\<lambda> id . id = IdRslt x" in spec; auto)

  apply (rule_tac x = "path @ [(IdRslt x, EReturn)]" in exI; auto)
  apply (rule pathsCongruentModChanPreservedSnoc; auto?)
  using pathsCongruent.Empty pathsCongruent.Return apply fastforce

  apply (rule staticPathLive.Edge; auto?)
  apply (drule staticFlowsAcceptPoolPreserved[of V F e C Em Hm]; auto?)
  apply (erule staticEvalPool.cases; auto?)
  apply (drule spec[of  _ "[]"]; auto)
  apply (erule staticEvalState.cases; auto)
  apply (simp add: star_left_implies_star)
  apply (erule staticFlowsAcceptPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticFlowsAcceptStack.cases; auto)

  apply (drule staticLiveChanPoolPreserved[of V Ln Lx xC e C Em Hm]; auto?)
  apply (erule staticEvalPool.cases; auto?)
  apply (drule spec[of  _ "[]"]; auto)
  apply (erule staticEvalState.cases; auto)
  apply (simp add: star_left_implies_star)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticLiveChanStack.cases; auto)

  apply (drule staticLiveChanPoolPreserved[of V Ln Lx xC e C Em Hm]; auto?)
  apply (erule staticEvalPool.cases; auto?)
  apply (drule spec[of  _ "[]"]; auto)
  apply (erule staticEvalState.cases; auto)
  apply (simp add: star_left_implies_star)
  apply (erule staticLiveChanPool.cases; auto)
  apply (drule spec[of _ pi]; auto)
  apply (erule staticLiveChanStack.cases; auto)   
done


lemma staticPathsLivePoolSoundUnitEval:
"
  (V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
  staticFlowsAcceptPool V F e [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
  star_left op \<rightarrow> ([[] \<mapsto> Stt e Map.empty []], {}) (Em, Hm) \<Longrightarrow>
  dynamicBuiltOnChanState (Stt e' (env(x \<mapsto> VUnt)) stack') (Ch \<pi>C xC) \<Longrightarrow>
  isEnd (tmId e') \<Longrightarrow>
  leaf Em pi \<Longrightarrow>
  Em pi = Some (Stt (Bind x Unt e') env stack') \<Longrightarrow>
  dynamicBuiltOnChanState (Stt (Bind x Unt e') env stack') (Ch \<pi>C xC) \<longrightarrow>
  (\<forall>isEnd. isEnd (tmId (Bind x Unt e')) \<longrightarrow>
           (\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) pi path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path)) \<Longrightarrow>
  \<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) (pi @ [LNxt x]) path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path
"
 apply (erule impE)
  apply (erule dynamicBuiltOnChanState.cases; auto)
   apply (erule dynamicBuiltOnChanEnv.cases; auto)
   apply (case_tac "n = x"; auto)
    apply (erule dynamicBuiltOnChanVal.cases; blast)
   apply (rule dynamicBuiltOnChanState.Env)
   apply (rule dynamicBuiltOnChanEnv_intro[of env]; auto)
  apply (rule dynamicBuiltOnChanState.Stack; auto)
 apply (drule spec[of _ "\<lambda> id . id = IdBind x"]; auto)
 apply (rule_tac x = "path @ [(IdBind x, ENext)]" in exI; auto)
  using Next pathsCongruent.Empty pathsCongruentModChanPreservedSnoc apply fastforce

 apply (drule staticFlowsAcceptPoolPreserved[of V F e C Em Hm])
   apply (erule staticEvalPool.cases; auto?)
   apply (drule spec[of  _ "[]"]; auto)
   apply (erule staticEvalState.cases; auto)
  apply (simp add: star_left_implies_star)

 apply (drule staticLiveChanPoolPreserved[of V Ln Lx xC e C Em Hm])
   apply (erule staticEvalPool.cases; auto?)
   apply (drule spec[of  _ "[]"]; auto)
   apply (erule staticEvalState.cases; auto)
  apply (simp add: star_left_implies_star)

 apply (rule staticPathLive.Edge; simp?)
   apply (erule staticFlowsAcceptPool.cases; auto)
   apply (drule spec[of _ pi]; auto)
   apply (erule staticFlowsAcceptTm.cases; auto)
(***)
  apply (erule staticLiveChanPool.cases; clarsimp)
  apply (drule spec[of _ pi]; auto)

sorry

lemma staticPathLivePoolSoundSeqEval: 
"
(V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
staticFlowsAcceptPool V F e [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e Map.empty []], {}) (Em, Hm) \<Longrightarrow>
\<forall>\<pi>' e' env' stack' isEnd.
  ([[] \<mapsto> Stt e Map.empty []], {}) = ([[] \<mapsto> Stt e Map.empty []], {}) \<longrightarrow>
  Em \<pi>' = Some (Stt e' env' stack') \<longrightarrow>
  dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<longrightarrow>
  isEnd (tmId e') \<longrightarrow> (\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path) \<Longrightarrow>
(Em(pi @ [LNxt x] \<mapsto> Stt ea (env(x \<mapsto> v)) k)) \<pi>' = Some (Stt e' env' stack') \<Longrightarrow>
dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<Longrightarrow>
isEnd (tmId e') \<Longrightarrow>
leaf Em pi \<Longrightarrow>
Em pi = Some (Stt (Bind x b ea) env k) \<Longrightarrow>
seqEval b env v \<Longrightarrow>
\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path
"
 apply (case_tac "\<pi>' = pi @ [LNxt x]"; auto)
 apply (drule spec[of _ pi]; clarify?)
 apply (drule spec[of _ "Bind x b e'"]; clarify?)
 apply (drule spec[of _ env]; clarify?)
 apply (drule spec[of _ stack']; clarify?)
 apply (erule seqEval.cases; clarify)
    apply (insert staticPathsLivePoolSoundUnitEval; auto)
sorry

lemma staticPathLivePoolSoundDynamicEval:
"
(V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
staticLiveChanPool V Ln Lx xC [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
staticFlowsAcceptPool V F e [[] \<mapsto> Stt e Map.empty []] \<Longrightarrow>
star_left op \<rightarrow> ([[] \<mapsto> Stt e Map.empty []], {}) (Em, Hm) \<Longrightarrow>
\<forall>\<pi>' e' env' stack' isEnd.
  ([[] \<mapsto> Stt e Map.empty []], {}) = ([[] \<mapsto> Stt e Map.empty []], {}) \<longrightarrow>
  Em \<pi>' = Some (Stt e' env' stack') \<longrightarrow>
  dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<longrightarrow>
  isEnd (tmId e') \<longrightarrow> 
  (\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path) \<Longrightarrow>
dynamicEval (Em, Hm) (E', H') \<Longrightarrow>
E' \<pi>' = Some (Stt e' env' stack') \<Longrightarrow>
dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<Longrightarrow>
isEnd (tmId e') \<Longrightarrow> 
\<exists>path. pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and> staticPathLive F Ln Lx (IdBind xC) isEnd path
"
apply (erule dynamicEval.cases; clarify?)
apply (insert staticPathLivePoolSoundReturn; auto)
apply (insert staticPathLivePoolSoundSeqEval; auto)
sorry

lemma staticPathLivePoolSound':
"
star_left dynamicEval EH EH' \<Longrightarrow>
(V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
staticFlowsAcceptPool V F e [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
\<forall> E' H' \<pi>' e' env' stack' isEnd .
  EH = ([[] \<mapsto> (Stt e empty [])], {}) \<longrightarrow> EH' = (E', H') \<longrightarrow>
  E' \<pi>' = Some (Stt e' env' stack') \<longrightarrow>
  dynamicBuiltOnChanState (Stt e' env' stack') (Ch \<pi>C xC) \<longrightarrow>
  isEnd (tmId e') \<longrightarrow>
  (\<exists> path .
    pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and>
    staticPathLive F Ln Lx (IdBind xC) isEnd path)
"

apply (erule star_left.induct; clarify)
  apply (erule dynamicBuiltOnChanState.cases; auto)
  apply (case_tac "\<pi>' = []"; auto)
  apply (erule dynamicBuiltOnChanEnv.cases; auto)
    apply (case_tac "\<pi>' = []"; auto)
  apply (erule dynamicBuiltOnChanStack.cases; auto)
  apply (insert staticPathLivePoolSoundDynamicEval; auto?)
done

lemma staticPathLivePoolSound:
"
  \<E>' \<pi>' = Some (Stt e' \<rho>' \<kappa>') \<Longrightarrow>
  dynamicBuiltOnChanState (Stt e' \<rho>' \<kappa>') (Ch \<pi>C xC) \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>\<E> [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
  staticFlowsAcceptPool V F e [[] \<mapsto> (Stt e empty [])] \<Longrightarrow>
  isEnd (tmId e') \<Longrightarrow>
  (\<exists> path . 
      pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and>
      staticPathLive F Ln Lx (IdBind xC) isEnd path)
"
apply (drule star_implies_star_left)
apply (insert staticPathLivePoolSound')
apply auto
done


lemma staticPathLiveSound: "
  \<E>' \<pi>' = Some (Stt e' \<rho>' \<kappa>') \<Longrightarrow>
  dynamicBuiltOnChanState (Stt e' \<rho>' \<kappa>') (Ch \<pi>C xC) \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  isEnd (tmId e') \<Longrightarrow>
  \<exists> path .
    pathsCongruentModChan e (Ch \<pi>C xC) \<pi>' path \<and>
    staticPathLive F Ln Lx (IdBind xC) isEnd path
"
apply (drule staticEval_to_pool)
apply (drule staticFlowsAcceptToPool)
apply (drule staticLiveChanToPool)
apply (simp add: staticPathLivePoolSound)
done


lemma sendEvtBuiltOnChan:
"
env xe = Some (VClsr (SendEvt xsc xm) enve) \<Longrightarrow>
enve xsc = Some (VChn (Ch \<pi>C xC)) \<Longrightarrow>
dynamicBuiltOnChanEnv env (Ch \<pi>C xC)
"
by (simp add: dynamicBuiltOnChanEnv_intro dynamicBuiltOnChanVal_chan dynamicBuiltOnChanVal_closure)


lemma staticPathLiveSendSound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  \<exists> pathSync .
    (pathsCongruentModChan e (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC) pathSync
"
 apply (unfold is_send_path.simps; auto) 
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in staticSendSiteSound; auto?)
  apply (frule staticPathLiveSound; auto?)
  apply (metis dynamicBuiltOnChanState.Env sendEvtBuiltOnChan)
done

(* END PATH SOUND *)


theorem staticOneShotSound': "
  forEveryTwo (staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC)) singular \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  forEveryTwo (is_send_path \<E>' (Ch \<pi> xC)) op =
"
 apply (simp add: forEveryTwo.simps singular.simps; auto)
 apply (frule_tac \<pi>Sync = \<pi>1 in staticPathLiveSendSound; auto)
 apply (drule_tac x = pathSync in spec)
 apply (frule_tac \<pi>Sync = \<pi>2 in staticPathLiveSendSound; auto?)
 apply (drule_tac x = pathSynca in spec)
 apply (erule impE, simp)
 apply (metis is_send_path_implies_nonempty_pool staticInclusiveSound static_equalitySound)
done

theorem staticOneShotSound: "
  \<lbrakk>
    staticOneShot e xC
  \<rbrakk> \<Longrightarrow>
  one_shot e (Ch \<pi> xC)
"
 apply (erule staticOneShot.cases; auto)
 apply (unfold one_shot.simps)
  using staticOneShotSound' apply fastforce
done


(*
TO DO LATER:
*)

theorem noncompetitive_send_to_ordered_send: "
  forEveryTwo (staticPathLive F Ln Lx (IdBind xC) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  forEveryTwo (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem staticOneToManySound: "
  \<lbrakk>
    staticOneToMany e xC
  \<rbrakk> \<Longrightarrow>
  fan_out e (Ch \<pi> xC)
"
 apply (erule staticOneToMany.cases; auto)
 apply (unfold fan_out.simps)
  using noncompetitive_send_to_ordered_send apply fastforce
done

lemma noncompetitive_recv_to_ordered_recv:
  "
   forEveryTwo (staticPathLive F Ln Lx (IdBind xC) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
   staticFlowsAccept V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
   forEveryTwo (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem staticManyToOneSound: "
  \<lbrakk>
    staticManyToOne e xC
  \<rbrakk> \<Longrightarrow>
  fan_in e (Ch \<pi> xC)
"
 apply (erule staticManyToOne.cases; auto)
 apply (unfold fan_in.simps)
  using noncompetitive_recv_to_ordered_recv apply fastforce
done


theorem staticOneToOneSound: "
  \<lbrakk>
    staticOneToOne e xC
  \<rbrakk> \<Longrightarrow>
  one_to_one e (Ch \<pi> xC)
"
 apply (erule staticOneToOne.cases; auto)
  apply (unfold one_to_one.simps)
 apply (metis fan_out.cases noncompetitive_recv_to_ordered_recv staticOneToMany.intros staticOneToManySound)
done

theorem staticOneSyncSound:
  "
      staticOneSync e xC \<Longrightarrow>
      one_sync e (Ch \<pi> xC)"
apply (erule staticOneSync.cases; auto)
apply (unfold one_sync.simps; auto)
using
fan_in.simps fan_out.simps noncompetitive_recv_to_ordered_recv noncompetitive_send_to_ordered_send
apply (metis star.refl staticOneShotSound')
done

end
