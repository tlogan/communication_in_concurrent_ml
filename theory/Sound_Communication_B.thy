theory Sound_Communication_B
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics Sound_Semantics
    Dynamic_Communication Static_Communication Sound_Communication
    Static_Communication_B
begin


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


inductive staticLiveChanStack :: "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> contin list \<Rightarrow> bool" where
  Empty: "staticLiveChanStack V Ln Lx x\<^sub>c []"
| Nonempty:
  "
    \<lbrakk> 
      \<not> Set.is_empty (Ln (tmId e));
      staticLiveChan V Ln Lx x\<^sub>c e;
      staticLiveChanEnv V Ln Lx x\<^sub>c \<rho>; 
      staticLiveChanStack V Ln Lx x\<^sub>c \<kappa>
    \<rbrakk> \<Longrightarrow> 
    staticLiveChanStack V Ln Lx x\<^sub>c ((Ctn x e \<rho>) # \<kappa>)
  "


inductive staticLiveChanPool ::  "static_env \<Rightarrow> tm_id_map \<Rightarrow> tm_id_map \<Rightarrow> name \<Rightarrow> trace_pool \<Rightarrow> bool"  where
  Intro:
  "
    (\<forall> \<pi> e \<rho> \<kappa> . pool \<pi> = Some (Stt e \<rho> \<kappa>) \<longrightarrow>
      staticLiveChan V Ln Lx x\<^sub>c e \<and>
      staticLiveChanEnv V Ln Lx x\<^sub>c \<rho> \<and>
      staticLiveChanStack V Ln Lx x\<^sub>c \<kappa>) \<Longrightarrow>
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
  "trace_pool * communication \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> static_path \<Rightarrow> bool" 
where
  Empty: "pathsCongruentModChan (\<E>, H) c [] []"
| Chan:
  "
    pathsCongruent ((LNxt xC) # \<pi>Suff) path \<Longrightarrow>
    \<E> (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
    pathsCongruentModChan (\<E>, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path
  " 
| Sync:
(*  inducts on the strict prefix up to channel passing point*) 
  "
    pathsCongruent \<pi>Suffix pathSuffix \<Longrightarrow>
    \<E> (\<pi>R @ (LNxt xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
    dynamicBuiltOnChan \<rho>RY c xR \<Longrightarrow>
    \<E> \<pi>S = Some (Stt (Bind xS (Sync xSE) eSY) \<rho>SY \<kappa>SY) \<Longrightarrow>
    \<E> \<pi>R = Some (Stt (Bind xR (Sync xRE) eRY) \<rho>RY \<kappa>RY) \<Longrightarrow>
    {(\<pi>S, c_c, \<pi>R)} \<subseteq> H \<Longrightarrow> 
    pathsCongruentModChan (\<E>, H) c \<pi>S pathPre \<Longrightarrow>
    pathsCongruentModChan (\<E>, H) c (\<pi>R @ (LNxt xR) # \<pi>Suffix) (pathPre @ (IdBind xS, ESend xSE) # (IdBind xR, ENext) # pathSuffix)
  " 


lemma staticInclusiveSound: "
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>

  \<E>' \<pi>1 \<noteq> None \<Longrightarrow> 
  pathsCongruentModChan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC) path1 \<Longrightarrow>
  
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 
  pathsCongruentModChan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC) path2 \<Longrightarrow>

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
  pathsCongruentModChan (\<E>', H') (Ch \<pi> xC) \<pi>1 path1 \<Longrightarrow>
  staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC) path1 \<Longrightarrow>
  
  pathsCongruentModChan (\<E>', H') (Ch \<pi> xC) \<pi>2 path2 \<Longrightarrow>
  staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC) path2 \<Longrightarrow>
  \<E>' \<pi>2 \<noteq> None \<Longrightarrow> 

  \<pi>1 = \<pi>2
"
  sorry

(* PATH SOUND *)

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
      then show ?thesis sorry
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
      then show ?thesis sorry
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
        using H2 H4 local.App(3) staticEvalPoolSoundSnapshot sorry
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

lemma staticLiveChanPoolPreservedStep: 
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
sorry


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
apply (metis surj_pair staticLiveChanPoolPreservedStep )
done

lemma staticLiveChanPoolPreserved:
  "
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e0 empty [])] \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e0 \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e0 empty [])], {}) (\<E>', H') \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC \<E>'
"
sorry


lemma staticLiveChanToPool:
  "
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC [[] \<mapsto> (Stt e empty [])]
"
apply (rule staticLiveChanPool.intros; auto)
apply (simp add: staticLiveChanEnv.simps)
apply (simp add: staticLiveChanStack.Empty)
done


lemma staticTraceablePoolSound':
  assumes
    H1: "star_left dynamicEval EH EH'" and
    H2: "(V, C) \<Turnstile>\<^sub>e e"
  shows "
    \<forall> E' H' \<pi>' x' b' e'' \<rho>' \<kappa>' isEnd .
    EH = ([[] \<mapsto> (Stt e empty [])], {}) \<longrightarrow> EH' = (E', H') \<longrightarrow>
    E' \<pi>' = Some (Stt (Bind x' b' e'') \<rho>' \<kappa>') \<longrightarrow>
    dynamicBuiltOnChanComplex \<rho>' (Ch \<pi>C xC) b' \<longrightarrow>
    staticLiveChanPool V Ln Lx xC E' \<longrightarrow>
    staticFlowsAcceptPool V F E' \<longrightarrow>
    isEnd (IdBind x') \<longrightarrow>
    (\<exists> path .
      pathsCongruentModChan (E', H') (Ch \<pi>C xC) \<pi>' path \<and>
      staticTraceable F Ln Lx (IdBind xC) isEnd path)
"
(*
using H1
proof induction
  case (refl z)
  have L1H1: "pathsCongruentModChan ([[] \<mapsto> Stt e Map.empty []], {}) (Ch \<pi>C xC) [] []"
  using pathsCongruentModChan.Empty by simp
  
  have L1H2: "\<forall> isEnd . staticTraceable F Ln Lx (IdBind xC) isEnd []" 
  sorry
  thm staticTraceable.Empty
  (* should there be an assumption to remove cases where dynamic path has no relevant channel?*)
 
  then show ?case using pathsCongruentModChan.Empty staticTraceable.Empty sorry
next
  case (step EH EHm EH')
  then show ?case using staticTraceablePoolStepSound[of EH EHm EH']
    using H2 by blast
qed
*)
sorry

lemma staticTraceablePoolSound:
"
  \<E>' \<pi>' = Some (Stt (Bind x' b' e'') \<rho>' \<kappa>') \<Longrightarrow>
  dynamicBuiltOnChanComplex \<rho>' (Ch \<pi>C xC) b' \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticLiveChanPool V Ln Lx xC \<E>' \<Longrightarrow>
  staticFlowsAcceptPool V F \<E>' \<Longrightarrow>
  isEnd (IdBind x') \<Longrightarrow>
  (\<exists> path . 
      pathsCongruentModChan (\<E>', H') (Ch \<pi>C xC) \<pi>' path \<and>
      staticTraceable F Ln Lx (IdBind xC) isEnd path)
"
apply (drule star_implies_star_left)
apply (insert staticTraceablePoolSound'[of "([[] \<mapsto> (Stt e empty [])], {})" "(\<E>', H')" V C e \<pi>C xC Ln Lx F])
apply auto
done


lemma staticTraceableSound: "
  \<E>' \<pi> = Some (Stt (Bind x b e\<^sub>n) \<rho> \<kappa>) \<Longrightarrow>
  dynamicBuiltOnChanComplex \<rho> (Ch \<pi>C xC) b \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  isEnd (IdBind x) \<Longrightarrow>
  \<exists> path .
    pathsCongruentModChan (\<E>', H') (Ch \<pi>C xC) \<pi> path \<and>
    staticTraceable F Ln Lx (IdBind xC) isEnd path
"
apply (drule staticFlowsAcceptToPool)
apply (drule staticLiveChanToPool)
apply (drule staticTraceablePoolSound; auto?)
apply (erule staticLiveChanPoolPreserved; auto?)
apply (erule staticFlowsAcceptPoolPreserved; auto?)
done

lemma sendEvtBuiltOnChan:
"
env xe = Some (VClsr (SendEvt xsc xm) enve) \<Longrightarrow>
enve xsc = Some (VChn (Ch \<pi>C xC)) \<Longrightarrow>
dynamicBuiltOnChanComplex env (Ch \<pi>C xC) (Sync xe)
"
apply (rule DynBuiltChanSync)
apply (rule DynBuiltChanClosure; auto?)
apply (rule DynBuiltChanSendEvt; auto)
apply (rule DynBuiltChan; auto)
done


lemma staticTraceableSendSound: "
  is_send_path \<E>' (Ch \<pi>C xC) \<pi>Sync \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow> 
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  \<exists> pathSync .
    (pathsCongruentModChan (\<E>', H') (Ch \<pi>C xC) \<pi>Sync pathSync) \<and> 
    staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC) pathSync"
 apply (unfold is_send_path.simps; auto) 
 apply (frule_tac x\<^sub>s\<^sub>c = xsc and \<pi>C = \<pi>C and \<rho>\<^sub>e = enve in staticSendSiteSound; auto?)
  apply (frule staticTraceableSound; auto?)
  apply (erule sendEvtBuiltOnChan; auto)
done

(* END PATH SOUND *)


theorem staticOneShotSound': "
  forEveryTwo (staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC)) singular \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
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
 apply (metis is_send_path_implies_nonempty_pool staticInclusiveSound static_equalitySound)
done

theorem staticOneShotSound: "
  \<lbrakk>
    staticOneShot V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_shot \<E>' (Ch \<pi> xC)
"
 apply (erule staticOneShot.cases; auto)
 apply (unfold one_shot.simps)
 apply (simp add: staticOneShotSound')
done


(*
TO DO LATER:
*)

theorem noncompetitive_send_to_ordered_send: "
  forEveryTwo (staticTraceable F Ln Lx (IdBind xC) (staticSendSite V e xC)) noncompetitive \<Longrightarrow>
  staticLiveChan V Ln Lx xC e \<Longrightarrow>
  staticFlowsAccept V F e \<Longrightarrow>
  (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
  star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
  forEveryTwo (is_send_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem staticOneToManySound: "
  \<lbrakk>
    staticOneToMany V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_out \<E>' (Ch \<pi> xC)
"
 apply (erule staticOneToMany.cases; auto)
 apply (unfold fan_out.simps)
 apply (metis noncompetitive_send_to_ordered_send)
done

lemma noncompetitive_recv_to_ordered_recv:
  "
   forEveryTwo (staticTraceable F Ln Lx (IdBind xC) (staticRecvSite V e xC)) noncompetitive \<Longrightarrow>
   staticFlowsAccept V F e \<Longrightarrow>
   (V, C) \<Turnstile>\<^sub>e e \<Longrightarrow>
   star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H') \<Longrightarrow>
   forEveryTwo (is_recv_path \<E>' (Ch \<pi> xC)) ordered
"
sorry


theorem staticManyToOneSound: "
  \<lbrakk>
    staticManyToOne V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  fan_in \<E>' (Ch \<pi> xC)
"
 apply (erule staticManyToOne.cases; auto)
 apply (unfold fan_in.simps)
 apply (metis noncompetitive_recv_to_ordered_recv)
done


theorem staticOneToOneSound: "
  \<lbrakk>
    staticOneToOne V e xC;
    (V, C) \<Turnstile>\<^sub>e e;
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (\<E>', H')
  \<rbrakk> \<Longrightarrow>
  one_to_one \<E>' (Ch \<pi> xC)
"
 apply (erule staticOneToOne.cases; auto)
  apply (unfold one_to_one.simps)
  apply (metis staticManyToOne.intros staticManyToOneSound staticOneToMany.intros staticOneToManySound)
done

(*

lemma paths_congPreservedDynamicEval_under_reduction: "
  pathsCongruent (\<pi> @ [l) (path @ [n]) \<Longrightarrow>
  pathsCongruent \<pi> path"
using pathsCongruent.cases by fastforce


lemma paths_cong_mod_chanPreservedDynamicEval_under_reduction: "
(suffix \<pi> (\<pi>C @ [LNxt xC)) \<and> suffix path [(IdBind xC, ENext)] \<or>
  True) \<Longrightarrow>
pathsCongruentModChan EH' (Ch \<pi>C xC) (\<pi> @ [l) (path @ [n]) \<Longrightarrow>
^env \<pi> \<noteq> None \<Longrightarrow>
pathsCongruentModChan (env, H) (Ch \<pi>C xC) \<pi> path"
proof -
  assume
    H1: "env \<pi> \<noteq> None" and
    H2: "\<pi> \<noteq> []" "path \<noteq> []" and
    H3: "pathsCongruentModChan EH' c (\<pi> @ [l) (path @ [n])"

  from H3
  show "pathsCongruentModChan (env, H) c \<pi> path"
  proof cases

    case (Chan xC \<pi>X E' \<pi>C H')

    have 
      H4: "\<pi> @ [l = \<pi>C @ (butlast (LNxt xC # \<pi>X)) @ [l"
      by (metis butlast_append butlast_snoc list.simps(3) local.Chan(3))
    
    have 
      H5: "pathsCongruent ((butlast (LNxt xC # \<pi>X)) @ [l) (path @ [n])"
      by (metis append_butlast_last_id last_ConsL last_appendR list.simps(3) local.Chan(3) local.Chan(4))

    have 
      H6: "butlast (LNxt xC # \<pi>X) \<noteq> []"
      by (metis H2(2) H5 pathsCongruent.cases snoc_eq_iff_butlast)

    have 
      H7: "pathsCongruent (butlast (LNxt xC # \<pi>X)) path"
      using H2(2) H5 H6 paths_congPreservedDynamicEval_under_reduction by blast

    have 
      H8: "pathsCongruent (LNxt xC # (butlast \<pi>X)) path"
      by (metis H6 H7 butlast.simps(2))

    have L2H10: "\<pi> = \<pi>C @ butlast (LNxt xC # \<pi>X)"
    using H4 by blast

    have "pathsCongruentModChan (env, H) (Ch \<pi>C xC) \<pi> path"
    using H1 H6 H8 L2H10 pathsCongruentModChan.Chan by auto
     
    then show "pathsCongruentModChan (env, H) c \<pi> path"
    by (simp add: local.Chan(2))

  next
    case (Sync \<pi>Suffix pathSuffix E' \<pi>R xR \<rho>RY \<pi>S xS xSE eSY \<rho>SY \<kappa>SY xRE eRY \<kappa>RY H' pathPre)

    
    then show "pathsCongruentModChan (env, H) c \<pi> path"
    proof cases
      assume L1H1: "pathSuffix = []"

      have L1H2: "path = pathPre @ [(IdBind xS, ESend xSE)]"
        using L1H1 local.Sync(3) by auto

      have L1H3: "\<pi>Suffix = []"
        using L1H1 local.Sync(4) pathsCongruent.cases by blast

      have L1H3: "\<pi> = \<pi>R"
        using L1H3 local.Sync(2) by blast

      have "pathsCongruentModChan (env, H) c \<pi>R (pathPre @ [(IdBind xS, ESend xSE)])" sorry

      then show ?thesis sorry
    next
      assume L1H1: "pathSuffix \<noteq> []"

      have 
        L1H2: "path = pathPre @ (IdBind xS, ESend xSE) # (IdBind xR, ENext) # (butlast pathSuffix)"
        by (metis L1H1 butlast.simps(2) butlast_append butlast_snoc list.simps(3) local.Sync(3))
      
      have L1H3: "\<pi>Suffix \<noteq> []"
        using local.Sync(4) pathsCongruent.cases sorry

      have L1H4: "\<pi> = \<pi>R @ LNxt xR # (butlast \<pi>Suffix)"
        by (metis L1H3 butlast.simps(2) butlast_append butlast_snoc list.distinct(1) local.Sync(2))

      show ?thesis
      proof cases
        assume 
          L2H1: "(butlast pathSuffix) = []"

        have 
          L2H2: "path = pathPre @ [(IdBind xS, ESend xSE), (IdBind xR, ENext)]"
          by (simp add: L1H2 L2H1)

        have 
          L2H3: "(butlast \<pi>Suffix) = []" sorry

        have L2H4: "\<pi> = \<pi>R @ [LNxt xR]" by (simp add: L1H4 L2H3)

        have 
          "pathsCongruentModChan (env, H) c (\<pi>R @ [LNxt xR]) (pathPre @ [(IdBind xS, ESend xSE), (IdBind xR, ENext)])" sorry

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
lemma paths_cong_mod_chanPreservedDynamicEval_under_reduction_chan: "
  pathsCongruent ((LNxt xC) # \<pi>Suff @ [l) (path @ [n]) \<Longrightarrow>
  env (\<pi>C @ (LNxt xC) # \<pi>Suff) \<noteq> None \<Longrightarrow>
  pathsCongruentModChan (env, H) (Ch \<pi>C xC) (\<pi>C @ (LNxt xC) # \<pi>Suff) path"
using paths_congPreservedDynamicEval_under_reduction pathsCongruentModChan.Chan by blast

lemma  paths_cong_mod_chanPreservedDynamicEval_under_reduction_sync: "
  pathsCongruent (\<pi>Suffix @ [l) (pathSuffix @ [n]) \<Longrightarrow>
  \<E> (\<pi>R @ (LNxt xR) # \<pi>Suffix) \<noteq> None \<Longrightarrow>
  dynamicBuiltOnChan \<rho>RY c xR \<Longrightarrow>
  \<E> \<pi>S = Some (Stt (Bind xS (Sync xSE) eSY) \<rho>SY \<kappa>SY)) \<Longrightarrow>
  \<E> \<pi>R = Some (Stt (Bind xR (Sync xRE) eRY) \<rho>RY \<kappa>RY)) \<Longrightarrow>
  {(\<pi>S, c, \<pi>R)} \<subseteq> H \<Longrightarrow>
  pathsCongruentModChan (\<E>, H) c \<pi>SforEveryTwo pathPre \<Longrightarrow>
  pathsCongruentModChan (\<E>, H) c (\<pi>R @ (LNxt xR) # \<pi>Suffix) (pathPre @ (IdBind xS, ESend xSE) # (IdBind xR, ENext) # pathSuffix)"
by (meson paths_congPreservedDynamicEval_under_reduction pathsCongruentModChan.Sync)
*)





end
