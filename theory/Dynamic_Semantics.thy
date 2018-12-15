theory Dynamic_Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" Stars
begin

datatype control_tm_id =
  LNxt name
| LSpwn name
| LCall name
| LRtn name

type_synonym control_path = "control_tm_id list"

datatype chan = Ch control_path name

datatype val =
  VUnt
| VChn chan
| VClsr atom "name \<Rightarrow> val option"

type_synonym env = "name \<Rightarrow> val option"


inductive seqEval :: "complex \<Rightarrow> env \<Rightarrow> val \<Rightarrow> bool" where
  UNIT:
  "
    seqEval Unt env VUnt
  "
| PRIM:
  "
    seqEval (Atom p) env (VClsr p env)
  "
| FST:
  "
    env xp = Some (VClsr (Pair x1 x2) envp) \<Longrightarrow>
    envp x1 = Some v \<Longrightarrow>
    seqEval (Fst xp) env v
  "
| SND:
  "
    env xp = Some (VClsr (Pair x1 x2) envp) \<Longrightarrow>
    envp x2 = Some v \<Longrightarrow>
    seqEval (Snd xp) env v"


inductive callEval :: "complex * env \<Rightarrow> tm * env \<Rightarrow> bool" where
  CaseLft:
  "
    \<lbrakk>
      env xs = Some (VClsr (Lft xl') envl);
      envl xl' = Some vl
    \<rbrakk> \<Longrightarrow>
    callEval (Case xs xl el xr er, env) (el, env(xl \<mapsto> vl))
  "
| CaseRht:
  "
    \<lbrakk>
      env xs = Some (VClsr (Rht xr') envr);
      envr xr' = Some vr
    \<rbrakk> \<Longrightarrow>
    callEval (Case xs xl el xr er, env) (er, env(xr \<mapsto> vr))
  "
| App:
  "
    \<lbrakk>
      env f = Some (VClsr (Fun fp xp el) envl);
      env xa = Some va
    \<rbrakk> \<Longrightarrow>
    callEval (App f xa, env) (el, envl(fp \<mapsto> (VClsr (Fun fp xp el) envl), xp \<mapsto> va))
  "



 
datatype contin = Ctn name tm env

datatype state = Stt tm env "contin list"

type_synonym trace_pool = "control_path \<rightharpoonup> state"

inductive leaf :: "trace_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro:
  "
    \<not>(pool pi = None) \<Longrightarrow>
    (\<nexists> pi' . \<not>(pool pi' = None) \<and> strict_prefix pi pi') \<Longrightarrow>
    leaf pool pi"

type_synonym corresp = "(control_path * chan * control_path)"

type_synonym communication = "corresp set"

inductive dynamicEval :: "trace_pool * communication \<Rightarrow> trace_pool * communication \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
  Seq_Step_Down:
  "
    \<lbrakk>
      leaf pool pi;
      pool pi = Some (Stt (Rslt x) env ((Ctn xk ek envk) # k)) ;
      env x = Some v
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(pi @ [LRtn x] \<mapsto> (Stt ek (envk(xk \<mapsto> v)) k)), ys)
  "
| Seq_Step:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (Stt (Bind x b e) env k) ;
      seqEval b env v
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> v)) k)), ys)
  "
| Seq_Step_Up:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (Stt (Bind x b e) env k) ;
      callEval (b, env) (e', env')
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(pi @ [LCall x] \<mapsto> (Stt e' env' ((Ctn x e env) # k))), ys)
  "
| BindMkChn:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (Stt (Bind x MkChn e) env k)
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(
      pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> (VChn (Ch pi x)))) k)), ys)
  "
| BindSpawn:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (Stt (Bind x (Spwn ec) e) env k)
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(
      pi @ [LNxt x] \<mapsto> (Stt e (env(x \<mapsto> VUnt)) k),
      pi @ [LSpwn x] \<mapsto> (Stt ec env [])), ys)
  "
| BindSync:
  "
    \<lbrakk>
  
      leaf pool pis ;
      pool pis = Some (Stt (Bind xs (Sync xse) es) envs ks);
      envs xse = Some (VClsr (SendEvt xsc xm) envse);

      leaf pool pir ;
      pool pir = Some (Stt (Bind xr (Sync xre) er) envr kr);
      envr xre = Some (VClsr (RecvEvt xrc) envre);

      envse xsc = Some (VChn c);
      envre xrc = Some (VChn c);     
      envse xm = Some vm

    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (
      pool(
        pis @ [LNxt xs] \<mapsto> (Stt es (envs(xs \<mapsto> VUnt)) ks),
        pir @ [LNxt xr] \<mapsto> (Stt er (envr(xr \<mapsto> vm)) kr)),
      ys \<union> {(pis, c, pir)})
  "


lemma mappingPreservedDynamicEval:
  assumes
      H1: "dynamicEval (env, H) (E', H')" 
  and H2: "env \<pi> = Some \<sigma>"

  shows
  "
     E' \<pi> = Some \<sigma>
  "
proof -

  show "E' \<pi> = Some \<sigma>"
  using H1
  proof cases
    case (Seq_Step_Down pi x env xk ek envk k v)
    have "pi @ [LRtn x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.Seq_Step_Down(3) option.simps(3) strict_prefixI')
    then show ?thesis using H2 local.Seq_Step_Down(1) by auto
  next
    case (Seq_Step pi x b e env k v)
    have "pi @ [LNxt x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.Seq_Step(3) option.simps(3) strict_prefixI')
    then show ?thesis using H2 local.Seq_Step(1) by auto
  next
    case (Seq_Step_Up pi x b e env k e' env')
    have "pi @ [LCall x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.Seq_Step_Up(3) option.simps(3) strict_prefixI')
    then show ?thesis using H2 local.Seq_Step_Up(1) by auto
  next
    case (BindMkChn pi x e env k)
    have "pi @ [LNxt x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.BindMkChn(3) option.simps(3) strict_prefixI')
    then show ?thesis  using H2 local.BindMkChn(1) by auto
  next
    case (BindSpawn pi x ec e env k)

      have "pi @ [LNxt x] \<noteq> \<pi> \<and> pi @ [LSpwn x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.BindSpawn(3) option.simps(3) strict_prefixI')
      then show ?thesis  using H2 local.BindSpawn(1) by auto
  next
    case (BindSync pis xs xse es envs ks xsc xm envse pir xr xre er envr kr xrc envre c vm)
      have "pis @ [LNxt xs] \<noteq> \<pi> \<and> pir @ [LNxt xr] \<noteq> \<pi>" using leaf.simps
      by (metis H2 local.BindSync(3) local.BindSync(6) option.simps(3) strict_prefixI')
    then show ?thesis using H2 local.BindSync(1) by auto
  qed
qed

lemma mappingPreserved:
  assumes
    H1: "star dynamicEval EH EH'" and
    H2: "EH = (env, H)" and
    H3: "EH' = (E', H')" and
    H4: "env \<pi> = Some \<sigma>"

  shows
  "
     E' \<pi> = Some \<sigma>
  "
proof -
 
  have H5:
  "
    \<forall> env H.
    EH = (env, H) \<longrightarrow>
    EH' = (E', H') \<longrightarrow>
    env \<pi> = Some \<sigma> \<longrightarrow>
    E' \<pi> = Some \<sigma>
  "
  using H1
  proof induct
    case (refl x)
    then show ?case by simp
  next
    case (step x y z)

    {
      fix env H
      assume
        L2H1: "x = (env, H)" and
        L2H2: "z = (E', H')" and
        L2H3: "env \<pi> = Some \<sigma>"

      obtain Em Hm where L2H4: "y = (Em, Hm)" by (meson surj_pair)

      have L2H5: "dynamicEval (env, H) (Em, Hm)"
        using L2H1 L2H4 step.hyps(1) by auto

      have "E' \<pi> = Some \<sigma>" using L2H2 L2H3 L2H4 L2H5 mappingPreservedDynamicEval step.hyps(3) by auto
    }
    then show ?case by simp
  qed

  show ?thesis by (simp add: H2 H3 H4 H5)
   
qed


end
