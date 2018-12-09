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

datatype state = State tm env "contin list" ("\<langle>_;_;_\<rangle>" [0, 0, 0] 71)

type_synonym trace_pool = "control_path \<rightharpoonup> state"

inductive leaf :: "trace_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro:
  "
    \<not>(pool pi = None) \<Longrightarrow>
    (\<nexists> pi' . \<not>(pool pi' = None) \<and> strict_prefix pi pi') \<Longrightarrow>
    leaf pool pi"

type_synonym cmmn_set = "(control_path * chan * control_path) set"

inductive dynamicEval :: "trace_pool * cmmn_set \<Rightarrow> trace_pool * cmmn_set \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
  Seq_Step_Down:
  "
    \<lbrakk>
      leaf pool pi;
      pool pi = Some (\<langle>Rslt x; env; (Ctn xk ek envk) # k\<rangle>) ;
      env x = Some v
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(pi @ [LRtn x] \<mapsto> \<langle>ek; envk(xk \<mapsto> v); k\<rangle>), ys)
  "
| Seq_Step:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (\<langle>(Bind x b e); env; k\<rangle>) ;
      seqEval b env v
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(pi @ [LNxt x] \<mapsto> \<langle>e; env(x \<mapsto> v); k\<rangle>), ys)
  "
| Seq_Step_Up:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (\<langle>(Bind x b e); env; k\<rangle>) ;
      callEval (b, env) (e', env')
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(pi @ [LCall x] \<mapsto> \<langle>e'; env'; (Ctn x e env) # k\<rangle>), ys)
  "
| BindMkChn:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (\<langle>(Bind x MkChn e); env; k\<rangle>)
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(
      pi @ [LNxt x] \<mapsto> (\<langle>e; env(x \<mapsto> (VChn (Ch pi x))); k\<rangle>)), ys)
  "
| BindSpawn:
  "
    \<lbrakk>
      leaf pool pi ;
      pool pi = Some (\<langle>Bind x (Spwn ec) e; env; k\<rangle>)
    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (pool(
      pi @ [LNxt x] \<mapsto> (\<langle>e; env(x \<mapsto> VUnt); k\<rangle>),
      pi @ [LSpwn x] \<mapsto> (\<langle>ec; env; []\<rangle>)), ys)
  "
| BindSync:
  "
    \<lbrakk>
  
      leaf pool pis ;
      pool pis = Some (\<langle>Bind xs (Sync xse) es; envs; ks\<rangle>);
      envs xse = Some (VClsr (SendEvt xsc xm) envse);

      leaf pool pir ;
      pool pir = Some (\<langle>Bind xr (Sync xre) er; envr; kr\<rangle>);
      envr xre = Some (VClsr (RecvEvt xrc) envre);

      envse xsc = Some (VChn c);
      envre xrc = Some (VChn c);     
      envse xm = Some vm

    \<rbrakk> \<Longrightarrow>
    (pool, ys) \<rightarrow> (
      pool(
        pis @ [LNxt xs] \<mapsto> (\<langle>es; envs(xs \<mapsto> VUnt); ks\<rangle>),
        pir @ [LNxt xr] \<mapsto> (\<langle>er; envr(xr \<mapsto> vm); kr\<rangle>)),
      ys \<union> {(pis, c, pir)})
  "


lemma mapping_preserved:
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

lemma mapping_preserved_star:
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

      have "E' \<pi> = Some \<sigma>" using L2H2 L2H3 L2H4 L2H5 mapping_preserved step.hyps(3) by auto
    }
    then show ?case by simp
  qed

  show ?thesis by (simp add: H2 H3 H4 H5)
   
qed


end
