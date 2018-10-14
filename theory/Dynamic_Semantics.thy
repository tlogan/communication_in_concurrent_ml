theory Dynamic_Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" Stars
begin

datatype control_label = 
  LNxt var | LSpwn var | LCall var | LRtn var

type_synonym control_path = "control_label list"

datatype chan = Ch control_path var

datatype val = 
  VUnt | VChn chan | VClsr prim "var \<Rightarrow> val option"

type_synonym env = "var \<Rightarrow> val option"


inductive seq_step :: "bound_exp \<Rightarrow> env \<Rightarrow> val \<Rightarrow> bool" where
  UNIT: "
    seq_step Unt env VUnt
  " |
  PRIM: "
    seq_step (Prim p) env (VClsr p env)
  " |
  FST: "
    env xp = Some (VClsr (Pair x1 x2) envp) \<Longrightarrow>
    envp x1 = Some v \<Longrightarrow>
    seq_step (Fst xp) env v
  " |
  SND: " 
    env xp = Some (VClsr (Pair x1 x2) envp) \<Longrightarrow>
    envp x2 = Some v \<Longrightarrow>
    seq_step (Snd xp) env v"


inductive seq_step_up :: "bound_exp * env \<Rightarrow> exp * env \<Rightarrow> bool" where 
  let_case_left: "
    \<lbrakk> 
      env xs = Some (VClsr (Lft xl') envl); 
      envl xl' = Some vl
    \<rbrakk> \<Longrightarrow>
    seq_step_up (Case xs xl el xr er, env) (el, env(xl \<mapsto> vl))
  " |
  let_case_right: "
    \<lbrakk>
      env xs = Some (VClsr (Rght xr') envr); 
      envr xr' = Some vr
    \<rbrakk> \<Longrightarrow>
    seq_step_up (Case xs xl el xr er, env) (er, env(xr \<mapsto> vr))
  " |
  let_app: "
    \<lbrakk>
      env f = Some (VClsr (Abs fp xp el) envl); 
      env xa = Some va 
    \<rbrakk> \<Longrightarrow>
    seq_step_up (App f xa, env) (el, envl(fp \<mapsto> (VClsr (Abs fp xp el) envl), xp \<mapsto> va))
  "



  
datatype contin = Ctn var exp env

datatype state = State exp env "contin list" ("\<langle>_;_;_\<rangle>" [0, 0, 0] 71) 

type_synonym trace_pool = "control_path \<rightharpoonup> state"

inductive leaf :: "trace_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro: "
    \<not>(trpl pi = None) \<Longrightarrow> 
    (\<nexists> pi' . \<not>(trpl pi' = None) \<and> strict_prefix pi pi') \<Longrightarrow> 
    leaf trpl pi"

type_synonym cmmn_set = "(control_path * chan * control_path) set"

inductive concur_step :: "trace_pool * cmmn_set \<Rightarrow> trace_pool * cmmn_set \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Seq_Step_Down: "
    \<lbrakk> 
      leaf trpl pi;
      trpl pi = Some (\<langle>Rslt x; env; (Ctn xk ek envk) # k\<rangle>) ;
      env x = Some v
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(pi @ [LRtn x] \<mapsto> \<langle>ek; envk(xk \<mapsto> v); k\<rangle>), ys)
  " |
  Seq_Step: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>(Let x b e); env; k\<rangle>) ;
      seq_step b env v
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(pi @ [LNxt x] \<mapsto> \<langle>e; env(x \<mapsto> v); k\<rangle>), ys)
  " |
  Seq_Step_Up: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>(Let x b e); env; k\<rangle>) ;
      seq_step_up (b, env) (e', env')
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(pi @ [LCall x] \<mapsto> \<langle>e'; env'; (Ctn x e env) # k\<rangle>), ys)
  " |
  Let_Chan: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>(Let x MkChn e); env; k\<rangle>)
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(
      pi @ [LNxt x] \<mapsto> (\<langle>e; env(x \<mapsto> (VChn (Ch pi x))); k\<rangle>)), ys)
  " |
  Let_Spawn: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>Let x (Spwn ec) e; env; k\<rangle>)
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(
      pi @ [LNxt x] \<mapsto> (\<langle>e; env(x \<mapsto> VUnt); k\<rangle>), 
      pi @ [LSpwn x] \<mapsto> (\<langle>ec; env; []\<rangle>)), ys)
  " |
  Let_Sync: "
    \<lbrakk>
   
      leaf trpl pis ;
      trpl pis = Some (\<langle>Let xs (Sync xse) es; envs; ks\<rangle>);
      envs xse = Some (VClsr (SendEvt xsc xm) envse);

      leaf trpl pir ;
      trpl pir = Some (\<langle>Let xr (Sync xre) er; envr; kr\<rangle>);
      envr xre = Some (VClsr (RecvEvt xrc) envre);

      envse xsc = Some (VChn c); 
      envre xrc = Some (VChn c);      
      envse xm = Some vm

    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (
      trpl(
        pis @ [LNxt xs] \<mapsto> (\<langle>es; envs(xs \<mapsto> VUnt); ks\<rangle>), 
        pir @ [LNxt xr] \<mapsto> (\<langle>er; envr(xr \<mapsto> vm); kr\<rangle>)), 
      ys \<union> {(pis, c, pir)})
  "


lemma mapping_preserved: 
  assumes 
    H1: "concur_step (E, H) (E', H')" and
    H2: "E \<pi> = Some \<sigma>"

  shows "
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
    case (Let_Chan pi x e env k)
    have "pi @ [LNxt x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.Let_Chan(3) option.simps(3) strict_prefixI')
    then show ?thesis  using H2 local.Let_Chan(1) by auto
  next
    case (Let_Spawn pi x ec e env k)

      have "pi @ [LNxt x] \<noteq> \<pi> \<and> pi @ [LSpwn x] \<noteq> \<pi>" using leaf.simps by (metis H2 local.Let_Spawn(3) option.simps(3) strict_prefixI')
      then show ?thesis  using H2 local.Let_Spawn(1) by auto
  next
    case (Let_Sync pis xs xse es envs ks xsc xm envse pir xr xre er envr kr xrc envre c vm)
      have "pis @ [LNxt xs] \<noteq> \<pi> \<and> pir @ [LNxt xr] \<noteq> \<pi>" using leaf.simps
      by (metis H2 local.Let_Sync(3) local.Let_Sync(6) option.simps(3) strict_prefixI')
    then show ?thesis using H2 local.Let_Sync(1) by auto
  qed
qed

lemma mapping_preserved_star: 
  assumes 
    H1: "star concur_step EH EH'" and
    H2: "EH = (E, H)" and 
    H3: "EH' = (E', H')" and
    H4: "E \<pi> = Some \<sigma>"

  shows "
     E' \<pi> = Some \<sigma>
  "
proof -
  
  have H5: "
    \<forall> E H.
    EH = (E, H) \<longrightarrow> 
    EH' = (E', H') \<longrightarrow>
    E \<pi> = Some \<sigma> \<longrightarrow>
    E' \<pi> = Some \<sigma>
  "
  using H1
  proof induct
    case (refl x)
    then show ?case by simp
  next
    case (step x y z)

    {
      fix E H
      assume 
        L2H1: "x = (E, H)" and 
        L2H2: "z = (E', H')" and 
        L2H3: "E \<pi> = Some \<sigma>"

      obtain Em Hm where L2H4: "y = (Em, Hm)" by (meson surj_pair)

      have L2H5: "concur_step (E, H) (Em, Hm)"
        using L2H1 L2H4 step.hyps(1) by auto

      have "E' \<pi> = Some \<sigma>" using L2H2 L2H3 L2H4 L2H5 mapping_preserved step.hyps(3) by auto
    }
    then show ?case by simp
  qed

  show ?thesis by (simp add: H2 H3 H4 H5)
    
qed


end
