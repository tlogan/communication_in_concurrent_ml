theory Dynamic_Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" Stars
begin


datatype control_label = 
  LNxt var | LSpwn var | LCall var | LRtn var

type_synonym control_path = "control_label list"

datatype chan = Ch control_path var

datatype val = 
  VUnt | VChn chan | VClsr prim "var \<rightharpoonup> val"

type_synonym env = "var \<rightharpoonup> val"


inductive seq_step :: "(bind \<times> env) \<Rightarrow> val \<Rightarrow> bool" where
  Let_Unit: "
    seq_step (Unt, env) VUnt
  " |
  Let_Prim: "
    seq_step (Prim p, env) (VClsr p env)
  " |
  Let_Fst: "
    \<lbrakk> 
      env xp = Some (VClsr (Pair x1 x2) envp); 
      envp x1 = Some v
    \<rbrakk> \<Longrightarrow>
    seq_step (Fst xp, env) v
  " |
  Let_Snd: "
    \<lbrakk> 
      env xp = Some (VClsr (Pair x1 x2) envp); 
      envp x2 = Some v
    \<rbrakk> \<Longrightarrow>
    seq_step (Snd xp, env) v
  "


inductive seq_step_up :: "bind * env \<Rightarrow> exp * env \<Rightarrow> bool" where 
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
    (trpl, ys) \<rightarrow> (trpl(pi @ [LRtn xk] \<mapsto> \<langle>ek; envk(xk \<mapsto> v); k\<rangle>), ys)
  " |
  Seq_Step: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>(Let x b e); env; k\<rangle>) ;
      seq_step (b, env) v
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

end
