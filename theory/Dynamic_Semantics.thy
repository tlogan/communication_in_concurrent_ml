theory Dynamic_Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" Stars
begin


datatype control_label = 
  LNext var | 
  LSpawn var |
  LCall var |
  LReturn var

type_synonym control_path = "control_label list"

datatype chan = Ch control_path var

datatype val = 
  VUnit |
  VChan chan |
  VClosure prim "var \<rightharpoonup> val"

type_synonym val_env = "var \<rightharpoonup> val"
  
datatype cont = Cont var exp val_env ("\<langle>_,_,_\<rangle>" [0, 0, 0] 70) 

datatype state = State exp val_env "cont list" ("\<langle>_;_;_\<rangle>" [0, 0, 0] 71) 


inductive seq_step :: "(bind \<times> val_env) \<Rightarrow> val \<Rightarrow> bool" where
  Let_Unit: "
    seq_step (\<lparr>\<rparr>, env) VUnit
  " |
  Let_Prim: "
    seq_step (Prim p, env) (VClosure p env)
  " |
  Let_Fst: "
    \<lbrakk> 
      env xp = Some (VClosure (Pair x1 x2) envp); 
      envp x1 = Some v
    \<rbrakk> \<Longrightarrow>
    seq_step (FST xp, env) v
  " |
  Let_Snd: "
    \<lbrakk> 
      env xp = Some (VClosure (Pair x1 x2) envp); 
      envp x2 = Some v
    \<rbrakk> \<Longrightarrow>
    seq_step (SND xp, env) v
  "


inductive seq_step_up :: "bind * val_env \<Rightarrow> exp * val_env \<Rightarrow> bool" where 
  Let_Case_Left: "
    \<lbrakk> 
      env xs = Some (VClosure (Left xl') envl); 
      envl xl' = Some vl
    \<rbrakk> \<Longrightarrow>
    seq_step_up (CASE xs LEFT xl |> el RIGHT xr |> er, env) (el, env(xl \<mapsto> vl))
  " |
  Let_Case_Right: "
    \<lbrakk>
      env xs = Some (VClosure (Right xr') envr); 
      envr xr' = Some vr
    \<rbrakk> \<Longrightarrow>
    seq_step_up (CASE xs LEFT xl |> el RIGHT xr |> er, env) (er, env(xr \<mapsto> vr))
  " |
  Let_App: "
    \<lbrakk>
      env f = Some (VClosure (Abs fp xp el) envl); 
      env xa = Some va 
    \<rbrakk> \<Longrightarrow>
    seq_step_up (APP f xa, env) (el, envl(fp \<mapsto> (VClosure (Abs fp xp el) envl), xp \<mapsto> va))
  "


type_synonym trace_pool = "control_path \<rightharpoonup> state"

inductive leaf :: "trace_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro: "
    \<not>(trpl pi = None) \<Longrightarrow> 
    (\<nexists> pi' . \<not>(trpl pi' = None) \<and> strict_prefix pi pi') \<Longrightarrow> 
    leaf trpl pi"

abbreviation control_path_append :: "control_path => control_label => control_path" (infixl ";;" 61) where
  "pi;;lab \<equiv> pi @ [lab]"

type_synonym cmmn_set = "(control_path * chan * control_path) set"

inductive concur_step :: "trace_pool * cmmn_set \<Rightarrow> trace_pool * cmmn_set \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Seq_Step_Down: "
    \<lbrakk> 
      leaf trpl pi;
      trpl pi = Some (\<langle>RESULT x; env; \<langle>xk, ek, envk\<rangle> # k\<rangle>) ;
      env x = Some v
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(pi;;(LReturn xk) \<mapsto> \<langle>ek; envk(xk \<mapsto> v); k\<rangle>), ys)
  " |
  Seq_Step: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>LET x = b in e; env; k\<rangle>) ;
      seq_step (b, env) v
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(pi;;(LNext x) \<mapsto> \<langle>e; env(x \<mapsto> v); k\<rangle>), ys)
  " |
  Seq_Step_Up: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>LET x = b in e; env; k\<rangle>) ;
      seq_step_up (b, env) (e', env')
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(pi;;(LCall x) \<mapsto> \<langle>e'; env'; \<langle>x, e, env\<rangle> # k\<rangle>), ys)
  " |
  Let_Chan: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; env; k\<rangle>)
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(
      pi;;(LNext x) \<mapsto> (\<langle>e; env(x \<mapsto> (VChan (Ch pi x))); k\<rangle>)), ys)
  " |
  Let_Spawn: "
    \<lbrakk> 
      leaf trpl pi ;
      trpl pi = Some (\<langle>LET x = SPAWN ec in e; env; k\<rangle>)
    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (trpl(
      pi;;(LNext x) \<mapsto> (\<langle>e; env(x \<mapsto> VUnit); k\<rangle>), 
      pi;;(LSpawn x) \<mapsto> (\<langle>ec; env; []\<rangle>)), ys)
  " |
  Let_Sync: "
    \<lbrakk>
   
      leaf trpl pis ;
      trpl pis = Some (\<langle>LET xs = SYNC xse in es; envs; ks\<rangle>);
      envs xse = Some (VClosure (Send_Evt xsc xm) envse);

      leaf trpl pir ;
      trpl pir = Some (\<langle>LET xr = SYNC xre in er; envr; kr\<rangle>);
      envr xre = Some (VClosure (Recv_Evt xrc) envre);

      envse xsc = Some (VChan c); 
      envre xrc = Some (VChan c);      
      envse xm = Some vm

    \<rbrakk> \<Longrightarrow>
    (trpl, ys) \<rightarrow> (
      trpl(
        pis;;(LNext xs) \<mapsto> (\<langle>es; envs(xs \<mapsto> VUnit); ks\<rangle>), 
        pir;;(LNext xr) \<mapsto> (\<langle>er; envr(xr \<mapsto> vm); kr\<rangle>)), 
      ys \<union> {(pis, c, pir)})
  "

abbreviation dynamic_eval :: "trace_pool * cmmn_set \<Rightarrow> trace_pool * cmmn_set \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where 
  "X \<rightarrow>* X' \<equiv> star concur_step X X'"

end
