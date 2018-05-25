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


inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<hookrightarrow>" 55) where 
  Result: "
    \<rho> x = Some \<omega> \<Longrightarrow>
    \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>
  " |
  Let_Unit: "
    \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> VUnit]; \<kappa>\<rangle>
  " |
  Let_Prim: "
    \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> (VClosure p \<rho>)]; \<kappa>\<rangle>
  " |
  Let_Fst: "
    \<lbrakk> 
      \<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p); 
      \<rho>\<^sub>p x\<^sub>1 = Some \<omega> 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> \<omega>]; \<kappa>\<rangle>
  " |
  Let_Snd: "
    \<lbrakk> 
      \<rho> x\<^sub>p = Some (VClosure (Pair x\<^sub>1 x\<^sub>2) \<rho>\<^sub>p); 
      \<rho>\<^sub>p x\<^sub>2 = Some \<omega> 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> \<omega>]; \<kappa>\<rangle>
  " |
  Let_Case_Left: "
    \<lbrakk> 
      \<rho> x\<^sub>s = Some (VClosure (Left x\<^sub>l') \<rho>\<^sub>l); 
      \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> 
    \<langle>e\<^sub>l; \<rho> ++ [x\<^sub>l \<mapsto> \<omega>\<^sub>l]; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<rho> x\<^sub>s = Some (VClosure (Right x\<^sub>r') \<rho>\<^sub>r); 
      \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> 
    \<langle>e\<^sub>r; \<rho> ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>r]; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
  " |
  Let_App: "
    \<lbrakk>
      \<rho> f = Some (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l); 
      \<rho> x\<^sub>a = Some \<omega>\<^sub>a 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> 
    \<langle>e\<^sub>l; \<rho>\<^sub>l ++ [f\<^sub>l \<mapsto> (VClosure (Abs f\<^sub>l x\<^sub>l e\<^sub>l) \<rho>\<^sub>l), x\<^sub>l \<mapsto> \<omega>\<^sub>a]; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
  "



type_synonym trace_pool = "control_path \<rightharpoonup> state"

inductive leaf :: "trace_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  "\<not>(\<E> \<pi> = None) \<and> (\<nexists> \<pi>' . \<not>(\<E> \<pi>' = None) \<and> strict_prefix \<pi> \<pi>') \<Longrightarrow> leaf \<E> \<pi>"


abbreviation control_path_append :: "control_path => control_label => control_path" (infixl ";;" 61) where
  "\<pi>;;lab \<equiv> \<pi> @ [lab]"


inductive concur_step :: "trace_pool \<Rightarrow> trace_pool \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Seq_Step_Down: "
    \<lbrakk> 
      leaf \<E> \<pi>;
      \<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) ;
      \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;(LReturn x\<^sub>\<kappa>) \<mapsto> \<sigma>']
  " |
  Seq_Step: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) ;
      \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho>'; \<kappa>\<rangle>
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;(LNext x) \<mapsto> \<langle>e; \<rho>'; \<kappa>\<rangle>]
  " |
  Seq_Step_Up: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) ;
      \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e'; \<rho>'; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;(LCall x) \<mapsto> \<langle>e'; \<rho>'; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>]
  " |
  Let_Chan: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>;;(LNext x) \<mapsto> (\<langle>e; \<rho> ++ [x \<mapsto> (VChan (Ch \<pi> x))]; \<kappa>\<rangle>)
    ]
  " |
  Let_Spawn: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>;;(LNext x) \<mapsto> (\<langle>e; \<rho> ++ [x \<mapsto> VUnit]; \<kappa>\<rangle>), 
      \<pi>;;(LSpawn x) \<mapsto> (\<langle>e\<^sub>c; \<rho>; []\<rangle>) 
    ]
  " |
  Let_Sync: "
    \<lbrakk>
   
      leaf \<E> \<pi>\<^sub>s ;
      \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>);
      \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>s\<^sub>e);

      leaf \<E> \<pi>\<^sub>r ;
      \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>);
      \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>r\<^sub>e);

      \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c); 
      \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c);      
      \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m 

    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>\<^sub>s;;(LNext x\<^sub>s) \<mapsto> (\<langle>e\<^sub>s; \<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> VUnit]; \<kappa>\<^sub>s\<rangle>), 
      \<pi>\<^sub>r;;(LNext x\<^sub>r) \<mapsto> (\<langle>e\<^sub>r; \<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m]; \<kappa>\<^sub>r\<rangle>)
    ]
  "

abbreviation dynamic_eval :: "trace_pool \<Rightarrow> trace_pool \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where 
  "\<E> \<rightarrow>* \<E>' \<equiv> star concur_step \<E> \<E>'"

end
