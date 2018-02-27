theory Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" Stars
begin

datatype control_label = 
  M var ("`_" [71] 70) | 
  C var ("._" [71] 70) | 
  Up var ("\<upharpoonleft>_" [71] 70) |
  Down var ("\<downharpoonleft>_" [71] 70)

type_synonym control_path = "control_label list"

datatype chan = Ch control_path var


datatype val = 
  V_Chan chan ("\<lbrace>_\<rbrace>") |
  V_Closure prim "var \<rightharpoonup> val" ("\<lbrace>_, _\<rbrace>") |
  V_Unit ("\<lbrace>\<rbrace>")

fun val_to_bind :: "val \<Rightarrow> bind" where
  "val_to_bind \<lbrace> _ \<rbrace> = CHAN \<lparr>\<rparr>" |
  "val_to_bind \<lbrace>p, _ \<rbrace> = Prim p" |
  "val_to_bind \<lbrace>\<rbrace> = \<lparr>\<rparr>"

type_synonym val_env = "var \<rightharpoonup> val"

datatype cont = Cont var exp val_env ("\<langle>_,_,_\<rangle>" [0, 0, 0] 70) 

datatype state = State exp val_env "cont list" ("\<langle>_;_;_\<rangle>" [0, 0, 0] 71) 
  
type_synonym state_pool = "control_path \<rightharpoonup> state"

  
inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<hookrightarrow>" 55) where 
  Result: "
    \<rho> x = Some \<omega> \<Longrightarrow>
    \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>
  " |
  Let_Unit: "
    \<langle>LET x = \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>]; \<kappa>\<rangle>
  " |
  Let_Prim: "
    \<langle>LET x = Prim p in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> \<lbrace>p, \<rho>\<rbrace>]; \<kappa>\<rangle>
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<rho> x\<^sub>s = Some \<lbrace>Left x\<^sub>l', \<rho>\<^sub>l\<rbrace>; 
      \<rho>\<^sub>l x\<^sub>l' = Some \<omega>\<^sub>l 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e\<^sub>l; \<rho> ++ [x\<^sub>l \<mapsto> \<omega>\<^sub>l]; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<rho> x\<^sub>s = Some \<lbrace>Right x\<^sub>r', \<rho>\<^sub>r\<rbrace>; 
      \<rho>\<^sub>r x\<^sub>r' = Some \<omega>\<^sub>r 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e\<^sub>r; \<rho> ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>r]; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
  " |
  Fst: "
    \<lbrakk> 
      \<rho> x\<^sub>p = Some \<lbrace>Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>; 
      \<rho>\<^sub>p x\<^sub>1 = Some \<omega> 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = FST x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> \<omega>]; \<kappa>\<rangle>
  " |
  Snd: "
    \<lbrakk> 
      \<rho> x\<^sub>p = Some \<lbrace>Pair x\<^sub>1 x\<^sub>2, \<rho>\<^sub>p\<rbrace>; 
      \<rho>\<^sub>p x\<^sub>2 = Some \<omega> 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = SND x\<^sub>p in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e; \<rho> ++ [x \<mapsto> \<omega>]; \<kappa>\<rangle>
  " |
  Let_App: "
    \<lbrakk>
      \<rho> f = Some \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace> ; 
      \<rho> x\<^sub>a = Some \<omega>\<^sub>a 
    \<rbrakk> \<Longrightarrow>
    \<langle>LET x = APP f x\<^sub>a in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> 
    \<langle>e\<^sub>l; \<rho>\<^sub>l ++ [f\<^sub>l \<mapsto> \<lbrace>Abs f\<^sub>l x\<^sub>l e\<^sub>l, \<rho>\<^sub>l\<rbrace>, x\<^sub>l \<mapsto> \<omega>\<^sub>a]; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
  "

inductive_cases Result_E[elim!]: "\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<langle>e\<^sub>\<kappa>; \<rho>\<^sub>\<kappa> ++ [x\<^sub>\<kappa> \<mapsto> \<omega>]; \<kappa>\<rangle>"

abbreviation control_path_append :: "control_path => control_label => control_path" (infixl ";;" 61) where
  "\<pi>;;lab \<equiv> \<pi> @ [lab]"
  
definition leaf :: "state_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  "leaf \<E> \<pi> \<equiv> \<not>(\<E> \<pi> = None) \<and> (\<nexists> \<pi>' . \<not>(\<E> \<pi>' = None) \<and> strict_prefix \<pi> \<pi>')"


lemma leaf_elim: "
  \<lbrakk> leaf \<E> \<pi>; strict_prefix \<pi> \<pi>' \<rbrakk> \<Longrightarrow>
   \<E> \<pi>' = None
"
using leaf_def by blast
  
inductive concur_step :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Seq_Step_Down: "
    \<lbrakk> 
      leaf \<E> \<pi>;
      \<E> \<pi> = Some (\<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle>) ;
      \<langle>RESULT x; \<rho>; \<langle>x\<^sub>\<kappa>, e\<^sub>\<kappa>, \<rho>\<^sub>\<kappa>\<rangle> # \<kappa>\<rangle> \<hookrightarrow> \<sigma>'
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;\<downharpoonleft>x\<^sub>\<kappa> \<mapsto> \<sigma>']
  " |
  Seq_Step_Up: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) ;
      \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e'; \<rho>'; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;\<upharpoonleft>x \<mapsto> \<langle>e'; \<rho>'; \<langle>x, e, \<rho>\<rangle> # \<kappa>\<rangle>]
  " |
  Seq_Step: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) ;
      \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<langle>e'; \<rho>'; \<kappa>\<rangle>
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;`x \<mapsto> \<langle>e'; \<rho>'; \<kappa>\<rangle>]
  " |
  Sync: "
    \<lbrakk>
   
      leaf \<E> \<pi>\<^sub>s ;
      \<E> \<pi>\<^sub>s = Some (\<langle>LET x\<^sub>s = SYNC x\<^sub>s\<^sub>e in e\<^sub>s; \<rho>\<^sub>s; \<kappa>\<^sub>s\<rangle>);
      \<rho>\<^sub>s x\<^sub>s\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>s\<^sub>e\<rbrace>;
      \<rho>\<^sub>s\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace>; 
      
      \<rho>\<^sub>s\<^sub>e x\<^sub>m = Some \<omega>\<^sub>m ;

      leaf \<E> \<pi>\<^sub>r ;
      \<E> \<pi>\<^sub>r = Some (\<langle>LET x\<^sub>r = SYNC x\<^sub>r\<^sub>e in e\<^sub>r; \<rho>\<^sub>r; \<kappa>\<^sub>r\<rangle>);
      \<rho>\<^sub>r x\<^sub>r\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>r\<^sub>e\<rbrace>;
      \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>;
  
      x\<^sub>s \<noteq> x\<^sub>r

    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>\<^sub>s;;`x\<^sub>s \<mapsto> (\<langle>e\<^sub>s; \<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>]; \<kappa>\<^sub>s\<rangle>), 
      \<pi>\<^sub>r;;`x\<^sub>r \<mapsto> (\<langle>e\<^sub>r; \<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m]; \<kappa>\<^sub>r\<rangle>)
    ]
  " |
  Let_Chan: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>;;`x \<mapsto> (\<langle>e; \<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>]; \<kappa>\<rangle>)
    ]
  " |
  Let_Spawn: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>;;`x \<mapsto> (\<langle>e; \<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>]; \<kappa>\<rangle>), 
      \<pi>;;.x \<mapsto> (\<langle>e\<^sub>c; \<rho>; []\<rangle>) 
    ]
  "

abbreviation concur_steps :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where 
  "\<E> \<rightarrow>* \<E>' \<equiv> star concur_step \<E> \<E>'"


fun start_state :: "exp \<Rightarrow> state_pool" where
 "start_state e = [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>]"




inductive path_balanced :: "control_path \<Rightarrow> bool" ("\<downharpoonright>_\<upharpoonleft>" [0]55) where
  Empty[simp]: "
    \<downharpoonright>[]\<upharpoonleft>
  " |
  Linear[simp]: "
    \<downharpoonright>[`x]\<upharpoonleft>
  " |
  Up_Down[simp]: "
    \<downharpoonright>\<pi>\<upharpoonleft> \<Longrightarrow>
    \<downharpoonright> (\<upharpoonleft>x # (\<pi> ;; \<downharpoonleft>x)) \<upharpoonleft>
  " |
  Append[simp]: "
    \<downharpoonright>\<pi>\<upharpoonleft> \<Longrightarrow> \<downharpoonright>\<pi>'\<upharpoonleft> \<Longrightarrow>
    \<downharpoonright> (\<pi> @ \<pi>') \<upharpoonleft>
  "
  

inductive linear :: "control_path \<Rightarrow> bool"("``_``" [0]55) where
  Empty: "
    ``[]``
  " |
  Seq_Cons: "
    ``\<pi>`` \<Longrightarrow>
    `` (`x # \<pi>) ``
  " |
  Up_Cons: "
    ``\<pi>`` \<Longrightarrow>
    `` (\<upharpoonleft>x # \<pi>) ``
  " |
  Down_Cons: "
    ``\<pi>`` \<Longrightarrow>
    `` (\<downharpoonleft>x # \<pi>) ``
  " 

lemma linear_preserved_over_linear_extension': "
  ``\<pi>`` \<Longrightarrow> ``\<pi>'`` \<longrightarrow> ``\<pi> @ \<pi>'``
"
 apply (erule linear.induct; auto)
 apply (erule Seq_Cons)
 apply (erule Up_Cons)
 apply (erule Down_Cons)
done

lemma  linear_preserved_over_linear_extension[simp]: "
  ``\<pi>`` \<Longrightarrow> ``\<pi>'`` \<Longrightarrow> ``\<pi> @ \<pi>'``
"
by (simp add: linear_preserved_over_linear_extension')

lemma up_down_balanced[simp]: "
   \<downharpoonright>[\<upharpoonleft>x, \<downharpoonleft>x] \<upharpoonleft>
"
using Up_Down path_balanced.Empty by fastforce


end
