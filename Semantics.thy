theory Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" "~~/src/HOL/IMP/Star"
begin

  
type_synonym control_path = "(var + unit) list"
datatype chan = Ch control_path var


datatype val = 
  V_Chan chan ("\<lbrace>_\<rbrace>") |
  V_Closure prim "var \<rightharpoonup> val" ("\<lbrace>_, _\<rbrace>") |
  V_Unit ("\<lbrace>\<rbrace>")
 
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

abbreviation control_path_append_var :: "control_path => var => control_path" (infixl ";;" 61) where
  "\<pi>;;x \<equiv> \<pi> @ [Inl x]"
  
abbreviation control_path_append_unit :: "control_path  => control_path" ("_;;." [60]61) where
  "\<pi>;;. \<equiv> \<pi> @ [Inr ()]"
  
  
definition leaf :: "state_pool \<Rightarrow> control_path \<Rightarrow> bool" where
  "leaf \<E> \<pi> \<equiv> \<not>(\<E> \<pi> = None) \<and> (\<nexists> \<pi>' . \<not>(\<E> \<pi>' = None) \<and> strict_prefix \<pi> \<pi>')"


lemma leaf_elim: "
  \<lbrakk> leaf \<E> \<pi>; strict_prefix \<pi> \<pi>' \<rbrakk> \<Longrightarrow>
   \<E> \<pi>' = None
"
using leaf_def by blast
(*
type_synonym val_pool = "control_path \<rightharpoonup> val"
inductive sync_step :: "val_pool \<Rightarrow> val_pool \<Rightarrow> bool" (infix "\<leadsto>" 55) where 
  Sync_Send_Recv: "
    \<lbrakk>
      Some (V_Chan _) = \<rho>_s x_ch_s; \<rho>_r x_ch_r = \<rho>_s x_ch_s ; (\<rho>_s x_m) = Some \<omega>_m
    \<rbrakk> \<Longrightarrow>
    [\<pi>_s \<mapsto> \<lbrace>Send_Evt x_ch_s x_m, \<rho>_s\<rbrace>, \<pi>_r \<mapsto> \<lbrace>Recv_Evt x_ch_r, \<rho>_r\<rbrace>] \<leadsto> 
    [\<pi>_s \<mapsto> \<lbrace>Always_Evt x_a_s, [x_a_s \<mapsto> \<lbrace>\<rbrace>]\<rbrace>, \<pi>_r \<mapsto> \<lbrace>Always_Evt x_a_r, [x_a_r \<mapsto> \<omega>_m]\<rbrace>]
  "

lemma "
(
  \<And> vpool vpool' stpool stpool_sync . 
    vpool \<leadsto> vpool' \<Longrightarrow>
    (\<forall> \<pi>' e \<rho>' \<kappa> .
      stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) \<longrightarrow>
      (\<exists> x \<omega>_a x_a \<rho> x_evt \<pi> .
        \<pi>' = \<pi>;;x \<and>
        \<rho>' = \<rho>(x \<mapsto> \<omega>_a) \<and>
        vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<and>
        vpool \<pi> = \<rho> x_evt \<and>
        stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and>
        leaf stpool \<pi>
      )
    ) \<Longrightarrow>
    (\<exists> \<pi>' e \<rho>' \<kappa> . stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) )
  
)
 \<Longrightarrow>
(
  \<And> vpool vpool' stpool stpool_sync \<pi> \<pi>' e \<rho>' \<kappa> x \<omega>_a x_a \<rho> x_evt .
    vpool \<leadsto> vpool' \<Longrightarrow>
    stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) \<Longrightarrow>
    \<rho>' = \<rho>(x \<mapsto> \<omega>_a) \<Longrightarrow>
    vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<Longrightarrow>
    vpool \<pi> = \<rho> x_evt \<Longrightarrow>
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<Longrightarrow>
    leaf stpool \<pi>
)
"
  using option.simps(3) by fastforce

lemma "
(
  \<And> vpool vpool' stpool stpool_sync \<pi> \<pi>' e \<rho>' \<kappa> x \<omega>_a x_a \<rho> x_evt . \<lbrakk>
    vpool \<leadsto> vpool' ;
    stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) ;
    \<pi>' = \<pi>;;x ;
    \<rho>' = \<rho>(x \<mapsto> \<omega>_a) ;
    vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> ;
    vpool \<pi> = \<rho> x_evt ;
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) ;
    leaf stpool \<pi>
  \<rbrakk> \<Longrightarrow>
  step stpool (stpool ++ stpool_sync)
) 

\<Longrightarrow>

(
  \<And> vpool vpool' stpool stpool_sync . \<lbrakk>
    vpool \<leadsto> vpool' ;
    (\<forall> \<pi>' e \<rho>' \<kappa> .
      stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) \<longrightarrow>
      (\<exists> x \<omega>_a x_a \<rho> x_evt \<pi> .
        \<pi>' = \<pi>;;x \<and>
        \<rho>' = \<rho>(x \<mapsto> \<omega>_a) \<and>
        vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<and>
        vpool \<pi> = \<rho> x_evt \<and>
        stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and>
        leaf stpool \<pi>
      )
    ) ;
    (\<exists> \<pi>' e \<rho>' \<kappa> . stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) )
  \<rbrakk> \<Longrightarrow>
  step stpool (stpool ++ stpool_sync)
)
"
by meson
*)  
  
inductive concur_step :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Seq_Step: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = b in e; \<rho>; \<kappa>\<rangle>) ;
      \<langle>LET x = b in e; \<rho>; \<kappa>\<rangle> \<hookrightarrow> \<sigma>'
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [\<pi>;;x \<mapsto> \<sigma>']
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
      \<rho>\<^sub>r\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace>

    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>\<^sub>s;;x\<^sub>s \<mapsto> (\<langle>e\<^sub>s; \<rho>\<^sub>s ++ [x\<^sub>s \<mapsto> \<lbrace>\<rbrace>]; \<kappa>\<^sub>s\<rangle>), 
      \<pi>\<^sub>r;;x\<^sub>r \<mapsto> (\<langle>e\<^sub>r; \<rho>\<^sub>r ++ [x\<^sub>r \<mapsto> \<omega>\<^sub>m]; \<kappa>\<^sub>r\<rangle>)
    ]
  " |
  Let_Chan: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e; \<rho>; \<kappa>\<rangle>)
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>;;x \<mapsto> (\<langle>e; \<rho> ++ [x \<mapsto> \<lbrace>Ch \<pi> x\<rbrace>]; \<kappa>\<rangle>)
    ]
  " |
  Let_Spawn: "
    \<lbrakk> 
      leaf \<E> \<pi> ;
      \<E> \<pi> = Some (\<langle>LET x = SPAWN e\<^sub>c in e; \<rho>; \<kappa>\<rangle>)
    \<rbrakk> \<Longrightarrow>
    \<E> \<rightarrow> \<E> ++ [
      \<pi>;;x \<mapsto> (\<langle>e; \<rho> ++ [x \<mapsto> \<lbrace>\<rbrace>]; \<kappa>\<rangle>), 
      \<pi>;;. \<mapsto> (\<langle>e\<^sub>c; \<rho>; []\<rangle>) 
    ]
  "   

abbreviation concur_steps :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where 
  "\<E> \<rightarrow>* \<E>' \<equiv> star concur_step \<E> \<E>'"


lemma result_final: "
  [[] \<mapsto> \<langle>e;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
  \<E>' \<pi> = Some (\<langle>LET x\<^sub>l = b in e';\<rho>';\<kappa>'\<rangle>) \<Longrightarrow>
  e \<noteq> RESULT x
"
 apply (erule star.cases; auto)
  apply (case_tac "\<pi> = []"; auto)
 apply (erule concur_step.cases)
  apply (metis exp.distinct(1) fun_upd_apply option.distinct(1) option.inject state.inject)
  apply (metis fun_upd_apply option.distinct(1) option.inject state.inject)
  apply (metis exp.simps(4) fun_upd_apply option.distinct(1) option.inject state.inject)+
done

end
