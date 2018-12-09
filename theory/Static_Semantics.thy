theory Static_Semantics
  imports Main Syntax Dynamic_Semantics
    "~~/src/HOL/Library/List"
begin

datatype static_val = 
  SChn name ("^Chan _" [61] 61) 
| SUnt ("^Unt") 
| SAtm atom ("^_" [61] 61 )

type_synonym static_env = "name \<Rightarrow> static_val set"

fun resultName :: "tm \<Rightarrow> name" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>Rslt x\<rfloor> = x"
| "\<lfloor>Bind _ _ e\<rfloor> = \<lfloor>e\<rfloor>"


inductive staticEval :: "static_env \<times> static_env \<Rightarrow> tm \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result:
  "
    staticEval (\<V>, \<C>) (Rslt x)
  "
| BindUnit:
  "
    \<lbrakk>
      {^Unt} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x Unt e)
  " 
| BindMkChn:
  "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow>  
    staticEval (\<V>, \<C>) (Bind x MkChn e)
  " 
| BindSendEvt :
  "
    \<lbrakk>
      {^(SendEvt x\<^sub>c x\<^sub>m)} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Atom (SendEvt x\<^sub>c x\<^sub>m)) e)
  "
| BindRecvEvt :
  "
    \<lbrakk>
      {^(RecvEvt x\<^sub>c)} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Atom (RecvEvt x\<^sub>c)) e)
  " 
| BindPair :
  "
    \<lbrakk>
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Atom (Pair x\<^sub>1 x\<^sub>2)) e)
  "
| BindLft :
  "
    \<lbrakk>
      {^(Lft x\<^sub>p)} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Atom (Lft x\<^sub>p)) e)
  "
| BindRht :
  "
    \<lbrakk>
      {^(Rht x\<^sub>p)} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Atom (Rht x\<^sub>p)) e)
  " 
| BindFun :
  "
    \<lbrakk>
      {^Fun f' x' e'} \<subseteq> \<V> f';
      staticEval (\<V>, \<C>) e';
      {^Fun f' x' e'} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Atom (Fun f' x' e')) e)
  " 
| BindSpawn:
  "
    \<lbrakk>
      {^Unt} \<subseteq> \<V> x;
      staticEval (\<V>, \<C>) e\<^sub>c;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow>  
    staticEval (\<V>, \<C>) (Bind x (Spwn e\<^sub>c) e)
  " 
| BindSync  :
  "
    \<lbrakk>
      \<forall> x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c . 
        ^(SendEvt x\<^sub>s\<^sub>c x\<^sub>m) \<in> \<V> x\<^sub>e \<longrightarrow> 
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow>
        {^Unt} \<subseteq> \<V> x \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
      ;
      \<forall> x\<^sub>r\<^sub>c x\<^sub>c . 
        ^(RecvEvt x\<^sub>r\<^sub>c) \<in> \<V> x\<^sub>e \<longrightarrow>
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow>
        \<C> x\<^sub>c \<subseteq> \<V> x
      ;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow>  
    staticEval (\<V>, \<C>) (Bind x (Sync x\<^sub>e) e)
  " 
| BindFst:
  "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      staticEval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Fst x\<^sub>p) e)
  "
| BindSnd:
  "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Snd x\<^sub>p) e)
  "
| BindCase:
  "
    \<lbrakk>
      \<forall> x\<^sub>l' . ^(Lft x\<^sub>l') \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x
      ; 
      staticEval (\<V>, \<C>) e\<^sub>l ;
      \<forall> x\<^sub>r' . ^(Rht x\<^sub>r') \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x
      ;
      staticEval (\<V>, \<C>) e\<^sub>r;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  "
| App:
  "
    \<lbrakk>
      \<forall> f' x' e' . ^Fun f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      staticEval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    staticEval (\<V>, \<C>) (Bind x (App f x\<^sub>a) e)
  "

inductive staticReachable :: "tm \<Rightarrow> tm \<Rightarrow> bool"  where
  Refl:
  "
    staticReachable e e
  " | 
  BindSpawn_Child:
  "
    staticReachable e\<^sub>c e \<Longrightarrow>
    staticReachable (Bind x (Spwn e\<^sub>c) e\<^sub>n) e
  "
| CaseLft:
  "
    staticReachable e\<^sub>l e \<Longrightarrow>
    staticReachable (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e
  "
| CaseRht:
  "
    staticReachable e\<^sub>r e \<Longrightarrow>
    staticReachable (Bind x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e
  "
| BindFun:
  "
    staticReachable e\<^sub>b e \<Longrightarrow>
    staticReachable (Bind x (Atom (Fun f x\<^sub>p e\<^sub>b)) e\<^sub>n) e
  " 
| Bind:
  "
    staticReachable e\<^sub>n e \<Longrightarrow>
    staticReachable (Bind x b e\<^sub>n) e
  "

end
