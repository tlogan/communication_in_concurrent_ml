theory Static_Semantics
  imports Main Syntax Dynamic_Semantics
    "~~/src/HOL/Library/List"
begin

datatype abstract_value = AChn var ("^Chan _" [61] 61) | AUnit ("^Unt") | APrim prim ("^_" [61] 61 )

type_synonym abstract_env = "var \<Rightarrow> abstract_value set"

fun rslt_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>Rslt x\<rfloor> = x" |
  "\<lfloor>Let _ _ e\<rfloor> = \<lfloor>e\<rfloor>"


inductive static_eval :: "abstract_env \<times> abstract_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result: "
    static_eval (\<V>, \<C>) (Rslt x)
  " |
  Let_Unit: "
    \<lbrakk>
      {^Unt} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x Unt e)
  " |

  Let_Chan: "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow>  
    static_eval (\<V>, \<C>) (Let x MkChn e)
  " |

  Let_SendEvt : "
    \<lbrakk>
      {^(SendEvt x\<^sub>c x\<^sub>m)} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Prim (SendEvt x\<^sub>c x\<^sub>m)) e)
  " |
  Let_RecvEvt : "
    \<lbrakk>
      {^(RecvEvt x\<^sub>c)} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Prim (RecvEvt x\<^sub>c)) e)
  " |

  Let_Pair : "
    \<lbrakk>
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Prim (Pair x\<^sub>1 x\<^sub>2)) e)
  " |
  Let_Lft : "
    \<lbrakk>
      {^(Lft x\<^sub>p)} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Prim (Lft x\<^sub>p)) e)
  " |
  Let_Rght : "
    \<lbrakk>
      {^(Rght x\<^sub>p)} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Prim (Rght x\<^sub>p)) e)
  " |

  Let_Abs : "
    \<lbrakk>
      {^Abs f' x' e'} \<subseteq> \<V> f';
      static_eval (\<V>, \<C>) e';
      {^Abs f' x' e'} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Prim (Abs f' x' e')) e)
  " |

  Let_Spawn: "
    \<lbrakk>
      {^Unt} \<subseteq> \<V> x;
      static_eval (\<V>, \<C>) e\<^sub>c;
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow>  
    static_eval (\<V>, \<C>) (Let x (Spwn e\<^sub>c) e)
  " |

  Let_Sync  : "
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
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow>  
    static_eval (\<V>, \<C>) (Let x (Sync x\<^sub>e) e)
  " |

  Let_Fst: "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      static_eval (\<V>, \<C>) e 
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Fst x\<^sub>p) e)
  " |
  Let_Snd: "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Snd x\<^sub>p) e)
  " |
  Let_Case: "
    \<lbrakk>
      \<forall> x\<^sub>l' . ^(Lft x\<^sub>l') \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x
      ; 
      static_eval (\<V>, \<C>) e\<^sub>l ;
      \<forall> x\<^sub>r' . ^(Rght x\<^sub>r') \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x
      ;
      static_eval (\<V>, \<C>) e\<^sub>r;
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e)
  " |
  let_app: "
    \<lbrakk>
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      static_eval (\<V>, \<C>) e
    \<rbrakk> \<Longrightarrow> 
    static_eval (\<V>, \<C>) (Let x (App f x\<^sub>a) e)
  "

inductive static_reachable :: "exp \<Rightarrow> exp \<Rightarrow> bool"  where
  Refl : "
    static_reachable e e
  " | 
  Let_Spawn_Child: "
    static_reachable e\<^sub>c e \<Longrightarrow>
    static_reachable (Let x (Spwn e\<^sub>c) e\<^sub>n) e
  " |
  let_case_left: "
    static_reachable e\<^sub>l e \<Longrightarrow>
    static_reachable (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e
  " |
  let_case_right: "
    static_reachable e\<^sub>r e \<Longrightarrow>
    static_reachable (Let x (Case x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r) e\<^sub>n) e
  " |
  Let_Abs_Body: "
    static_reachable e\<^sub>b e \<Longrightarrow>
    static_reachable (Let x (Prim (Abs f x\<^sub>p e\<^sub>b)) e\<^sub>n) e
  " | 
  Let: "
    static_reachable e\<^sub>n e \<Longrightarrow>
    static_reachable (Let x b e\<^sub>n) e
  "

end