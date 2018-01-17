theory Abstract_Value_Flow_Analysis
  imports Main Syntax Semantics
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^_" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"
type_synonym bind_env = "var \<Rightarrow> bind set" 

type_synonym site_set = "((var + var) \<times> (var + var) option) set"
datatype site_env = Site_Env site_set "((var + var) option) set" ("_ . _" [61,61] 61)


fun result_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>RESULT x\<rfloor> = x" |
  "\<lfloor>LET _ = _ in e\<rfloor> = \<lfloor>e\<rfloor>"


fun site_set :: "((var + var) option) set \<Rightarrow> exp \<Rightarrow> ((var + var) option) set"("\<lceil>_ | _\<rceil>" [0,0]61) where
  "\<lceil>\<Z> | RESULT _\<rceil> = \<Z>" |
  "\<lceil>_ | LET x = SPAWN _ in _\<rceil> = {Some (Inl x), Some (Inr x)}" |
  "\<lceil>_ | LET x = _ in e\<rceil> = {Some (Inl x)}"


fun path_exists' :: "site_set \<Rightarrow> control_path \<Rightarrow> bool" where
  "path_exists' \<Y> [] = True" |
  "path_exists' \<Y> [y] = ((\<nexists> x . (x, Some y) \<in> \<Y>) \<and> (\<exists> z . (y, z) \<in> \<Y>))" |
  "path_exists' \<Y> (z # y # \<pi>) = ((y, Some z) \<in> \<Y> \<and> path_exists' \<Y> (y # \<pi>))"

fun path_exists where
  "path_exists \<Y> \<pi> = path_exists' \<Y> (rev \<pi>)"


inductive accept_exp :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<times> site_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk> 
      {\<lparr>\<rparr>} \<subseteq> \<X> x;
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk>
      {FN f' x' . e' } \<subseteq> \<X> f';
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e';
      {FN f' x' . e' } \<subseteq> \<X> x;
      {^Abs f' x' e'} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk> 
      {\<lparr>x\<^sub>1, x\<^sub>2\<rparr>} \<subseteq> \<X> x;
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk> 
      {LEFT x\<^sub>p} \<subseteq> \<X> x;
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk>
      {RIGHT x\<^sub>p} \<subseteq> \<X> x;
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = RIGHT x\<^sub>p in e
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      {SEND EVT x\<^sub>c x\<^sub>m} \<subseteq> \<X> x;
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      {RECV EVT x\<^sub>c} \<subseteq> \<X> x;
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      {CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r} \<subseteq> \<X> x;
      \<forall> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> 
        (\<forall> z \<in> \<lceil>\<Z> | e\<^sub>l\<rceil> . (Inl x, z) \<in> \<Y>) \<and>
        (\<V>, \<C>, \<X>, \<Y> . \<lceil>\<Z> | e\<rceil>) \<Turnstile>\<^sub>e e\<^sub>l
      ;
      \<forall> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> 
        (\<forall> z \<in> \<lceil>\<Z> | e\<^sub>r\<rceil> . (Inl x, z) \<in> \<Y>) \<and>
        (\<V>, \<C>, \<X>, \<Y> . \<lceil>\<Z> | e\<rceil>) \<Turnstile>\<^sub>e e\<^sub>r
      ;
      
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk> 
      {FST x\<^sub>p} \<subseteq> \<X> x;
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      {SND x\<^sub>p} \<subseteq> \<X> x;
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      {APP f x\<^sub>a} \<subseteq> \<X> x;
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and> \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x \<and>
        (\<forall> z \<in> \<lceil>\<Z> | e'\<rceil> . (Inl x, z) \<in> \<Y>) \<and> 
        (\<V>, \<C>, \<X>, \<Y> . \<lceil>\<Z> | e\<rceil>) \<Turnstile>\<^sub>e e'
      ;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk>
      {SYNC x\<^sub>e} \<subseteq> \<X> x;
      \<forall> x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c . 
        ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>e \<longrightarrow> 
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow>
        {^\<lparr>\<rparr>} \<subseteq> \<V> x \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
      ;
      \<forall> x\<^sub>r\<^sub>c x\<^sub>c . 
        ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>e \<longrightarrow>
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow>
        \<C> x\<^sub>c \<subseteq> \<V> x
      ;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      {CHAN \<lparr>\<rparr>} \<subseteq> \<X> x;
      {^Chan x} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn: "
    \<lbrakk>
      {SPAWN e\<^sub>c} \<subseteq> \<X> x;
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      \<forall> z \<in> \<lceil>{None} | e\<^sub>c\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e\<^sub>c;
      \<forall> z \<in> \<lceil>\<Z> | e\<rceil> . (Inl x, z) \<in> \<Y>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e
  "


fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|\<lbrace>Ch \<pi> x\<rbrace>| = ^Chan x" |
  "|\<lbrace>p, \<rho>\<rbrace>| = ^p" |
  "|\<lbrace>\<rbrace>| = ^\<lparr>\<rparr>"

definition env_to_abstract_value_env :: "(var \<rightharpoonup> val) \<Rightarrow> abstract_value_env" ("\<parallel>_\<parallel>" [0]61) where
  "\<parallel>\<rho>\<parallel>= (\<lambda> x . (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {|\<omega>|} |
    None \<Rightarrow> {}
  ))"


definition abstract_value_env_precision :: "abstract_value_env \<Rightarrow> abstract_value_env \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "\<V> \<sqsubseteq> \<V>' \<equiv> (\<forall> x . \<V> x \<subseteq> \<V>' x)"


inductive accept_value :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<times> site_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  accept_val_env :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<times> site_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "(\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" |
  Chan: "(\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>c\<rbrace>" |
  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |
  Pair: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |
  Always_Evt: "
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive accept_stack :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<times> site_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive accept_state :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<times> site_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive accept_state_pool :: "abstract_value_env \<times> abstract_value_env \<times> bind_env \<times> site_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>, \<X>, \<Y> . \<Z>) \<Turnstile>\<^sub>\<E> \<E>
  "
   
end