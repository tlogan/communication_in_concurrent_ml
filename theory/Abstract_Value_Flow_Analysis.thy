theory Abstract_Value_Flow_Analysis
  imports Main Syntax Semantics
    "~~/src/HOL/Library/List"
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^_" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"
type_synonym bind_env = "var \<Rightarrow> bind set" 
fun result_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>RESULT x\<rfloor> = x" |
  "\<lfloor>LET _ = _ in e\<rfloor> = \<lfloor>e\<rfloor>"


inductive accept_exp :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result: "
    (\<V>, \<C>) \<Turnstile>\<^sub>e (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk>
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>) \<Turnstile>\<^sub>e e';
      {^Abs f' x' e'} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk>
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk>
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk>
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = RIGHT x\<^sub>p in e
  " |
  Let_Send_Evt : "
    \<lbrakk>
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk>
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      \<forall> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l
      ;
      \<forall> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r
      ;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk>
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
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e
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

inductive accept_value :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  accept_val_env :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>" |
  Chan: "(\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>c\<rbrace>" |
  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |
  Pair: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " (*|
  Always_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " *)|

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive accept_stack :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive accept_state :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive accept_state_pool :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
  "
   
definition abstract_value_env_precision :: "abstract_value_env \<Rightarrow> abstract_value_env \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "\<V> \<sqsubseteq> \<V>' \<equiv> (\<forall> x . \<V> x \<subseteq> \<V>' x)"


inductive traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> (control_path \<times> exp) \<Rightarrow> bool" ("_ \<turnstile> _ \<down> _" [56,0,56]55)  where
  Start: "
    \<V> \<turnstile> e\<^sub>0 \<down> ([], e\<^sub>0)
  " |
  Result_Case_Left: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>\<bar>x # \<pi>', RESULT x\<^sub>r); 
      \<downharpoonright>\<pi>'\<upharpoonleft>; ``\<pi>'``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n) 
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>\<bar>x # (\<pi>';;\<downharpoonleft>x), e\<^sub>n)
  " |
  Result_Case_Right: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>:x # \<pi>', RESULT x\<^sub>r); 
      \<downharpoonright>\<pi>'\<upharpoonleft>; ``\<pi>'``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n) 
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>:x # (\<pi>';;\<downharpoonleft>x), e\<^sub>n)
  " |
  Result_App: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # \<pi>', RESULT x\<^sub>r); 
      \<downharpoonright>\<pi>'\<upharpoonleft>; ``\<pi>'``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n) 
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # (\<pi>';;\<downharpoonleft>x), e\<^sub>n)
  " |
  Let_App: " 
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = APP f x\<^sub>a in e\<^sub>n);
      ^Abs f' x' e' \<in> \<V> f
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;\<upharpoonleft>x, e')
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n);
      ^Left x\<^sub>l' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;\<upharpoonleft>x, e\<^sub>l)
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n);
      ^Right x\<^sub>r' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;\<upharpoonleft>x, e\<^sub>r)
  " |
  Let_Spawn_Child: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SPAWN e\<^sub>c in e\<^sub>n)
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;.x, e\<^sub>c)
  " |
  Let_Spawn: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SPAWN e\<^sub>c in e\<^sub>n)
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  " |
  Let_Unit: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = \<lparr>\<rparr> in e\<^sub>n)
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  " |
  Let_Chan: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = CHAN \<lparr>\<rparr> in e\<^sub>n)
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  " |
  Let_Sync: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SYNC x\<^sub>v in e\<^sub>n);
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  " |
  Let_Fst: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = FST p in e\<^sub>n);
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  " |
  Let_Snd: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SND p in e\<^sub>n);
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  " |
  Let_Prim: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = Prim p in e\<^sub>n)
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e\<^sub>n)
  "

inductive stack_traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> (control_path \<times> cont list) \<Rightarrow> bool" ("_ \<tturnstile> _ \<downharpoonleft>\<downharpoonright> _" [56,0,56]55)  where
  Empty: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<upharpoonleft>; ``\<pi>``
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e \<downharpoonleft>\<downharpoonright> (\<pi>, [])
  " |
  Empty_Local: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>; ``\<pi>\<^sub>2``
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1 @ .x # \<pi>\<^sub>2, [])
  " |
  Nonempty_App: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>; ``\<pi>\<^sub>2``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>\<^sub>1, LET x\<^sub>\<kappa> = APP f x\<^sub>a in e\<^sub>\<kappa>);
      \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1, \<kappa>)
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1 @ \<upharpoonleft>x\<^sub>\<kappa> # \<pi>\<^sub>2, \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)
  " |
  Nonempty_Case_Left: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>; ``\<pi>\<^sub>2``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>\<^sub>1, LET x\<^sub>\<kappa> = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>\<kappa>);
      \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1, \<kappa>)
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1 @ \<upharpoonleft>\<bar>x\<^sub>\<kappa> # \<pi>\<^sub>2, \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)
  " |
  Nonempty_Case_Right: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>; ``\<pi>\<^sub>2``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>\<^sub>1, LET x\<^sub>\<kappa> = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>\<kappa>);
      \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1, \<kappa>)
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1 @ \<upharpoonleft>:x\<^sub>\<kappa> # \<pi>\<^sub>2, \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)
  " 


lemma stack_traceable_preserved_over_linear_balanced_extension: "
 \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>, \<kappa>) \<Longrightarrow> \<downharpoonright>\<pi>'\<upharpoonleft> \<Longrightarrow> ``\<pi>'`` \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi> @ \<pi>', \<kappa>)
"
apply (erule stack_traceable.cases; auto)
   apply (simp add: stack_traceable.Empty)
  apply (simp add: Empty_Local)
 apply (simp add: stack_traceable.Nonempty_App)
 apply (simp add: stack_traceable.Nonempty_Case_Left)
 apply (simp add: stack_traceable.Nonempty_Case_Right)
done

lemma stack_traceable_preserved_over_seq_extension:"
  \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>, \<kappa>) \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi> ;; `x, \<kappa>)
"
by (simp add: Seq_Cons linear.Empty stack_traceable_preserved_over_linear_balanced_extension)


inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" ("_ \<preceq>\<^sub>e _" [56,56]55) where
  Refl : "
    e \<preceq>\<^sub>e e
  " |
  Let_Abs_Body: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>b 
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)
  " | 
  Let: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = b in e\<^sub>n)
  " | 
  Let_Spawn_Child: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>c
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = SPAWN e\<^sub>c in e\<^sub>n)
  " |
  Let_Case_Left: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>l
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " | 
  Let_Case_Right: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>r
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  "

lemma subexp_trans': "
  e\<^sub>y \<preceq>\<^sub>e e\<^sub>z \<Longrightarrow> (\<forall> e\<^sub>x . e\<^sub>x \<preceq>\<^sub>e e\<^sub>y \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>z)
"
  apply (erule subexp.induct; auto)
   apply (drule spec; auto, rule subexp.Let_Abs_Body, assumption)
   apply (drule spec; auto, rule subexp.Let, assumption)
   apply (drule spec; auto, rule subexp.Let_Spawn_Child, assumption)
   apply (drule spec; auto, rule subexp.Let_Case_Left, assumption)
   apply (drule spec; auto, rule subexp.Let_Case_Right, assumption)
done

lemma subexp_trans: "
  e\<^sub>x \<preceq>\<^sub>e e\<^sub>y \<Longrightarrow> e\<^sub>y \<preceq>\<^sub>e e\<^sub>z \<Longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>z
"
using subexp_trans' by blast

lemma subexp1: "
  e\<^sub>n \<preceq>\<^sub>e LET x = b in e\<^sub>n
"
by (simp add: Let Refl)

lemma traceable_implies_subexp': "
  \<V> \<turnstile> e\<^sub>0 \<down> p \<Longrightarrow>
  (\<forall> \<pi> e .
    p = (\<pi>, e) \<longrightarrow>
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0)) \<longrightarrow>
    e \<preceq>\<^sub>e e\<^sub>0
  )
"
 apply (erule traceable.induct; auto)
            apply (rule subexp.Refl)
            apply (rotate_tac -1, rule subexp_trans; auto?; rule subexp1)+
           apply (drule_tac x = f in spec)
           apply (drule_tac x = "\<lbrace> Abs f' x' e' , _\<rbrace>" in spec)
           apply (erule impE; simp)
           apply (blast intro:  Let_Abs_Body Refl subexp_trans)
          apply (rule subexp_trans; auto?; rule subexp.Let_Case_Left; rule subexp.Refl)
         apply (rule subexp_trans; auto?; rule subexp.Let_Case_Right; rule subexp.Refl)
       apply (rule subexp_trans; auto?; rule subexp.Let_Spawn_Child; rule subexp.Refl)
      apply (rule subexp_trans; auto?; rule subexp1)+
done

theorem traceable_implies_subexp: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e);
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0))
  \<rbrakk> \<Longrightarrow>
  e \<preceq>\<^sub>e e\<^sub>0
"
by (simp add: traceable_implies_subexp')

inductive abstract_step :: "abstract_value_env \<times> exp \<Rightarrow> exp \<Rightarrow> control_label \<Rightarrow> exp \<Rightarrow> bool" ("_ \<turnstile> _ \<midarrow>_\<rightarrow> _" [56,0,0,56]55)  where
  Let_Spawn_Child: "
    \<lbrakk>
      (LET x = SPAWN e\<^sub>c in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = SPAWN e\<^sub>c in e) \<midarrow>.x\<rightarrow> e\<^sub>c
  " |
  Let_Spawn: "
    \<lbrakk>
      (LET x = SPAWN e\<^sub>c in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = SPAWN e\<^sub>c in e) \<midarrow>`x\<rightarrow> e
  " |
  Let_Unit: "
    \<lbrakk>
      (LET x = \<lparr>\<rparr> in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = \<lparr>\<rparr> in e) \<midarrow>`x\<rightarrow> e
  " |
  Let_Chan: "
    \<lbrakk>
      (LET x = CHAN \<lparr>\<rparr> in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = CHAN \<lparr>\<rparr> in e) \<midarrow>`x\<rightarrow> e
  " |
  Let_Sync: "
    \<lbrakk>
      (LET x = SYNC x\<^sub>v in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = SYNC p in e) \<midarrow>`x\<rightarrow> e
  " |
  Let_Fst: "
    \<lbrakk>
      (LET x = FST x\<^sub>p in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = FST p in e) \<midarrow>`x\<rightarrow> e
  " |
  Let_Snd: "
    \<lbrakk>
      (LET x = SND x\<^sub>p in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = SND p in e) \<midarrow>`x\<rightarrow> e
  " |
  Let_Prim: "
    \<lbrakk>
      (LET x = Prim p in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = Prim p in e) \<midarrow>`x\<rightarrow> e
  " |
  App: "
    \<lbrakk>
      ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f; 
      (LET x = APP f x\<^sub>a in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = APP f x\<^sub>a in e) \<midarrow>\<upharpoonleft>x\<rightarrow> e\<^sub>b
  " |
  Case_Left: "
    \<lbrakk>
      (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) \<midarrow>\<upharpoonleft>x\<rightarrow> e\<^sub>l
  " |
  Case_Right: "
    \<lbrakk>
      (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) \<midarrow>\<upharpoonleft>x\<rightarrow> e\<^sub>r
  " |
  Result_App: "
    \<lbrakk>
      ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f; 
      (LET x = APP f x\<^sub>a in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (RESULT \<lfloor>e\<^sub>b\<rfloor>) \<midarrow>\<downharpoonleft>x\<rightarrow> e
  " |
  Result_Case_Left: "
    \<lbrakk>
      (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (RESULT \<lfloor>e\<^sub>l\<rfloor>) \<midarrow>\<downharpoonleft>x\<rightarrow> e
  " |
  Result_Case_Right: "
    \<lbrakk>
      (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e) \<preceq>\<^sub>e e\<^sub>0
    \<rbrakk> \<Longrightarrow>
    (\<V>, e\<^sub>0) \<turnstile> (RESULT \<lfloor>e\<^sub>r\<rfloor>) \<midarrow>\<downharpoonleft>x\<rightarrow> e
  " 
(*
lemma traceable_functional: "
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e\<^sub>1) \<Longrightarrow>
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e\<^sub>2) \<Longrightarrow>
  e\<^sub>1 = e\<^sub>2
"
(* this could be true if CASE steps created distinct control_labels for left and right *)
sorry
*)

theorem traceable_implies_abstract_step: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # \<pi>', RESULT y); 
    \<downharpoonright>\<pi>'\<upharpoonleft>; ``\<pi>'``;
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n);

    (* y = \<lfloor>e\<^sub>b\<rfloor>; more precise, but needs change in traceable definition *)
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0))
  \<rbrakk> \<Longrightarrow>
  (\<V>, e\<^sub>0) \<turnstile> RESULT y \<midarrow>\<downharpoonleft>x\<rightarrow> e\<^sub>b  
  (* 
    This is used to concretize the b as APP or CASE.
    Is this necessary, or could traceable itself be used to concretize the b as APP or CASE?
  *)
"
sorry

(*

theorem traceable_result_implies_subexp: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # \<pi>', RESULT y); 
    \<downharpoonright>\<pi>'\<upharpoonleft>; ``\<pi>'``;
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n);

    y = \<lfloor>e\<^sub>b\<rfloor>; (* more precise, but needs change in traceable definition *)
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0))
  \<rbrakk> \<Longrightarrow>
  (
    (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>b RIGHT x\<^sub>r |> e\<^sub>r in e) \<preceq>\<^sub>e e\<^sub>0 \<or>
    (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>b in e) \<preceq>\<^sub>e e\<^sub>0 \<or>
    (^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<and> (LET x = APP f x\<^sub>a in e) \<preceq>\<^sub>e e\<^sub>0)
  )
"
sorry

*)

end