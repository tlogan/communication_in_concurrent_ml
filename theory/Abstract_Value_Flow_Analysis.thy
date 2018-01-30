theory Abstract_Value_Flow_Analysis
  imports Main Syntax Semantics
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


fun path_balanced' :: "control_path \<Rightarrow> var list \<Rightarrow> bool"  where
 "path_balanced' [] xs = True" |
 "path_balanced' (\<downharpoonleft>y # \<pi>) (x # xs) = ((x = y) \<and> path_balanced' \<pi> xs)" |
 "path_balanced' (\<upharpoonleft>y # \<pi>) xs = path_balanced' \<pi> (y # xs)" |
 "path_balanced' (_ # \<pi>) xs = path_balanced' \<pi> xs"

fun local_path' :: "control_path \<Rightarrow> control_path \<Rightarrow> control_path" where
 "local_path' [] \<pi> = rev \<pi>" |
 "local_path' ((C _) # xs) \<pi> = local_path' xs []" |
 "local_path' (x # xs) \<pi> = local_path' xs (x # \<pi>)"

fun local_path :: "control_path \<Rightarrow> control_path" ("\<plusminus>_" [61]61) where
  "local_path \<pi> = local_path' \<pi> []"


definition path_balanced :: "control_path \<Rightarrow> bool" ("\<downharpoonright>_\<upharpoonleft>" [0]55) where
 "\<downharpoonright>\<pi>\<upharpoonleft> = path_balanced' \<pi> []"

fun linear :: "control_path \<Rightarrow> bool"("``_``" [0]55)  where
 "``[]`` = True" |
 "``((C _ ) # _)`` = False" |
 "``(_ # \<pi>)`` =  ``\<pi>``"



lemma  path_balanced_preserved_over_balanced_extension[simp]: "
  \<downharpoonright>\<pi>\<upharpoonleft> \<Longrightarrow> \<downharpoonright>\<pi>'\<upharpoonleft> \<Longrightarrow> \<downharpoonright>\<pi> @ \<pi>'\<upharpoonleft>
"
sorry

lemma  path_balanced_preserved_over_single_extension[simp]: "
  \<downharpoonright>\<pi>\<upharpoonleft> \<Longrightarrow> \<downharpoonright>\<pi> ;; `x\<upharpoonleft>
"
using path_balanced_def path_balanced_preserved_over_balanced_extension by auto

lemma empty_path_balanced[simp]: "\<downharpoonright>[]\<upharpoonleft>"
by (simp add: path_balanced_def)


lemma  linear_preserved_over_linear_extension[simp]: "
  ``\<pi>`` \<Longrightarrow> ``\<pi>'`` \<Longrightarrow> ``\<pi> @ \<pi>'``
"
sorry

lemma  linear_preserved_over_single_extension[simp]: "
  ``\<pi>`` \<Longrightarrow> ``\<pi> ;; `x``
"
by simp

lemma up_down_balanced[simp]: "
   \<downharpoonright>[\<upharpoonleft>x, \<downharpoonleft>x] \<upharpoonleft>
"
by (simp add: path_balanced_def)

lemma up_down_linear[simp]: "
   ``[\<upharpoonleft>x, \<downharpoonleft>x]``
"
by simp

lemma xyz[simp]: "
   ``[`x]``
"
by simp



inductive traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> (control_path \<times> exp) \<Rightarrow> bool" ("_ \<turnstile> _ \<down> _" [56,0,56]55)  where
  Start: "
    \<V> \<turnstile> e\<^sub>0 \<down> ([], e\<^sub>0)
  " |
  Result: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # \<pi>', RESULT _); 
      \<downharpoonright>\<pi>'\<upharpoonleft>; ``\<pi>'``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = _ in e')
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # (\<pi>';;\<downharpoonleft>x), e')
  " |
  Let_App: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = APP f x\<^sub>a in _);
      ^Abs f' x' e' \<in> \<V> f
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;\<upharpoonleft>x, e')
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in _);
      ^Left x\<^sub>l' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;\<upharpoonleft>x, e\<^sub>l)
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in _);
      ^Right x\<^sub>r' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;\<upharpoonleft>x, e\<^sub>r)
  " |
  Let_Spawn_Child: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SPAWN e\<^sub>c in _)
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;.x, e\<^sub>c)
  " |
  Let_Spawn: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SPAWN _ in e')
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
  " |
  Let_Unit: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = \<lparr>\<rparr> in e')
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
  " |
  Let_Chan: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = CHAN \<lparr>\<rparr> in e')
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
  " |
  Let_Sync: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SYNC _ in e');
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
  " |
  Let_Fst: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = FST _ in e');
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
  " |
  Let_Snd: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = SND _ in e');
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
  " |
  Let_Prim: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = Prim _ in e')
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>;;`x, e')
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
  "|
  Nonempty: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>; ``\<pi>\<^sub>2``;
      \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>\<^sub>1, LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>);
      \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1 @ \<upharpoonleft>x\<^sub>\<kappa> # (\<pi>\<^sub>2 ;; \<downharpoonleft>x\<^sub>\<kappa>), \<kappa>)
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>\<^sub>1 @ \<upharpoonleft>x\<^sub>\<kappa> # \<pi>\<^sub>2, \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>)
  "

lemma stack_traceable_preserved_under_linear[simp]: "
 \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>, \<kappa>) \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi> ;; `x, \<kappa>)
"
sorry

lemma stack_traceable_preserved_under_up_down[simp]: "
 \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi>, \<kappa>) \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<downharpoonleft>\<downharpoonright> (\<pi> @ [\<upharpoonleft>x, \<downharpoonleft>x], \<kappa>)
"
sorry

end