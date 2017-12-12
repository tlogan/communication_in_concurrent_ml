theory Abstract_Value_Flow_Analysis
  imports Main Syntax Semantics
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^_" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"

fun result_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>RESULT x\<rfloor> = x" |
  "\<lfloor>LET _ = _ in e\<rfloor> = \<lfloor>e\<rfloor>"


class flow =
  fixes accept :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Turnstile>" 55)

instantiation exp :: flow
begin

inductive accept_exp where
  "
    (\<V>, \<C>) \<Turnstile> (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk> {^\<lparr>\<rparr>} \<subseteq> \<V> x; (\<V>, \<C>) \<Turnstile> e \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk> 
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>) \<Turnstile> e';
      {^Abs f' x' e'} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk> 
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk> 
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk> 
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = RIGHT x\<^sub>p in e
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      \<forall> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow> 
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>l
      ;
      \<forall> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>r
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk> 
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = APP f x\<^sub>a in e
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
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn_Parent: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e\<^sub>c;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = SPAWN e\<^sub>c in e
  "

instance proof
qed

end


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


inductive flow_over_value_accept :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<parallel>>" 55)
and  flow_over_env_accept :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> env \<Rightarrow> bool" (infix "\<parallel>\<approx>" 55) 
where
  Unit: "(\<V>, \<C>) \<parallel>> \<lbrace>\<rbrace>" |
  Chan: "(\<V>, \<C>) \<parallel>> \<lbrace>c\<rbrace>" |
  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<parallel>> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |
  Pair: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |
  Always_Evt: "
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x \<rhd> \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<parallel>> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>\<approx> \<rho>
  "

instantiation val :: flow
begin
fun accept_val where "(\<V>, \<C>) \<Turnstile> \<omega> \<longleftrightarrow> (\<V>, \<C>) \<parallel>> \<omega> "
instance proof
qed
end

instantiation env :: flow
begin
fun accept_env where "(\<V>, \<C>) \<Turnstile> \<omega> \<longleftrightarrow> (\<V>, \<C>) \<parallel>\<approx> \<omega> "
instance proof
qed
end


datatype abstract_stack_bind = ASB "abstract_value set" "cont_stack" (infix "\<Rrightarrow>" 70)
instantiation abstract_stack_bind :: flow
begin
inductive accept_abstract_stack_bind where
  Empty: "(\<V>, \<C>) \<Turnstile> \<W> \<Rrightarrow> [.]" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<Turnstile> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> :# \<kappa>)
  "
instance proof
qed
end

instantiation state :: flow
begin
inductive accept_state where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e; 
      (\<V>, \<C>) \<Turnstile> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile> \<langle>e; \<rho>; \<kappa>\<rangle>
  "
instance proof
qed
end

instantiation state_pool :: flow
begin
inductive accept_state_pool where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> \<diamond> \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> \<E>
  "
instance proof
qed
end

end