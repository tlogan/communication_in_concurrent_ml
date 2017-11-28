theory Analysis
  imports Main Syntax Semantics
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^ _" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"

fun result_var :: "exp \<Rightarrow> var" where
  "result_var (RESULT x) = x" |
  "result_var (LET _ = _ in e) = result_var e"

inductive abstract_value_flow :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
  Result: "
    (\<V>, \<C>) \<Turnstile> RESULT x
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
      \<And> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<Longrightarrow> 
        \<rho> x\<^sub>l' \<subseteq> \<rho> x\<^sub>l \<and> \<V> (result_var e\<^sub>l) \<subseteq> \<rho> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>l
      ;
      \<And> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<Longrightarrow>
        \<rho> x\<^sub>r' \<subseteq> \<rho> x\<^sub>r \<and> \<rho> (result_var e\<^sub>r) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>r
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk> 
      \<And> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<Longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      \<And> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<Longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      \<And> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<Longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (result_var e') \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk>
      \<And> x\<^sub>c x\<^sub>m . ^Send_Evt x\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>e \<Longrightarrow> 
        {^\<lparr>\<rparr>} \<subseteq> \<V> x \<and> \<V> x_m \<subseteq> \<C> x\<^sub>c
      ;
      \<And> x\<^sub>c . ^Recv_Evt x\<^sub>c \<in> \<V> x\<^sub>e \<Longrightarrow>
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

fun absval :: "val \<Rightarrow> abstract_value" where
  "absval \<lbrace>Ch \<pi> x\<rbrace> = ^Chan x" |
  "absval \<lbrace>p, \<rho>\<rbrace> = ^p" |
  "absval \<lbrace>\<rbrace> = ^\<lparr>\<rparr>"

definition absval_env :: "(var \<rightharpoonup> val) \<Rightarrow> var \<Rightarrow> abstract_value set" where
  "absval_env \<rho> x = (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {absval \<omega>} |
    None \<Rightarrow> {}
  )"


definition abstract_more_precise :: "abstract_value_env \<Rightarrow> abstract_value_env \<Rightarrow> prop" (infix "\<sqsubseteq>" 55) where
  "abstract_more_precise \<V> \<V>' \<equiv> (\<And> x . \<V> x \<subseteq> \<V>' x)"

inductive abstract_value_flow_value :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<parallel>>" 55)
and  abstract_value_flow_env :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> (var \<rightharpoonup> val) \<Rightarrow> bool" (infix "\<parallel>\<approx>" 55) 
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
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |
  Left: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Left _, \<rho>\<rbrace>
  " |
  Right: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Right _, \<rho>\<rbrace>
  " |
  Send_Evt: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |
  Recv_Evt: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |
  Always_Evt: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>> \<lbrace>Always_Evt _, \<rho>\<rbrace>
  " |

  Empty: "(\<V>, \<C>) \<parallel>\<approx> empty" |
  Nonempty: "
    \<lbrakk>
      {absval \<omega>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<parallel>> \<omega>;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>\<approx> \<rho>(x \<mapsto> \<omega>)
  "

inductive abstract_value_flow_stack :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile> _ \<Rrightarrow> _" [56, 0, 56] 56) where
  Empty: "(\<V>, \<C>) \<Turnstile> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e;
      (\<V>, \<C>) \<parallel>\<approx> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (result_var e) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> \<W> \<Rrightarrow> \<langle>x, e, \<rho>\<rangle> # \<kappa>
  "

inductive abstract_value_flow_state :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e; 
      (\<V>, \<C>) \<parallel>\<approx> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (result_var e) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<TTurnstile> (e, \<rho>, \<kappa>)
  "

inductive abstract_value_flow_pool :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<parallel>\<lless>" 55) where
  Empty: "(\<V>, \<C>) \<parallel>\<lless> empty" |
  Nonempty: "
    \<lbrakk>
      (\<V>, \<C>) \<TTurnstile> \<sigma>;
      (\<V>, \<C>) \<parallel>\<lless> \<E>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<parallel>\<lless> \<E>(\<pi> \<mapsto> \<sigma>)
  "

theorem abstract_value_flow_preservation : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>; 
    \<E> \<rightarrow> \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<parallel>\<lless> \<E>'
"
sorry

theorem abstract_value_flow_preservation_star : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>; 
    \<E> \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  (\<V>, \<C>) \<parallel>\<lless> \<E>'
"
sorry


theorem abstract_value_flow_precision : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless>  \<E>  (* or should it be (\<V>, \<C>) \<parallel>\<approx> \<rho> *);
    \<E> \<pi> = Some (e, \<rho>, \<kappa>)
  \<rbrakk>
  \<Longrightarrow>
  absval_env \<rho> \<sqsubseteq> \<V>
"
 sorry

theorem lift_flow: "(\<V>, \<C>) \<Turnstile> e \<Longrightarrow> (\<V>, \<C>) \<parallel>\<lless> [[] \<mapsto> (e, empty, [])]"
 apply rule
  apply rule
    apply auto
   apply (rule, rule, rule)
done

theorem abstract_value_flow_pool_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<parallel>\<lless> \<E>; 
    \<E> \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (e', \<rho>', \<kappa>')
  \<rbrakk> \<Longrightarrow>
  absval_env \<rho>' \<sqsubseteq> \<V>
"
 apply (drule abstract_value_flow_preservation_star [of \<V> \<C> _ \<E>'])
  apply auto
 thm abstract_value_flow_precision
 apply (erule abstract_value_flow_precision [of \<V> \<C> \<E>' \<pi> e' \<rho>' \<kappa>'])
 apply auto
done


theorem abstract_value_flow_sound : "
  \<lbrakk>
    (\<V>, \<C>) \<Turnstile> e; 
    [[] \<mapsto> (e, empty, [])] \<rightarrow>* \<E>';
    \<E>' \<pi> = Some (e', \<rho>', \<kappa>')
  \<rbrakk> \<Longrightarrow>
  absval_env \<rho>' \<sqsubseteq> \<V>
"
 thm lift_flow
 apply (drule lift_flow)
 thm abstract_value_flow_pool_sound
 apply (erule abstract_value_flow_pool_sound [of \<V> \<C> _ \<E>' \<pi> e' \<rho>' \<kappa>'])
 apply auto
done


type_synonym abstract_path = "(var + unit) list"


inductive path_in_exp' :: "abstract_value_env \<Rightarrow> abstract_path \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "path_in_exp' \<rho> [Inl x] (RESULT x)" |
  Let_Unit: "
    path_in_exp' \<V> \<pi> e \<Longrightarrow> 
    path_in_exp' \<V> (Inl x # \<pi>) (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Prim: "
    path_in_exp' \<V> \<pi> e \<Longrightarrow> 
    path_in_exp' \<V> (Inl x # \<pi>) (LET x = Prim p in e)
  " |
  Let_Case_Left: "
    \<lbrakk>
      path_in_exp' \<V> \<pi>\<^sub>l e\<^sub>l; 
      path_in_exp' \<V> \<pi> e 
    \<rbrakk>\<Longrightarrow> 
    path_in_exp' \<V> (\<pi>\<^sub>l @ (Inl x # \<pi>)) (LET x = CASE _ LEFT x\<^sub>l |> e\<^sub>l RIGHT _ |> _ in e)
  " |
  Let_Case_Right: "
    \<lbrakk>
      path_in_exp' \<V> \<pi>\<^sub>r e\<^sub>r;
      path_in_exp' \<V> \<pi> e
    \<rbrakk> \<Longrightarrow> 
    path_in_exp' \<V> (\<pi>\<^sub>r @ (Inl x # \<pi>)) (LET x = CASE _ LEFT _ |> _ RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_Fst: "
    path_in_exp' \<V> \<pi> e \<Longrightarrow> 
    path_in_exp' \<V> (Inl x # \<pi>) (LET x = FST _ in e)
  " |
  Let_Snd: "
    path_in_exp' \<V> \<pi> e \<Longrightarrow> 
    path_in_exp' \<V> (Inl x # \<pi>) (LET x = SND _ in e)
  " |
  Let_App: "
    \<lbrakk>
      ^Abs f' x' e' \<in> \<V> f;
      path_in_exp' (\<V>(x' := \<V> x' \<inter> \<V> x\<^sub>a)) \<pi>' e';
      path_in_exp' \<V> \<pi> e
    \<rbrakk> \<Longrightarrow> 
    path_in_exp' \<V> (\<pi>' @ (Inl x # \<pi>)) (LET x = APP f x\<^sub>a in e)
  " |
  Let_Sync: "
   path_in_exp' \<V> \<pi> e \<Longrightarrow>
   path_in_exp' \<V> (Inl x # \<pi>) (LET x = SYNC _ in e)
  " |
  Let_Chan: "
    path_in_exp' \<V> \<pi> e \<Longrightarrow>
    path_in_exp' \<V> (Inl x # \<pi>) (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    path_in_exp' \<V> \<pi> e \<Longrightarrow>
    path_in_exp' \<V> (Inl x # \<pi>) (LET x = SPAWN _ in e)
  " |
  Let_Spawn_Child: " 
    path_in_exp' \<V> \<pi> e\<^sub>c \<Longrightarrow>
    path_in_exp' \<V> (Inr () # \<pi>) (LET x = SPAWN e\<^sub>c in _)
  " 


definition path_in_exp :: "abstract_path \<Rightarrow> exp \<Rightarrow> bool" where
  "path_in_exp \<pi> e \<equiv> (\<exists> \<V> \<C> . (\<V>, \<C>) \<Turnstile> e \<and> path_in_exp' \<V> \<pi> e)"

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" where
  Refl: "subexp e e" |
  Step: "subexp e' e \<Longrightarrow> subexp e' (LET _ = _ in e)"

definition send_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "send_sites c e = {x . \<exists> y e' z \<V> \<C>. 
    subexp (LET x = SYNC y in e') e \<and> 
    (\<V>, \<C>) \<Turnstile> e \<and> 
    ^Send_Evt c z \<in> \<V> y
  }"

definition recv_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "recv_sites c e = {x . \<exists> y e' \<V> \<C>. 
    subexp (LET x = SYNC y in e') e \<and> 
    (\<V>, \<C>) \<Turnstile> e \<and> 
    ^Recv_Evt c \<in> \<V> y
  }"


definition paths :: "var set \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "paths sites e = {path @ [Inl x] | path x . 
    (x \<in> sites) \<and>  path_in_exp (path @ [Inl x]) e
  }" 

definition processes :: "var set \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "processes sites e = {\<pi> \<in> paths sites e .
    (\<exists> \<pi>' . (\<pi> @ [Inr ()] @ \<pi>') \<in> paths sites e) \<or>
    (\<forall> \<pi>' . (\<pi> @ \<pi>') \<notin> paths sites e)
  }" 

definition send_paths where 
  "send_paths c e = paths (send_sites c e) e"

definition recv_paths where 
  "recv_paths c e = paths (recv_sites c e) e"

definition send_processes where 
  "send_processes c e = processes (send_sites c e) e"

definition recv_processes where 
  "recv_processes c e = processes (recv_sites c e) e"

definition one_max :: "abstract_path set \<Rightarrow> bool"  where
  "one_max \<T> \<equiv>  (\<nexists> p . p \<in> \<T>) \<or> (\<exists>! p . p \<in> \<T>)" 


datatype topo_class = OneShot | OneToOne | FanOut | FanIn | Any

type_synonym topo_class_pair = "var \<times> topo_class"

inductive communication_topology' :: "topo_class_pair \<Rightarrow> exp \<Rightarrow> bool" where
  OneShot: "
    one_max (send_paths c e) \<Longrightarrow> 
    communication_topology' (c, OneShot) e
  " | 
  OneToOne: "
    \<lbrakk> 
      one_max (send_processes c e) ;
      one_max (recv_processes c e) 
    \<rbrakk> \<Longrightarrow> 
    communication_topology' (c, OneToOne) e
  " | 

  FanOut: "
    one_max (send_processes c e) \<Longrightarrow> 
    communication_topology' (c, FanOut) e
  " | 

  FanIn: "
    one_max (recv_processes c e) \<Longrightarrow> 
    communication_topology' (c, OneToOne) e
  " | 

  Any: "communication_topology' (c, OneToOne) e"


type_synonym topo_class_env = "var \<Rightarrow> topo_class"

definition communication_topology :: "topo_class_env \<Rightarrow> exp \<Rightarrow> prop" where 
  "communication_topology \<A> e \<equiv> (\<And> x . communication_topology' (x, \<A> x) e)"



inductive precision_order :: "topo_class \<Rightarrow> topo_class \<Rightarrow> bool" (infix "\<preceq>" 55) where  
  Edge1 : "OneShot \<preceq> OneToOne" | 
  Edge2 : "OneToOne \<preceq> FanOut" |
  Edge3 : "OneToOne \<preceq> FanIn" |
  Edge4 : "FanOut \<preceq> Any" |
  Edge5 : "FanIn \<preceq> Any" |
  Refl : "t \<preceq> t" |
  Trans : "\<lbrakk> a \<preceq> b ; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c"

end
