theory Communication_Topology_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin

  

datatype topo = OneShot | OneToOne | FanOut | FanIn | Any

definition send_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_sites \<E> ch = {\<pi>. \<exists> x x\<^sub>e e \<kappa> \<rho> x\<^sub>c x\<^sub>m \<rho>\<^sub>e. 
    \<E> \<pi> = Some (<<LET x = SYNC x\<^sub>e in e, \<rho>, \<kappa>>>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>c = Some \<lbrace>ch\<rbrace>
  }"

definition recv_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_sites \<E> ch = {\<pi>. \<exists> x x\<^sub>e e \<kappa> \<rho> x\<^sub>c \<rho>\<^sub>e. 
    \<E> \<pi> = Some (<<LET x = SYNC x\<^sub>e in e, \<rho>, \<kappa>>>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>c, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>c = Some \<lbrace>ch\<rbrace>
  }"

definition single_side :: "(state_pool \<Rightarrow> chan \<Rightarrow> control_path set) \<Rightarrow> state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "single_side sites_of \<E> c \<longleftrightarrow> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    \<pi>\<^sub>1 \<in> sites_of \<E> c \<longrightarrow>
    \<pi>\<^sub>2 \<in> sites_of \<E> c \<longrightarrow>
    (prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1) 
  )"

definition one_shot :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_shot \<E> c \<longleftrightarrow> card (send_sites \<E> c) \<le> 1"


definition single_receiver :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where 
  "single_receiver = single_side recv_sites"

definition single_sender :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where 
  "single_sender = single_side recv_sites"

definition point_to_point :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "point_to_point \<E> c \<longleftrightarrow> single_sender \<E> c \<and> single_receiver \<E> c"
  
definition fan_out :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_out \<E> c \<longleftrightarrow> single_sender \<E> c \<and> \<not> single_receiver \<E> c"
  
definition fan_in :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_in \<E> c \<longleftrightarrow> \<not> single_sender \<E> c \<and> single_receiver \<E> c"

definition var_topo :: "(state_pool \<Rightarrow> chan \<Rightarrow> bool) \<Rightarrow> state_pool \<Rightarrow> var \<Rightarrow> bool" where
  "var_topo t \<E> x \<longleftrightarrow> (\<forall> \<pi> . \<exists> x' e' \<rho>' \<kappa>' . \<E> \<pi> = Some (<<LET x' = CHAN \<lparr>\<rparr> in e', \<rho>', \<kappa>'>>) \<longrightarrow> t \<E> (Ch \<pi> x))"

type_synonym topo_pair = "var \<times> topo"

type_synonym topo_env = "var \<Rightarrow> topo"

definition var_to_topo :: "state_pool \<Rightarrow> var \<Rightarrow> topo" ("\<langle>\<langle>_ ; _\<rangle>\<rangle>" [0,0]61) where
  "\<langle>\<langle>\<E> ; x\<rangle>\<rangle> = 
    (if var_topo one_shot \<E> x then OneShot
    else (if var_topo point_to_point \<E> x then OneToOne
    else (if var_topo fan_out \<E> x then FanOut
    else (if var_topo fan_in \<E> x then FanOut
    else Any))))
  "



definition state_pool_to_topo_env :: "state_pool \<Rightarrow> topo_env" ("\<langle>\<langle>_\<rangle>\<rangle>" [0]61) where
  "\<langle>\<langle>\<E>\<rangle>\<rangle> = (\<lambda> x . \<langle>\<langle>\<E> ; x\<rangle>\<rangle>)"


inductive precision_order :: "topo \<Rightarrow> topo \<Rightarrow> bool" (infix "\<preceq>" 55) where  
  Edge1 : "OneShot \<preceq> OneToOne" | 
  Edge2 : "OneToOne \<preceq> FanOut" |
  Edge3 : "OneToOne \<preceq> FanIn" |
  Edge4 : "FanOut \<preceq> Any" |
  Edge5 : "FanIn \<preceq> Any" |
  Refl : "t \<preceq> t" |
  Trans : "\<lbrakk> a \<preceq> b ; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c"

definition topo_env_precision :: "topo_env \<Rightarrow> topo_env \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>t" 55) where
  "\<A> \<sqsubseteq>\<^sub>t \<A>' \<equiv> (\<forall> x . \<A> x \<preceq> \<A>' x)"




type_synonym abstract_path = "(var + unit) list"


inductive path_in_exp' :: "abstract_value_env \<Rightarrow> abstract_path \<Rightarrow> exp \<Rightarrow> bool" ("_ \<Turnstile> _ \<triangleleft> _" [56, 0, 56] 55) where
  Result: "\<V> \<Turnstile> [Inl x] \<triangleleft> (RESULT x)" |
  Let_Unit: "
    \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Prim: "
    \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = Prim p in e)
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<Turnstile> \<pi>\<^sub>l \<triangleleft> e\<^sub>l; 
      \<V> \<Turnstile> \<pi> \<triangleleft> e 
    \<rbrakk>\<Longrightarrow> 
    \<V> \<Turnstile> (\<pi>\<^sub>l @ (Inl x # \<pi>)) \<triangleleft> (LET x = CASE _ LEFT x\<^sub>l |> e\<^sub>l RIGHT _ |> _ in e)
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<Turnstile> \<pi>\<^sub>r \<triangleleft> e\<^sub>r;
      \<V> \<Turnstile> \<pi> \<triangleleft> e
    \<rbrakk> \<Longrightarrow> 
    \<V> \<Turnstile> (\<pi>\<^sub>r @ (Inl x # \<pi>)) \<triangleleft> (LET x = CASE _ LEFT _ |> _ RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_Fst: "
    \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = FST _ in e)
  " |
  Let_Snd: "
    \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = SND _ in e)
  " |
  Let_App: "
    \<lbrakk>
      ^Abs f' x' e' \<in> \<V> f;
      (\<V>(x' := \<V> x' \<inter> \<V> x\<^sub>a)) \<Turnstile> \<pi>' \<triangleleft> e';
      \<V> \<Turnstile> \<pi> \<triangleleft> e
    \<rbrakk> \<Longrightarrow> 
    \<V> \<Turnstile> (\<pi>' @ (Inl x # \<pi>)) \<triangleleft> (LET x = APP f x\<^sub>a in e)
  " |
  Let_Sync: "
   \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow>
   \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = SYNC _ in e)
  " |
  Let_Chan: "
    \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow>
    \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    \<V> \<Turnstile> \<pi> \<triangleleft> e \<Longrightarrow>
    \<V> \<Turnstile> (Inl x # \<pi>) \<triangleleft> (LET x = SPAWN _ in e)
  " |
  Let_Spawn_Child: " 
    \<V> \<Turnstile> \<pi> \<triangleleft> e\<^sub>c \<Longrightarrow>
    \<V> \<Turnstile> (Inr () # \<pi>) \<triangleleft> (LET x = SPAWN e\<^sub>c in _)
  " 


definition path_in_exp :: "abstract_path \<Rightarrow> exp \<Rightarrow> bool" (infix "\<triangleleft>" 55)where
  "\<pi> \<triangleleft> e \<equiv> (\<exists> \<V> \<C> . (\<V>, \<C>) \<Turnstile> e \<and> (\<V> \<Turnstile> \<pi> \<triangleleft> e))"

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<unlhd>" 55)where
  Refl: "e \<unlhd> e" |
  Step: "e' \<unlhd> e \<Longrightarrow> e' \<unlhd> (LET x = b in e)"

definition abstract_send_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "abstract_send_sites x\<^sub>c e = {x . \<exists> x\<^sub>e e' x\<^sub>m \<V> \<C>. 
    (LET x = SYNC x\<^sub>e in e') \<unlhd> e \<and> 
    (\<V>, \<C>) \<Turnstile> e \<and> 
    {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
  }"

definition abstract_recv_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "abstract_recv_sites x\<^sub>c e = {x . \<exists> x\<^sub>e e' \<V> \<C>. 
    (LET x = SYNC x\<^sub>e in e') \<unlhd> e \<and> 
    (\<V>, \<C>) \<Turnstile> e \<and> 
    {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x\<^sub>e
  }"


definition abstract_paths :: "var set \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "abstract_paths sites e = {\<pi>;;x | \<pi> x . 
    (x \<in> sites) \<and>  (\<pi>;;x) \<triangleleft> e
  }" 

definition abstract_processes :: "var set \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "abstract_processes sites e = {\<pi> \<in> abstract_paths sites e .
    (\<exists> \<pi>' . (\<pi> @ [Inr ()] @ \<pi>') \<in> abstract_paths sites e) \<or>
    (\<forall> \<pi>' . (\<pi> @ \<pi>') \<notin> abstract_paths sites e)
  }" 

definition abstract_send_paths where 
  "abstract_send_paths c e = abstract_paths (abstract_send_sites c e) e"

definition abstract_recv_paths where 
  "abstract_recv_paths c e = abstract_paths (abstract_recv_sites c e) e"

definition abstract_send_processes where 
  "abstract_send_processes c e = abstract_processes (abstract_send_sites c e) e"

definition abstract_recv_processes where 
  "abstract_recv_processes c e = abstract_processes (abstract_recv_sites c e) e"

definition one_max :: "abstract_path set \<Rightarrow> bool"  where
  "one_max \<T> \<equiv>  (\<nexists> p . p \<in> \<T>) \<or> (\<exists>! p . p \<in> \<T>)"


inductive topo_pair_accept :: "topo_pair \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>t" 55) where
  OneShot: "
    one_max (abstract_send_paths c e) \<Longrightarrow> 
    (c, OneShot) \<Turnstile>\<^sub>t e
  " | 
  OneToOne: "
    \<lbrakk> 
      one_max (abstract_send_processes c e) ;
      one_max (abstract_recv_processes c e) 
    \<rbrakk> \<Longrightarrow> 
    (c, OneToOne) \<Turnstile>\<^sub>t e
  " | 

  FanOut: "
    one_max (abstract_send_processes c e) \<Longrightarrow> 
    (c, FanOut) \<Turnstile>\<^sub>t e
  " | 

  FanIn: "
    one_max (abstract_recv_processes c e) \<Longrightarrow> 
    (c, FanIn) \<Turnstile>\<^sub>t e
  " | 

  Any: "(c, Any) \<Turnstile>\<^sub>t e"


definition topo_accept :: "topo_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<bind>" 55) where 
  "\<A> \<bind> e \<longleftrightarrow> (\<forall> x . (x, \<A> x) \<Turnstile>\<^sub>t e)"

(*

inductive topo_pair_over_value_accept :: "topo_pair \<Rightarrow> val \<Rightarrow> bool" (infix "\<parallel>>\<^sub>t" 55)
and  topo_pair_over_env_accept :: "topo_pair \<Rightarrow> (var \<rightharpoonup> val) \<Rightarrow> bool" (infix "\<parallel>\<approx>\<^sub>t" 55) 
where
inductive topo_pair_over_stack_accept :: "topo_pair \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>t _ \<Rrightarrow> _" [56, 0, 56] 55)

inductive topo_pair_over_state_accept :: "topo_pair \<Rightarrow> state \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>t" 55) where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e; 
      (\<V>, \<C>) \<parallel>\<approx> \<rho>; 
      (\<V>, \<C>) \<Turnstile> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<TTurnstile> <<e, \<rho>, \<kappa>>>
  "

inductive topo_pair_over_pool_accept :: "topo_pair \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<parallel>\<lless>\<^sub>t" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<TTurnstile> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<parallel>\<lless> \<E>
  "

*)
 

end
