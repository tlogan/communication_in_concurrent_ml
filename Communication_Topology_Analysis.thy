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

definition chan_to_topo :: "state_pool \<Rightarrow> chan \<Rightarrow> topo" ("\<langle>\<langle>_ ; _\<rangle>\<rangle>" [0,0]61) where
  "\<langle>\<langle>\<E> ; c\<rangle>\<rangle> = 
    (if one_shot \<E> c then OneShot
    else (if point_to_point \<E> c then OneToOne
    else (if fan_out \<E> c then FanOut
    else (if fan_in \<E> c then FanOut
    else Any))))
  "



definition state_pool_to_topo_env :: "state_pool \<Rightarrow> topo_env" ("\<langle>\<langle>_\<rangle>\<rangle>" [0]61) where
  "\<langle>\<langle>\<E>\<rangle>\<rangle> = (\<lambda> x .
    (if var_topo one_shot \<E> x then OneShot
    else (if var_topo point_to_point \<E> x then OneToOne
    else (if var_topo fan_out \<E> x then FanOut
    else (if var_topo fan_in \<E> x then FanOut
    else Any))))
  )"


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

definition abstract_send_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "abstract_send_sites c e = {x . \<exists> y e' z \<V> \<C>. 
    subexp (LET x = SYNC y in e') e \<and> 
    (\<V>, \<C>) \<Turnstile> e \<and> 
    ^Send_Evt c z \<in> \<V> y
  }"

definition abstract_recv_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "abstract_recv_sites c e = {x . \<exists> y e' \<V> \<C>. 
    subexp (LET x = SYNC y in e') e \<and> 
    (\<V>, \<C>) \<Turnstile> e \<and> 
    ^Recv_Evt c \<in> \<V> y
  }"


definition abstract_paths :: "var set \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "abstract_paths sites e = {path @ [Inl x] | path x . 
    (x \<in> sites) \<and>  path_in_exp (path @ [Inl x]) e
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



inductive communication_topology' :: "topo_pair \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>t" 55) where
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


definition communication_topology :: "topo_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<bind>" 55) where 
  "\<A> \<bind> e \<longleftrightarrow> (\<forall> x . (x, \<A> x) \<Turnstile>\<^sub>t e)"

end
