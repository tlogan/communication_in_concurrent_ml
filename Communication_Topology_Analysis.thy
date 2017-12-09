theory Communication_Topology_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin

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


datatype topo = OneShot | OneToOne | FanOut | FanIn | Any

type_synonym topo_pair = "var \<times> topo"

inductive communication_topology' :: "topo_pair \<Rightarrow> exp \<Rightarrow> bool" (infix "\<parallel>\<bind>" 55) where
  OneShot: "
    one_max (send_paths c e) \<Longrightarrow> 
    (c, OneShot) \<parallel>\<bind> e
  " | 
  OneToOne: "
    \<lbrakk> 
      one_max (send_processes c e) ;
      one_max (recv_processes c e) 
    \<rbrakk> \<Longrightarrow> 
    (c, OneToOne) \<parallel>\<bind> e
  " | 

  FanOut: "
    one_max (send_processes c e) \<Longrightarrow> 
    (c, FanOut) \<parallel>\<bind> e
  " | 

  FanIn: "
    one_max (recv_processes c e) \<Longrightarrow> 
    (c, FanIn) \<parallel>\<bind> e
  " | 

  Any: "(c, Any) \<parallel>\<bind> e"


type_synonym topo_env = "var \<Rightarrow> topo"

definition communication_topology :: "topo_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<bind>" 55) where 
  "\<A> \<bind> e \<longleftrightarrow> (\<forall> x . (x, \<A> x) \<parallel>\<bind> e)"



definition env_to_topo_env :: "(var \<rightharpoonup> val) \<Rightarrow> topo_env" ("\<langle>\<langle>_\<rangle>\<rangle>" [0]61) where
  "\<langle>\<langle>\<rho>\<rangle>\<rangle> = (\<lambda> x . Any)"


inductive precision_order :: "topo \<Rightarrow> topo \<Rightarrow> bool" (infix "\<preceq>" 55) where  
  Edge1 : "OneShot \<preceq> OneToOne" | 
  Edge2 : "OneToOne \<preceq> FanOut" |
  Edge3 : "OneToOne \<preceq> FanIn" |
  Edge4 : "FanOut \<preceq> Any" |
  Edge5 : "FanIn \<preceq> Any" |
  Refl : "t \<preceq> t" |
  Trans : "\<lbrakk> a \<preceq> b ; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c"

definition topo_env_prevision :: "topo_env \<Rightarrow> topo_env \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>t" 55) where
  "\<A> \<sqsubseteq>\<^sub>t \<A>' \<equiv> (\<forall> x . \<A> x \<preceq> \<A>' x)"
end
