theory Analysis
  imports Main Syntax
begin


(*

determine values of higher-order abstractions and channels
determine program points (Var x) send/receive on a static channel (Var c)
determine which paths reach (Var x)
determine total number of processes and paths that reach every (Var x)


How to represent loops statically?
  stop after first loop is recorded.  Only care if there is either one or more.
*)

(*



type_synonym point_env = "var \<Rightarrow> var set"

inductive send_sites_accept :: "point_env \<Rightarrow> exp \<Rightarrow> bool" (infix "s\<Turnstile>" 55) where  
  Something: "x s\<Turnstile> y"

inductive receive_sites_accept :: "point_env \<Rightarrow> exp \<Rightarrow> bool" (infix "r\<Turnstile>" 55) where  
  Something: "x r\<Turnstile> y"


type_synonym abstract_path_env = "var \<rightharpoonup> abstract_path set"

inductive abstract_path_accept :: "abstract_path_env \<Rightarrow> exp \<Rightarrow> bool" (infix "p\<Turnstile>" 55) where  
  Something: "x p\<Turnstile> y"

*)

type_synonym abstract_path = "(var + unit) list"

definition paths_to :: "var \<Rightarrow> exp \<Rightarrow> abstract_path set" where
  "paths_to x e = {}"

datatype abstract_value = Chan var | Unit | Prim prim
type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"

inductive val_env_accept :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>" 55) where  
  Something: "x \<Turnstile> y"

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" where
  Refl: "subexp e e" |
  Step: "subexp e' e \<Longrightarrow> subexp e' (LET _ = _ in e)"

definition send_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "send_sites c e = {x . \<exists> y e' \<rho> z. 
    subexp (LET x = SYNC y in e') e \<and> 
    val_env_accept \<rho> e \<and> 
    Prim (P_Send_Evt c z) \<in> (\<rho> y)
  }"

definition send_paths :: "var \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "send_paths c e = {path @ [Inl x] | (path::abstract_path) (x::var) . 
    (x \<in> send_sites c) \<and>  (path @ (Inl x) \<in> paths_to x e)
  }" 

datatype topo_class = OneShot | OneToOne | FanOut | FanIn | Any

type_synonym topo_class_pair = "var \<times> topo_class"

inductive class_pair_accept :: "topo_class_pair \<Rightarrow> exp \<Rightarrow> bool" where
  OneShot: "
    path_count (send_paths c e) \<le> 1 \<Longrightarrow> 
    class_pair_accept (c, OneShot) e
  " | 

  OneToOne: "
    \<lbrakk> 
      process_count (send_paths c e) \<le> 1 ;
      process_count (receive_paths c e) \<le> 1 
    \<rbrakk> \<Longrightarrow> 
    class_pair_accept (c, OneToOne) e
  " | 

  FanOut: "
    \<lbrakk> 
      process_count (send_paths c e) \<le> 1
    \<rbrakk> \<Longrightarrow> 
    class_pair_accept (c, FanOut) e
  " | 

  FanIn: "
    process_count (receive_paths c e) \<le> 1 \<Longrightarrow> 
    class_pair_accept (c, OneToOne) e
  " | 

  Any: "class_pair_accept (c, OneToOne) e"


type_synonym topo_class_env = "var \<Rightarrow> topo_class"

definition test :: "bool \<Rightarrow> bool" where
  Something:  "test b \<equiv> b"

definition class_env_accept :: "topo_class_env \<Rightarrow> exp \<Rightarrow> bool" where 
  "class_env_accept E e \<equiv> (\<forall> (x::var) (t::topo_class) . ((E x) = t) \<and> (class_pair_accept (x, t) e))"



inductive precision_order :: "topo_class \<Rightarrow> topo_class \<Rightarrow> bool" (infix "\<preceq>" 55) where  
  Edge1 : "OneShot \<preceq> OneToOne" | 
  Edge2 : "OneToOne \<preceq> FanOut" |
  Edge3 : "OneToOne \<preceq> FanIn" |
  Edge4 : "FanOut \<preceq> Any" |
  Edge5 : "FanIn \<preceq> Any" |
  Refl : "t \<preceq> t" |
  Trans : "\<lbrakk> a \<preceq> b ; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c"

end