theory Abstract_Communication_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis Communication_Analysis
begin

datatype topo = Non | OneShot | OneToOne | FanOut | FanIn | ManyToMany
type_synonym topo_pair = "var \<times> topo"
type_synonym topo_env = "var \<Rightarrow> topo"

definition var_to_topo :: "state_pool \<Rightarrow> control_path \<Rightarrow> var \<Rightarrow> topo" ("\<langle>\<langle>_ ; _ ; _\<rangle>\<rangle>" [0,0,0]61) where
  "\<langle>\<langle>\<E> ; \<pi>; x\<rangle>\<rangle> \<equiv>
    (if  one_shot \<E> (Ch \<pi> x) then OneShot
    else (if one_to_one \<E> (Ch \<pi> x) then OneToOne
    else (if fan_out \<E> (Ch \<pi> x) then FanOut
    else (if fan_in \<E> (Ch \<pi> x) then FanIn
    else ManyToMany))))
  "

definition state_pool_to_topo_env :: "state_pool \<Rightarrow> control_path \<Rightarrow> topo_env" ("\<langle>\<langle>_ ; _\<rangle>\<rangle>" [0, 0]61) where
  "\<langle>\<langle>\<E> ; \<pi>\<rangle>\<rangle> = (\<lambda> x . \<langle>\<langle>\<E> ; \<pi>; x\<rangle>\<rangle>)"

inductive precision_order :: "topo \<Rightarrow> topo \<Rightarrow> bool" (infix "\<preceq>" 55) where  
  Edge1 : "OneShot \<preceq> OneToOne" | 
  Edge2 : "OneToOne \<preceq> FanOut" |
  Edge3 : "OneToOne \<preceq> FanIn" |
  Edge4 : "FanOut \<preceq> ManyToMany" |
  Edge5 : "FanIn \<preceq> ManyToMany" |
  Refl : "t \<preceq> t" |
  Trans : "\<lbrakk> a \<preceq> b ; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c"

definition topo_env_precision :: "topo_env \<Rightarrow> topo_env \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>t" 55) where
  "\<A> \<sqsubseteq>\<^sub>t \<A>' \<equiv> (\<forall> x . \<A> x \<preceq> \<A>' x)"

inductive exp_reachable :: "abstract_value_env \<times> exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<downharpoonright>" 55) where
  Refl: "
    (\<V>, e) \<downharpoonright> e
  " |
  Let: "
    \<lbrakk>
      (\<V>, e) \<downharpoonright> (LET x = b in e');
      ^\<omega> \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    (\<V>, e) \<downharpoonright> e'
  " |
  Let_App: "
    \<lbrakk>
      (\<V>, e) \<downharpoonright> (LET x = APP f x\<^sub>a in _);
      ^Abs f' x' e' \<in> \<V> f
    \<rbrakk> \<Longrightarrow>
    (\<V>, e) \<downharpoonright> e'
  " |
  Let_Case_Left: "
    \<lbrakk>
      (\<V>, e) \<downharpoonright> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in _);
      ^Left x\<^sub>l' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    (\<V>, e) \<downharpoonright> e\<^sub>l
  " |
  Let_Case_Right: "
    \<lbrakk>
      (\<V>, e) \<downharpoonright> (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in _);
      ^Right x\<^sub>r' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    (\<V>, e) \<downharpoonright> e\<^sub>r
  " |
  Let_Spawn: "
    \<lbrakk>
      (\<V>, e) \<downharpoonright> (LET x = SPAWN e\<^sub>c in _)
    \<rbrakk> \<Longrightarrow>
    (\<V>, e) \<downharpoonright> e\<^sub>c
  "

inductive path_reachable :: "abstract_value_env \<times> exp \<Rightarrow> control_path \<Rightarrow> bool" (infix ":\<downharpoonright>" 55) where
  Empty: "
   (\<V>, e) :\<downharpoonright> []
  "


definition abstract_send_sites :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> var set" where
  "abstract_send_sites \<A> x\<^sub>c \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> {x\<^sub>y | x\<^sub>e x\<^sub>y x\<^sub>s\<^sub>c x\<^sub>m e'. 
    (\<V>, e) \<downharpoonright> (LET x\<^sub>y = SYNC x\<^sub>e in e') \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
    {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
  }"

definition abstract_recv_sites :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> var set" where
  "abstract_recv_sites \<A> x\<^sub>c \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> {x\<^sub>y | x\<^sub>e x\<^sub>y x\<^sub>r\<^sub>c e'. 
    (\<V>, e) \<downharpoonright> (LET x\<^sub>y = SYNC x\<^sub>e in e') \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e \<and>
    \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>y
  }"

definition abstract_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var set \<Rightarrow> control_path set" where 
  "abstract_paths \<A> sites \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow>  {\<pi>\<^sub>y;;`x\<^sub>y | \<pi>\<^sub>y x\<^sub>y . 
    (x\<^sub>y \<in> sites) \<and> (\<V>, e) :\<downharpoonright> (\<pi>\<^sub>y;;`x\<^sub>y)
  }" 

definition abstract_send_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path set" where 
  "abstract_send_paths \<A> x\<^sub>c \<equiv> abstract_paths \<A> (abstract_send_sites \<A> x\<^sub>c)"

definition abstract_recv_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow>  var \<Rightarrow> control_path set" where 
  "abstract_recv_paths \<A> x\<^sub>c \<equiv> abstract_paths \<A> (abstract_recv_sites \<A> x\<^sub>c)"


definition abstract_one_shot :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_one_shot \<A> x\<^sub>c \<equiv> single_path (abstract_send_paths \<A> x\<^sub>c) \<and> single_path (abstract_recv_paths \<A> x\<^sub>c)"

definition abstract_one_to_one :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_one_to_one \<A> x\<^sub>c \<equiv> single_proc (abstract_send_paths \<A> x\<^sub>c) \<and> single_proc (abstract_recv_paths \<A> x\<^sub>c)"

definition abstract_fan_out :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_fan_out \<A> x\<^sub>c \<equiv> single_proc (abstract_send_paths \<A> x\<^sub>c)"

definition abstract_fan_in :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_fan_in \<A> x\<^sub>c \<equiv> single_proc (abstract_recv_paths \<A> x\<^sub>c)"


inductive topo_pair_accept :: "topo_pair \<Rightarrow> exp \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  OneShot: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      abstract_one_shot (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, OneShot) \<TTurnstile> e
  " | 
  OneToOne: "
    \<lbrakk> 
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      abstract_one_to_one (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, OneToOne) \<TTurnstile> e
  " | 

  FanOut: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      abstract_fan_out (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, FanOut) \<TTurnstile> e
  " | 

  FanIn: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      abstract_fan_in (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, FanIn) \<TTurnstile> e
  " | 

  ManyToMany: "(x\<^sub>c, ManyToMany) \<TTurnstile> e"


definition topo_accept :: "topo_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<bind>" 55) where 
  "\<A> \<bind> e \<equiv> (\<forall> x\<^sub>c . (x\<^sub>c, \<A> x\<^sub>c) \<TTurnstile> e)"


end
