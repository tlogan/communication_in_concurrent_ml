theory Static_Communication_Analysis
  imports Main Syntax Runtime_Semantics Static_Semantics Runtime_Communication_Analysis
begin

definition all  :: "(control_path \<Rightarrow> bool) \<Rightarrow> (control_path \<Rightarrow> control_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "all P R \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    P \<pi>\<^sub>1 \<longrightarrow>
    P \<pi>\<^sub>2 \<longrightarrow>
    R \<pi>\<^sub>1 \<pi>\<^sub>2
  )"


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


definition is_static_send_path :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_send_path \<A> x\<^sub>c \<pi>' \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>s\<^sub>c x\<^sub>m e\<^sub>n . 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
    {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
  )"

definition is_static_recv_path :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_static_recv_path \<A> x\<^sub>c \<pi>' \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> (\<exists> \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>r\<^sub>c e\<^sub>n \<omega>. 
    \<pi>' = \<pi>\<^sub>y;;`x\<^sub>y \<and>
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e \<and>
    {|\<omega>|} \<subseteq> \<V> x\<^sub>y
  )"

(*  

Reppy/Xiao analyze the subprogram within which a channel is live, 
thus avoiding conflating different instances of a channel with one name, 
such as one created in a loop.

Reppy/Xiao do not distinguish between paths that 
occur in the same run from those that occur in the same subprogram.

Reppy/Xiao consider paths with the same process path to be noncompetitive statically.

*)
(*
  L_Left var ("\<upharpoonleft>\<bar>_" [71] 70) |
  L_Right var ("\<upharpoonleft>:_" [71] 70) | 
  L_Up var ("\<upharpoonleft>_" [71] 70) |
  L_Down var ("\<downharpoonleft>_" [71] 70)
*)

inductive linear :: "control_path \<Rightarrow> bool" where
 Seq: "linear \<pi> \<Longrightarrow> linear (`x # \<pi>)" | 
 Left: "linear \<pi> \<Longrightarrow> linear (\<upharpoonleft>\<bar>x # \<pi>)" |
 Right: "linear \<pi> \<Longrightarrow> linear (\<upharpoonleft>:x # \<pi>)" |
 UP: "linear \<pi> \<Longrightarrow> linear (\<upharpoonleft>x # \<pi>)" |
 Down: "linear \<pi> \<Longrightarrow> linear (\<downharpoonleft>x # \<pi>)" |
 Empty: "linear []"



inductive same_process :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<cong>" 55) where
 Lin: "linear \<pi>\<^sub>1 \<Longrightarrow> linear \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2" |
 Spawn: "linear \<pi>\<^sub>1 \<Longrightarrow> linear \<pi>\<^sub>2 \<Longrightarrow> \<pi> @ (.x # \<pi>\<^sub>1) \<cong> \<pi> @ (.x # \<pi>\<^sub>2)"

(*

this seems like a correct simple definition of exclusive

inductive exclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<triangleq>" 55) where
 Same_Proc: "
   \<lbrakk>
     \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2;
     \<not> prefix \<pi>\<^sub>1 \<pi>\<^sub>2;
     \<not> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
   \<rbrakk> \<Longrightarrow> 
   \<pi>\<^sub>1 \<triangleq> \<pi>\<^sub>2
 " |    
 Cons_Spawn: "
   \<lbrakk>
     \<pi>\<^sub>1 \<triangleq> \<pi>\<^sub>2
   \<rbrakk> \<Longrightarrow> 
   \<pi>\<^sub>1 @ (.x # \<pi>\<^sub>1') \<triangleq> \<pi>\<^sub>2 @ (.x # \<pi>\<^sub>2')
 "
*)

lemma same_process_commut: "
  \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>2 \<cong> \<pi>\<^sub>1
"
by (metis Lin Spawn same_process.cases)

definition exclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> \<pi>\<^sub>1 = \<pi>\<^sub>2"

definition noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
 "noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1"

definition static_one_shot :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_shot \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) exclusive \<and> all (is_static_recv_path \<A> x\<^sub>c) exclusive"

definition static_one_to_one :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_to_one \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) noncompetitive \<and> all (is_static_recv_path \<A> x\<^sub>c) noncompetitive"

definition static_fan_out :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_out \<A> x\<^sub>c \<equiv> all (is_static_send_path \<A> x\<^sub>c) noncompetitive"

definition static_fan_in :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_in \<A> x\<^sub>c \<equiv> all (is_static_recv_path \<A> x\<^sub>c) noncompetitive"


inductive topo_pair_accept :: "topo_pair \<Rightarrow> exp \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  OneShot: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      static_one_shot (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, OneShot) \<TTurnstile> e
  " | 
  OneToOne: "
    \<lbrakk> 
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      static_one_to_one (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, OneToOne) \<TTurnstile> e
  " | 

  FanOut: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      static_fan_out (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, FanOut) \<TTurnstile> e
  " | 

  FanIn: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      static_fan_in (\<V>, \<C>, e) x\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    (x\<^sub>c, FanIn) \<TTurnstile> e
  " | 

  ManyToMany: "(x\<^sub>c, ManyToMany) \<TTurnstile> e"


definition topo_accept :: "topo_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<bind>" 55) where 
  "\<A> \<bind> e \<equiv> (\<forall> x\<^sub>c . (x\<^sub>c, \<A> x\<^sub>c) \<TTurnstile> e)"

end
