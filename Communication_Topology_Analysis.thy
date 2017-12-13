theory Communication_Topology_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin


datatype topo = OneShot | OneToOne | FanOut | FanIn | Any
type_synonym topo_pair = "var \<times> topo"
type_synonym topo_env = "var \<Rightarrow> topo"

class com_topo =
  fixes flow_accept :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<Turnstile>" 55)
  fixes exp_accept :: "exp \<Rightarrow> 'a \<Rightarrow> bool"
  fixes flow_path_accept :: "abstract_value_env \<Rightarrow> control_path \<Rightarrow> 'a \<Rightarrow> bool" (" _ \<tturnstile> _ \<triangleleft> _ " [56,0,56]55)

definition (in com_topo) abstract_send_sites :: "var \<Rightarrow> 'a \<Rightarrow> var set" where
  "abstract_send_sites x\<^sub>c g \<equiv> {x . \<exists> x\<^sub>e e' x\<^sub>m \<V> \<C>. 
    exp_accept (LET x = SYNC x\<^sub>e in e') g \<and> 
    (\<V>, \<C>) \<Turnstile> g \<and> 
    {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e
  }"

definition (in com_topo) abstract_recv_sites :: "var \<Rightarrow> 'a \<Rightarrow> var set" where
  "abstract_recv_sites x\<^sub>c g \<equiv> {x . \<exists> x\<^sub>e e' \<V> \<C>. 
    exp_accept (LET x = SYNC x\<^sub>e in e') g \<and> 
    (\<V>, \<C>) \<Turnstile> g \<and> 
    {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x\<^sub>e
  }"

definition (in com_topo) control_paths :: "abstract_value_env \<Rightarrow> var set \<Rightarrow> 'a \<Rightarrow> control_path set" where 
  "control_paths \<V> sites g \<equiv> {\<pi>;;x | \<pi> x . 
    (x \<in> sites) \<and> \<V> \<tturnstile> (\<pi>;;x) \<triangleleft> g
  }" 

definition (in com_topo) abstract_processes :: "abstract_value_env \<Rightarrow> var set \<Rightarrow> 'a \<Rightarrow> control_path set" where 
  "abstract_processes \<V> sites e \<equiv> {\<pi> \<in> control_paths \<V> sites e .
    (\<exists> \<pi>' . (\<pi> @ [Inr ()] @ \<pi>') \<in> control_paths \<V> sites e) \<or>
    (\<forall> \<pi>' . (\<pi> @ \<pi>') \<notin> control_paths \<V> sites e)
  }"

definition (in com_topo) abstract_send_paths :: "abstract_value_env \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> control_path set"  where 
  "abstract_send_paths \<V> c g \<equiv> control_paths \<V> (abstract_send_sites c g) g"

definition (in com_topo) abstract_recv_paths :: "abstract_value_env \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> control_path set"  where 
  "abstract_recv_paths \<V> c g \<equiv> control_paths \<V> (abstract_recv_sites c g) g"

definition (in com_topo) abstract_send_processes :: "abstract_value_env \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> control_path set"  where 
  "abstract_send_processes \<V> c g \<equiv> abstract_processes \<V> (abstract_send_sites c g) g"

definition (in com_topo) abstract_recv_processes :: "abstract_value_env \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> control_path set"  where 
  "abstract_recv_processes \<V> c g \<equiv> abstract_processes \<V> (abstract_recv_sites c g) g"

definition one_max :: "control_path set \<Rightarrow> bool"  where
  "one_max \<T> \<equiv>  (\<nexists> p . p \<in> \<T>) \<or> (\<exists>! p . p \<in> \<T>)"


inductive (in com_topo) topo_pair_accept :: "topo_pair \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  OneShot: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      one_max (abstract_send_paths \<V> c e) 
    \<rbrakk> \<Longrightarrow> 
    (c, OneShot) \<TTurnstile> e
  " | 
  OneToOne: "
    \<lbrakk> 
      (\<V>, \<C>) \<Turnstile> e;
      one_max (abstract_send_processes \<V> c e) ;
      one_max (abstract_recv_processes \<V> c e) 
    \<rbrakk> \<Longrightarrow> 
    (c, OneToOne) \<TTurnstile> e
  " | 

  FanOut: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      one_max (abstract_send_processes \<V> c e) 
    \<rbrakk> \<Longrightarrow> 
    (c, FanOut) \<TTurnstile> e
  " | 

  FanIn: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile> e;
      one_max (abstract_recv_processes \<V> c e) 
    \<rbrakk> \<Longrightarrow> 
    (c, FanIn) \<TTurnstile> e
  " | 

  Any: "(c, Any) \<TTurnstile> e"


(***************)


definition send_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_sites \<E> ch \<equiv> {\<pi>. \<exists> x x\<^sub>e e \<kappa> \<rho> x\<^sub>c x\<^sub>m \<rho>\<^sub>e. 
    \<E> \<pi> = Some (\<langle>LET x = SYNC x\<^sub>e in e; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>c = Some \<lbrace>ch\<rbrace>
  }"

definition recv_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_sites \<E> ch \<equiv> {\<pi>. \<exists> x x\<^sub>e e \<kappa> \<rho> x\<^sub>c \<rho>\<^sub>e. 
    \<E> \<pi> = Some (\<langle>LET x = SYNC x\<^sub>e in e; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>c, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>c = Some \<lbrace>ch\<rbrace>
  }"

definition single_side :: "(state_pool \<Rightarrow> chan \<Rightarrow> control_path set) \<Rightarrow> state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "single_side sites_of \<E> c \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
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
  "var_topo t \<E> x \<longleftrightarrow> (\<forall> \<pi> . \<exists> x' e' \<rho>' \<kappa>' . \<E> \<pi> = Some (\<langle>LET x' = CHAN \<lparr>\<rparr> in e'; \<rho>'; \<kappa>'\<rangle>) \<longrightarrow> t \<E> (Ch \<pi> x))"

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


inductive flow_path_in_exp :: "abstract_value_env \<Rightarrow> control_path \<Rightarrow> exp \<Rightarrow> bool" ("_ \<tturnstile>\<^sub>e _ \<triangleleft> _" [56, 0, 56] 55) where
  Result: "\<V> \<tturnstile>\<^sub>e [Inl x] \<triangleleft> (RESULT x)" |
  Let_Unit: "
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Prim: "
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = Prim p in e)
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<tturnstile>\<^sub>e \<pi>\<^sub>l \<triangleleft> e\<^sub>l; 
      \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e 
    \<rbrakk>\<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (\<pi>\<^sub>l @ (Inl x # \<pi>)) \<triangleleft> (LET x = CASE _ LEFT x\<^sub>l |> e\<^sub>l RIGHT _ |> _ in e)
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<tturnstile>\<^sub>e \<pi>\<^sub>r \<triangleleft> e\<^sub>r;
      \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e
    \<rbrakk> \<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (\<pi>\<^sub>r @ (Inl x # \<pi>)) \<triangleleft> (LET x = CASE _ LEFT _ |> _ RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_Fst: "
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = FST _ in e)
  " |
  Let_Snd: "
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = SND _ in e)
  " |
  Let_App: "
    \<lbrakk>
      {^Abs f' x' e'} \<subseteq> \<V> f;
      (\<V>(x' := \<V> x' \<inter> \<V> x\<^sub>a)) \<tturnstile>\<^sub>e \<pi>' \<triangleleft> e';
      \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e
    \<rbrakk> \<Longrightarrow> 
    \<V> \<tturnstile>\<^sub>e (\<pi>' @ (Inl x # \<pi>)) \<triangleleft> (LET x = APP f x\<^sub>a in e)
  " |
  Let_Sync: "
   \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow>
   \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = SYNC _ in e)
  " |
  Let_Chan: "
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow>
    \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e \<Longrightarrow>
    \<V> \<tturnstile>\<^sub>e (Inl x # \<pi>) \<triangleleft> (LET x = SPAWN _ in e)
  " |
  Let_Spawn_Child: " 
    \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e\<^sub>c \<Longrightarrow>
    \<V> \<tturnstile>\<^sub>e (Inr () # \<pi>) \<triangleleft> (LET x = SPAWN e\<^sub>c in _)
  "

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<unlhd>" 55)where
  Refl: "e \<unlhd> e" |
  Step: "e' \<unlhd> e \<Longrightarrow> e' \<unlhd> (LET x = b in e)"

instantiation exp :: com_topo
begin
definition flow_accept_exp where "\<T> \<Turnstile> e \<equiv> \<T> \<Turnstile>\<^sub>e e" 
definition exp_accept_exp where "exp_accept e' e \<equiv> e' \<unlhd> e"
definition flow_path_accept_exp where " \<V> \<tturnstile> \<pi> \<triangleleft> e  \<equiv> \<V> \<tturnstile>\<^sub>e \<pi> \<triangleleft> e"
instance proof qed
end 

abbreviation topo_pair_accept_exp :: "topo_pair \<Rightarrow> exp \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>e" 55) where
  "\<T> \<TTurnstile>\<^sub>e e \<equiv> \<T> \<TTurnstile> e "


definition topo_accept :: "topo_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<bind>" 55) where 
  "\<A> \<bind> e \<equiv> (\<forall> x . (x, \<A> x) \<TTurnstile>\<^sub>e e)"


inductive exp_in_pool :: "exp \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<lhd>|" 55)where
  Any: "
    \<lbrakk>
      \<E> \<pi> = Some (\<langle>e; \<rho>; \<kappa>\<rangle>);
      e' \<unlhd> e
    \<rbrakk> \<Longrightarrow>
    e' \<lhd>| \<E>
  "


definition path_in_state_pool :: "abstract_value_env \<Rightarrow> control_path \<Rightarrow> state_pool \<Rightarrow> bool" ("_ \<tturnstile>\<^sub>\<E> _ \<triangleleft> _ " [56,0,56]55) where
  "\<V> \<tturnstile>\<^sub>\<E> \<pi> \<triangleleft> \<E>  \<equiv> (\<exists> \<V> \<C> \<pi>' e' \<rho>' \<kappa>' \<pi>''. 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E> \<and> 
    \<E> \<pi>' = Some (\<langle>e'; \<rho>'; \<kappa>'\<rangle>) \<and> 
    \<V> \<tturnstile>\<^sub>e \<pi>'' \<triangleleft> e'
  )"

datatype state_pool' = SP state_pool
instantiation state_pool' :: com_topo
begin
fun flow_accept_state_pool' where "\<T> \<Turnstile> (SP \<E>) = \<T> \<Turnstile>\<^sub>\<E> \<E>" 
fun exp_accept_state_pool' where "exp_accept e' (SP \<E>) = e' \<lhd>| \<E>"
fun flow_path_accept_state_pool' where "\<V> \<tturnstile> \<pi> \<triangleleft> (SP \<E>) = \<V> \<tturnstile>\<^sub>\<E> \<pi> \<triangleleft> \<E>"
instance proof qed
end 


abbreviation topo_pair_accept_state_pool :: "topo_pair \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<TTurnstile>\<^sub>\<E>" 55) where
  "\<T> \<TTurnstile>\<^sub>\<E> \<E> \<equiv> \<T> \<TTurnstile> (SP \<E>) "

end
