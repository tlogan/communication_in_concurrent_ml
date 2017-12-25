theory Communication_Topology_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin


datatype topo = Non | OneShot | OneToOne | FanOut | FanIn | ManyToMany
type_synonym topo_pair = "var \<times> topo"
type_synonym topo_env = "var \<Rightarrow> topo"


definition send_paths :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_paths \<E> c \<equiv> {\<pi>\<^sub>y ;; x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e e \<kappa> \<rho> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e. 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e; \<rho>; \<kappa>\<rangle>) \<and>
    \<rho> x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e; \<rho>(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>)
  }"

definition recv_paths :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_paths \<E> c \<equiv> {\<pi>\<^sub>y ;; x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e e \<kappa> \<rho> x\<^sub>r\<^sub>c \<rho>\<^sub>e \<omega>. 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;x\<^sub>y) = Some (\<langle>e; \<rho>(x\<^sub>y \<mapsto> \<omega>); \<kappa>\<rangle>)
  }"

definition single_proc :: "control_path set \<Rightarrow> bool" where
  "single_proc \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    (prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1) 
  )"

definition single_path :: "control_path set \<Rightarrow> bool"  where
  "single_path \<T> \<equiv>  (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 . 
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow> 
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>1 = \<pi>\<^sub>2
  )"

definition one_shot :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_shot \<E> c \<equiv> single_path (send_paths \<E> c) \<and> single_path (recv_paths \<E> c)"


definition one_to_one :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_to_one \<E> c \<equiv> single_proc (send_paths \<E> c) \<and> single_proc (recv_paths \<E> c)"
  
definition fan_out :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_out \<E> c \<equiv> single_proc (send_paths \<E> c)"
  
definition fan_in :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_in \<E> c \<equiv> single_proc (recv_paths \<E> c)"

definition var_to_topo :: "state_pool \<Rightarrow> control_path \<Rightarrow> var \<Rightarrow> topo" ("\<langle>\<langle>_ ; _ ; _\<rangle>\<rangle>" [0,0,0]61) where
  "\<langle>\<langle>\<E> ; \<pi>; x\<rangle>\<rangle> \<equiv>
    (if (\<nexists> e' \<rho>' \<kappa>'. \<E> \<pi> = Some (\<langle>LET x = CHAN \<lparr>\<rparr> in e'; \<rho>'; \<kappa>'\<rangle>)) then Non
    else (if  one_shot \<E> (Ch \<pi> x) then OneShot
    else (if one_to_one \<E> (Ch \<pi> x) then OneToOne
    else (if fan_out \<E> (Ch \<pi> x) then FanOut
    else (if fan_in \<E> (Ch \<pi> x) then FanIn
    else ManyToMany)))))
  "

definition state_pool_to_topo_env :: "state_pool \<Rightarrow> control_path \<Rightarrow> topo_env" ("\<langle>\<langle>_ ; _\<rangle>\<rangle>" [0, 0]61) where
  "\<langle>\<langle>\<E> ; \<pi>\<rangle>\<rangle> = (\<lambda> x . \<langle>\<langle>\<E> ; \<pi>; x\<rangle>\<rangle>)"

inductive precision_order :: "topo \<Rightarrow> topo \<Rightarrow> bool" (infix "\<preceq>" 55) where  
  Edge0 : "Non \<preceq> OneShot" |
  Edge1 : "OneShot \<preceq> OneToOne" | 
  Edge2 : "OneToOne \<preceq> FanOut" |
  Edge3 : "OneToOne \<preceq> FanIn" |
  Edge4 : "FanOut \<preceq> ManyToMany" |
  Edge5 : "FanIn \<preceq> ManyToMany" |
  Refl : "t \<preceq> t" |
  Trans : "\<lbrakk> a \<preceq> b ; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c"

definition topo_env_precision :: "topo_env \<Rightarrow> topo_env \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>t" 55) where
  "\<A> \<sqsubseteq>\<^sub>t \<A>' \<equiv> (\<forall> x . \<A> x \<preceq> \<A>' x)"


inductive flow_path_in_exp :: "abstract_value_env \<Rightarrow> control_path \<Rightarrow> exp \<Rightarrow> bool" ("_ \<tturnstile> _ \<triangleleft> _" [56, 0, 56] 55) where
  Result: "\<V> \<tturnstile> [Inl x] \<triangleleft> (RESULT x)" |
  Let_Unit: "
    \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Prim: "
    \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = Prim p in e)
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<tturnstile> \<pi>\<^sub>l \<triangleleft> e\<^sub>l; 
      \<V> \<tturnstile> \<pi> \<triangleleft> e 
    \<rbrakk>\<Longrightarrow> 
    \<V> \<tturnstile> (\<pi>\<^sub>l @ (Inl x # \<pi>)) \<triangleleft> (LET x = CASE _ LEFT x\<^sub>l |> e\<^sub>l RIGHT _ |> _ in e)
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<tturnstile> \<pi>\<^sub>r \<triangleleft> e\<^sub>r;
      \<V> \<tturnstile> \<pi> \<triangleleft> e
    \<rbrakk> \<Longrightarrow> 
    \<V> \<tturnstile> (\<pi>\<^sub>r @ (Inl x # \<pi>)) \<triangleleft> (LET x = CASE _ LEFT _ |> _ RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_Fst: "
    \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = FST _ in e)
  " |
  Let_Snd: "
    \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow> 
    \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = SND _ in e)
  " |
  Let_App: "
    \<lbrakk>
      {^Abs f\<^sub>p x\<^sub>p e\<^sub>b} \<subseteq> \<V> f;
      \<V>(x\<^sub>p := (\<V> x\<^sub>p) \<inter> (\<V> x\<^sub>a)) \<tturnstile> \<pi>' \<triangleleft> e\<^sub>b;
      \<V> \<tturnstile> \<pi> \<triangleleft> e
    \<rbrakk> \<Longrightarrow> 
    \<V> \<tturnstile> \<pi>' @ (Inl x # \<pi>) \<triangleleft> (LET x = APP f x\<^sub>a in e)
  " |
  Let_Sync: "
   \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow>
   \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = SYNC _ in e)
  " |
  Let_Chan: "
    \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow>
    \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    \<V> \<tturnstile> \<pi> \<triangleleft> e \<Longrightarrow>
    \<V> \<tturnstile> (Inl x # \<pi>) \<triangleleft> (LET x = SPAWN _ in e)
  " |
  Let_Spawn_Child: " 
    \<V> \<tturnstile> \<pi> \<triangleleft> e\<^sub>c \<Longrightarrow>
    \<V> \<tturnstile> (Inr () # \<pi>) \<triangleleft> (LET x = SPAWN e\<^sub>c in _)
  "

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<unlhd>" 55)where
  Refl: "e \<unlhd> e" |
  Step: "e' \<unlhd> e \<Longrightarrow> e' \<unlhd> (LET x = b in e)"


definition abstract_send_sites :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> var set" where
  "abstract_send_sites \<A> x\<^sub>c \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> {x\<^sub>y | x\<^sub>y x\<^sub>s\<^sub>c x\<^sub>e e' x\<^sub>m . 
    (LET x\<^sub>y = SYNC x\<^sub>e in e') \<unlhd> e \<and> 
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
    {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
  }"

definition abstract_recv_sites :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> var set" where
  "abstract_recv_sites \<A> x\<^sub>c \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> {x\<^sub>y | x\<^sub>y x\<^sub>r\<^sub>c x\<^sub>e e'. 
    (LET x\<^sub>y = SYNC x\<^sub>e in e') \<unlhd> e \<and> 
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e \<and>
    \<C> x\<^sub>c \<subseteq> \<V> x\<^sub>y
  }"

definition abstract_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var set \<Rightarrow> control_path set" where 
  "abstract_paths \<A> sites \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow>  {\<pi>\<^sub>y;;x\<^sub>y | \<pi>\<^sub>y x\<^sub>y . 
    (x\<^sub>y \<in> sites) \<and> \<V> \<tturnstile> (\<pi>\<^sub>y;;x\<^sub>y) \<triangleleft> e
  }" 

definition abstract_send_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path set" where 
  "abstract_send_paths \<A> x\<^sub>c \<equiv> abstract_paths \<A> (abstract_send_sites \<A> x\<^sub>c)"

definition abstract_recv_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path set" where 
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
