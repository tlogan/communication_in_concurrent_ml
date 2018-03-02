theory Abstract_Communication_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis Communication_Analysis
begin



fun proc_legacy :: "control_path \<Rightarrow> control_path" where
  "proc_legacy [] = []" |
  "proc_legacy (.l # \<pi>) = `l # []" |
  "proc_legacy (`l # \<pi>) = `l # (proc_legacy \<pi>)" |
  "proc_legacy (\<upharpoonleft>\<bar>l # \<pi>) = \<upharpoonleft>\<bar>l # (proc_legacy \<pi>)" |
  "proc_legacy (\<upharpoonleft>:l # \<pi>) = \<upharpoonleft>:l # (proc_legacy \<pi>)" |
  "proc_legacy (\<upharpoonleft>l # \<pi>) = \<upharpoonleft>l # (proc_legacy \<pi>)" |
  "proc_legacy (\<downharpoonleft>l # \<pi>) = \<downharpoonleft>l # (proc_legacy \<pi>)"

fun proc_spawn :: "control_path \<Rightarrow> control_path" where
  "proc_spawn [] = []" |
  "proc_spawn (.l # \<pi>) = \<pi>" |
  "proc_spawn (`l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<upharpoonleft>\<bar>l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<upharpoonleft>:l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<upharpoonleft>l # \<pi>) = (proc_spawn \<pi>)" |
  "proc_spawn (\<downharpoonleft>l # \<pi>) = (proc_spawn \<pi>)"

inductive two_paths_exclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  Base: "
    \<lbrakk>
      \<not> (two_paths_ordered (proc_legacy \<pi>\<^sub>1) (proc_legacy \<pi>\<^sub>2))
    \<rbrakk> \<Longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Induc: "
    \<lbrakk>
      (proc_legacy \<pi>\<^sub>1) = (proc_legacy \<pi>\<^sub>2);
      two_paths_exclusive (proc_spawn \<pi>\<^sub>1) (proc_spawn \<pi>\<^sub>1)
    \<rbrakk> \<Longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


(*
lemma two_paths_exclusive_preserved_under_seq_cons: "
  two_paths_exclusive \<pi> \<pi>' \<Longrightarrow> two_paths_exclusive (`x # \<pi>) (`x # \<pi>')
"
sorry

lemma two_paths_exclusive_preserved_under_up_cons: "
  two_paths_exclusive \<pi> \<pi>' \<Longrightarrow> two_paths_exclusive (\<upharpoonleft>x # \<pi>) (\<upharpoonleft>x # \<pi>')
"
sorry

lemma two_paths_exclusive_preserved_under_down_cons: "
  two_paths_exclusive \<pi> \<pi>' \<Longrightarrow> two_paths_exclusive (\<downharpoonleft>x # \<pi>) (\<downharpoonleft>x # \<pi>')
"
sorry
*)

definition two_paths_noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  "two_paths_noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 = (two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2)"

(*
lemma "
  \<forall> \<pi>\<^sub>b \<pi>\<^sub>b' . two_paths_noncompetitive \<pi>\<^sub>b \<pi>\<^sub>b' \<longrightarrow>
  \<not> prefix \<pi>\<^sub>b (\<pi> @ \<pi>\<^sub>b') \<longrightarrow> \<not> prefix (\<pi> @ \<pi>\<^sub>b') \<pi>\<^sub>b \<longrightarrow>
  two_paths_exclusive \<pi>\<^sub>b (\<pi> @ \<pi>\<^sub>b')
"
 apply (induct \<pi>; auto)
  apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def)
  apply (drule_tac x = \<pi>\<^sub>b in spec; auto?)
  apply (drule_tac x = \<pi>\<^sub>b' in spec; auto?)
  apply (case_tac \<pi>\<^sub>b; auto)
sorry

theorem double_append_exclusive: "
  (\<forall> \<pi>\<^sub>a' \<pi>\<^sub>b \<pi>\<^sub>b'.
    two_paths_noncompetitive  \<pi>\<^sub>a \<pi>\<^sub>a' \<longrightarrow> two_paths_noncompetitive \<pi>\<^sub>b \<pi>\<^sub>b' \<longrightarrow>
    \<not> prefix (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b') \<longrightarrow> \<not> prefix (\<pi>\<^sub>a' @ \<pi>\<^sub>b') (\<pi>\<^sub>a @ \<pi>\<^sub>b) \<longrightarrow>
    two_paths_exclusive (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b')
  )
"
 apply (induct \<pi>\<^sub>a; auto; simp?)
  apply (case_tac \<pi>\<^sub>a'; auto)
   apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def; auto)
  apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def; auto)
    
sorry


theorem noncompetitive_preserved_under_double_append: "
 two_paths_noncompetitive  \<pi>\<^sub>a \<pi>\<^sub>a' \<Longrightarrow> two_paths_noncompetitive \<pi>\<^sub>b \<pi>\<^sub>b' \<Longrightarrow> two_paths_noncompetitive (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b')
"
 apply (simp add: two_paths_noncompetitive_def two_paths_ordered_def; blast?)
 apply (case_tac "prefix (\<pi>\<^sub>a @ \<pi>\<^sub>b) (\<pi>\<^sub>a' @ \<pi>\<^sub>b')"; blast?) 
 apply (case_tac" prefix (\<pi>\<^sub>a' @ \<pi>\<^sub>b') (\<pi>\<^sub>a @ \<pi>\<^sub>b)"; blast?)
 apply (rule disjI2, rule disjI2) 
 apply (simp add: double_append_exclusive two_paths_noncompetitive_def two_paths_ordered_def)
done
*)

definition set_noncompetitive  :: "control_path set \<Rightarrow> bool" where
  "set_noncompetitive \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    two_paths_noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  )"

definition set_exclusive :: "control_path set \<Rightarrow> bool"  where
  "set_exclusive \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 . 
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow> 
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
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

definition abstract_send_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path set" where
  "abstract_send_paths \<A> x\<^sub>c \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> {\<pi>\<^sub>y;;`x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>s\<^sub>c x\<^sub>m e\<^sub>n. 
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<and>
    {^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m} \<subseteq> \<V> x\<^sub>e \<and>
    {^\<lparr>\<rparr>} \<subseteq> \<V> x\<^sub>y \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
  }"

definition abstract_recv_paths :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> control_path set" where
  "abstract_recv_paths \<A> x\<^sub>c \<equiv> case \<A> of (\<V>, \<C>, e) \<Rightarrow> {\<pi>\<^sub>y;;`x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e x\<^sub>r\<^sub>c e\<^sub>n \<omega>. 
    \<V> \<turnstile> e \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<and>
    ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<and>
    {^Recv_Evt x\<^sub>r\<^sub>c} \<subseteq> \<V> x\<^sub>e \<and>
    {|\<omega>|} \<subseteq> \<V> x\<^sub>y
  }"


definition abstract_one_shot :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_one_shot \<A> x\<^sub>c \<equiv> set_exclusive (abstract_send_paths \<A> x\<^sub>c) \<and> set_exclusive (abstract_recv_paths \<A> x\<^sub>c)"

definition abstract_one_to_one :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_one_to_one \<A> x\<^sub>c \<equiv> set_noncompetitive (abstract_send_paths \<A> x\<^sub>c) \<and> set_noncompetitive (abstract_recv_paths \<A> x\<^sub>c)"

definition abstract_fan_out :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_fan_out \<A> x\<^sub>c \<equiv> set_noncompetitive (abstract_send_paths \<A> x\<^sub>c)"

definition abstract_fan_in :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "abstract_fan_in \<A> x\<^sub>c \<equiv> set_noncompetitive (abstract_recv_paths \<A> x\<^sub>c)"


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
