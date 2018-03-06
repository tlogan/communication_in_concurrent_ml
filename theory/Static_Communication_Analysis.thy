theory Static_Communication_Analysis
  imports Main Syntax Runtime_Semantics Static_Semantics Runtime_Communication_Analysis
begin

fun proc_legacy_unsafe :: "control_path \<Rightarrow> control_path" where
  "proc_legacy_unsafe [] = []" |
  "proc_legacy_unsafe (.l # \<pi>) = (*maybe just [] instead?  *) `l # []" |
  "proc_legacy_unsafe (`l # \<pi>) = `l # (proc_legacy_unsafe \<pi>)" |
  "proc_legacy_unsafe (\<upharpoonleft>\<bar>l # \<pi>) = \<upharpoonleft>\<bar>l # (proc_legacy_unsafe \<pi>)" |
  "proc_legacy_unsafe (\<upharpoonleft>:l # \<pi>) = \<upharpoonleft>:l # (proc_legacy_unsafe \<pi>)" |
  "proc_legacy_unsafe (\<upharpoonleft>l # \<pi>) = \<upharpoonleft>l # (proc_legacy_unsafe \<pi>)" |
  "proc_legacy_unsafe (\<downharpoonleft>l # \<pi>) = \<downharpoonleft>l # (proc_legacy_unsafe \<pi>)"

fun proc_legacy :: "control_path \<Rightarrow> control_path option" where
  "proc_legacy (.l # \<pi>) = Some (proc_legacy_unsafe (.l # \<pi>))" |
  "proc_legacy _ = None "


fun proc_spawn_unsafe :: "control_path \<Rightarrow> control_path" where
  "proc_spawn_unsafe [] = []" |
  "proc_spawn_unsafe (.l # \<pi>) = \<pi>" |
  "proc_spawn_unsafe (`l # \<pi>) = (proc_spawn_unsafe \<pi>)" |
  "proc_spawn_unsafe (\<upharpoonleft>\<bar>l # \<pi>) = (proc_spawn_unsafe \<pi>)" |
  "proc_spawn_unsafe (\<upharpoonleft>:l # \<pi>) = (proc_spawn_unsafe \<pi>)" |
  "proc_spawn_unsafe (\<upharpoonleft>l # \<pi>) = (proc_spawn_unsafe \<pi>)" |
  "proc_spawn_unsafe (\<downharpoonleft>l # \<pi>) = (proc_spawn_unsafe \<pi>)"


fun proc_spawn :: "control_path \<Rightarrow> control_path option" where
  "proc_spawn (.l # \<pi>) = Some (proc_spawn_unsafe (.l # \<pi>))" |
  "proc_spawn _ = None"


function two_paths_exclusive' :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  "two_paths_exclusive' \<pi>\<^sub>1 \<pi>\<^sub>2 = (
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<or>
    (case ((proc_legacy \<pi>\<^sub>1), (proc_legacy \<pi>\<^sub>2)) of 
      (Some \<pi>\<^sub>1l, Some \<pi>\<^sub>2l) \<Rightarrow> \<not> (two_paths_ordered \<pi>\<^sub>1l \<pi>\<^sub>2l) |
      _ \<Rightarrow> False
    ) \<or>
    (case ((proc_legacy \<pi>\<^sub>1), (proc_legacy \<pi>\<^sub>2), (proc_spawn \<pi>\<^sub>1), (proc_spawn \<pi>\<^sub>2)) of 
      (Some \<pi>\<^sub>1l, Some \<pi>\<^sub>2l, Some \<pi>\<^sub>1w, Some \<pi>\<^sub>2w) \<Rightarrow> 
          \<pi>\<^sub>1l = \<pi>\<^sub>2l \<and> (two_paths_exclusive' \<pi>\<^sub>1w \<pi>\<^sub>2w) |
      _ \<Rightarrow> False
    )
  )" 
apply auto[1]
by auto


inductive two_paths_exclusive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  Refl: "
    two_paths_exclusive \<pi> \<pi>
  " |
  Base: "
    \<lbrakk>
      (proc_legacy \<pi>\<^sub>1) = Some \<pi>\<^sub>1l;
      (proc_legacy \<pi>\<^sub>2) = Some \<pi>\<^sub>2l;

      \<not> (two_paths_ordered \<pi>\<^sub>1l \<pi>\<^sub>2l)
    \<rbrakk> \<Longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  " |
  Induc: "
    \<lbrakk>
      (proc_legacy \<pi>\<^sub>1) = Some \<pi>\<^sub>1l;
      (proc_legacy \<pi>\<^sub>2) = Some \<pi>\<^sub>2l;
      \<pi>\<^sub>1l = \<pi>\<^sub>2l;

      (proc_spawn \<pi>\<^sub>1) = Some \<pi>\<^sub>1w;
      (proc_spawn \<pi>\<^sub>2) = Some \<pi>\<^sub>2w;
      two_paths_exclusive \<pi>\<^sub>1w \<pi>\<^sub>2w

(*
      exclusive (
  .x .z
  .x .y
)
*)
    \<rbrakk> \<Longrightarrow>
    two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
  "


lemma two_paths_exclusive_preserved_under_pop: "
  two_paths_exclusive (l # \<pi>\<^sub>1) (l # \<pi>\<^sub>2) \<Longrightarrow> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
"
 apply (erule two_paths_exclusive.cases; auto)
  apply (simp add: two_paths_exclusive.Refl)
  apply (cases l; auto)
   apply (simp add: two_paths_ordered_def)
  apply (cases l; auto)
done

lemma two_paths_exclusive_and_ordered_implies_equal': "
  \<forall> \<pi>\<^sub>2 .two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2
"
 apply (simp add: two_paths_ordered_def)
 apply (induct \<pi>\<^sub>1; auto; case_tac \<pi>\<^sub>2; auto)
 apply (erule two_paths_exclusive.cases; auto)
  using two_paths_exclusive_preserved_under_pop apply blast
 apply (erule two_paths_exclusive.cases; auto)
  using two_paths_exclusive_preserved_under_pop apply blast
done


lemma two_paths_exclusive_and_ordered_implies_equal: "
  two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2
"
by (simp add: two_paths_exclusive_and_ordered_implies_equal')


lemma empty_not_two_paths_exclusive: "
  two_paths_exclusive [] (l # \<pi>) \<Longrightarrow> False
"
 apply (erule two_paths_exclusive.cases; auto)
done

lemma not_two_paths_exclusive_with_extension: "
  \<not> (two_paths_exclusive (\<pi> ;; l) \<pi>)
"
 apply (induct \<pi>; auto)
 apply (erule two_paths_exclusive.cases; auto)
  using two_paths_exclusive_preserved_under_pop
 apply blast
done

lemma two_paths_exclusive_commut: "
  two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> two_paths_exclusive \<pi>\<^sub>2 \<pi>\<^sub>1  
"
 apply (erule two_paths_exclusive.induct; auto?)
  apply (simp add: two_paths_exclusive.Refl)
  using Base two_paths_ordered_commut apply blast
  apply (simp add: Induc)
done


lemma two_paths_exclusive_and_unordered_implies_exclusive_or_prefix_under_backtrack: "
  two_paths_exclusive (\<pi>\<^sub>1 ;; l) \<pi>\<^sub>2 \<Longrightarrow>
  \<not> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow>  \<not> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
  two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2
"
 apply (erule two_paths_exclusive.cases; auto)
 apply ((case_tac \<pi>\<^sub>1; auto; case_tac a; auto), (simp add: Base))
sorry

lemma not_exclusive_with_process_split': "
  \<forall> x . two_paths_exclusive (\<pi> ;; .x) (\<pi> ;; `x) \<longrightarrow> False
"
 apply (induct \<pi>; auto)
 apply (erule two_paths_exclusive.cases; auto)
 using two_paths_exclusive_preserved_under_pop apply blast
done

lemma not_exclusive_with_process_split: "
  \<not> two_paths_exclusive (\<pi> ;; .x) (\<pi> ;; `x)
"
using not_exclusive_with_process_split' by auto

definition two_paths_noncompetitive :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" where
  "two_paths_noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 = (two_paths_ordered \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> two_paths_exclusive \<pi>\<^sub>1 \<pi>\<^sub>2)"


definition all_noncompetitive  :: "(control_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "all_noncompetitive P \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    P \<pi>\<^sub>1 \<longrightarrow>
    P \<pi>\<^sub>2 \<longrightarrow>
    two_paths_noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
  )"

definition all_exclusive :: "(control_path \<Rightarrow> bool) \<Rightarrow> bool"  where
  "all_exclusive P\<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 . 
    P \<pi>\<^sub>1 \<longrightarrow> 
    P \<pi>\<^sub>2 \<longrightarrow>
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


definition static_one_shot :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_shot \<A> x\<^sub>c \<equiv> all_exclusive (is_static_send_path \<A> x\<^sub>c) \<and> all_exclusive (is_static_recv_path \<A> x\<^sub>c)"

definition static_one_to_one :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_one_to_one \<A> x\<^sub>c \<equiv> all_noncompetitive (is_static_send_path \<A> x\<^sub>c) \<and> all_noncompetitive (is_static_recv_path \<A> x\<^sub>c)"

definition static_fan_out :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_out \<A> x\<^sub>c \<equiv> all_noncompetitive (is_static_send_path \<A> x\<^sub>c)"

definition static_fan_in :: "(abstract_value_env \<times> abstract_value_env \<times> exp) \<Rightarrow> var \<Rightarrow> bool" where
  "static_fan_in \<A> x\<^sub>c \<equiv> all_noncompetitive (is_static_recv_path \<A> x\<^sub>c)"


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
