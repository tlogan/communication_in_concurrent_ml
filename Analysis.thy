theory Analysis
  imports Main Syntax
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^ _" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"

fun result_var :: "exp \<Rightarrow> var" where
  "result_var (RESULT x) = x" |
  "result_var (LET _ = _ in e) = result_var e"

inductive val_env_accept :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
  Result: "
    (\<V>, \<C>) \<Turnstile> RESULT x
  " |
  Let_Unit: "
    \<lbrakk> {^\<lparr>\<rparr>} \<subseteq> \<V> x; (\<V>, \<C>) \<Turnstile> e \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = \<lparr>\<rparr> in e
  " |
  Let_Abs : "
    \<lbrakk> 
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>) \<Turnstile> e';
      {^Abs f' x' e'} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FN f' x' . e' in e
  " |
  Let_Pair : "
    \<lbrakk> 
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk> 
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk> 
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = RIGHT x\<^sub>p in e
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Case: "
    \<lbrakk>
      \<And> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<Longrightarrow> 
        (\<rho> x\<^sub>l' \<subseteq> \<rho> x\<^sub>l) \<and> (\<V> (result_var e\<^sub>l) \<subseteq> \<rho> x) \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>l
      ;
      \<And> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<Longrightarrow>
        \<rho> x\<^sub>r' \<subseteq> \<rho> x\<^sub>r \<and> \<rho> (result_var e\<^sub>r) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile> e\<^sub>r
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_Fst: "
    \<lbrakk> 
      \<And> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<Longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk> 
      \<And> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<Longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = SND x\<^sub>p in e
  " |
  Let_App: "
    \<lbrakk>
      \<And> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<Longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (result_var e') \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile> LET x = APP f x\<^sub>a in e
  " |
  Let_Sync  : "
    \<lbrakk>
      \<And> x\<^sub>c x\<^sub>m . ^Send_Evt x\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>e \<Longrightarrow> 
        {^\<lparr>\<rparr>} \<subseteq> \<V> x \<and> \<V> x_m \<subseteq> \<C> x\<^sub>c
      ;
      \<And> x\<^sub>c . ^Recv_Evt x\<^sub>c \<in> \<V> x\<^sub>e \<Longrightarrow>
        \<C> x\<^sub>c \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = SYNC x\<^sub>e in e
  " |
  Let_Chan: "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Spawn_Parent: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile> e\<^sub>c;
      (\<V>, \<C>) \<Turnstile> e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile> LET x = SPAWN e\<^sub>c in e
  "



type_synonym abstract_path = "(var + unit) list"

inductive path_sub_accept :: "abstract_value_env \<Rightarrow> abstract_path \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "path_sub_accept \<rho> [Inl x] (RESULT x)" |
  Let_Unit: "
    path_sub_accept \<V> \<pi> e \<Longrightarrow> 
    path_sub_accept \<V> (Inl x # \<pi>) (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Prim: "
    path_sub_accept \<V> \<pi> e \<Longrightarrow> 
    path_sub_accept \<V> (Inl x # \<pi>) (LET x = Prim p in e)
  " |
  Let_Case_Left: "
    \<lbrakk>
      path_sub_accept \<V> \<pi>\<^sub>l e\<^sub>l; 
      path_sub_accept \<V> \<pi> e 
    \<rbrakk>\<Longrightarrow> 
    path_sub_accept \<V> (\<pi>\<^sub>l @ (Inl x # \<pi>)) (LET x = CASE _ LEFT x\<^sub>l |> e\<^sub>l RIGHT _ |> _ in e)
  " |
  Let_Case_Right: "
    \<lbrakk>
      path_sub_accept \<V> \<pi>\<^sub>r e\<^sub>r;
      path_sub_accept \<V> \<pi> e
    \<rbrakk> \<Longrightarrow> 
    path_sub_accept \<V> (\<pi>_r @ (Inl x # \<pi>)) (LET x = CASE _ LEFT _ |> _ RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_Fst: "
    path_sub_accept \<V> \<pi> e \<Longrightarrow> 
    path_sub_accept \<V> (Inl x # \<pi>) (LET x = FST _ in e)
  " |
  Let_Snd: "
    path_sub_accept \<V> \<pi> e \<Longrightarrow> 
    path_sub_accept \<V> (Inl x # \<pi>) (LET x = SND _ in e)
  " |
  Let_App: "
    \<lbrakk>
      ^Abs f' x' e' \<in> \<V> f;
      path_sub_accept (\<V>(x' := \<V> x' \<inter> \<V> x\<^sub>a)) \<pi>' e';
      path_sub_accept \<V> \<pi> e
    \<rbrakk> \<Longrightarrow> 
    path_sub_accept \<V> (\<pi>' @ (Inl x # \<pi>)) (LET x = APP f x\<^sub>a in e)
  " |
  Let_Sync: "
   path_sub_accept \<V> \<pi> e \<Longrightarrow>
   path_sub_accept \<V> (Inl x # \<pi>) (LET x = SYNC _ in e)
  " |
  Let_Chan: "
    path_sub_accept \<V> \<pi> e \<Longrightarrow>
    path_sub_accept \<V> (Inl x # \<pi>) (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    path_sub_accept \<V> \<pi> e \<Longrightarrow>
    path_sub_accept \<V> (Inl x # \<pi>) (LET x = SPAWN _ in e)
  " |
  Let_Spawn_Child: " 
    path_sub_accept \<V> \<pi> e\<^sub>c \<Longrightarrow>
    path_sub_accept \<V> (Inr () # \<pi>) (LET x = SPAWN e\<^sub>c in _)
  " 


(*  What's the way to show that the number of acceptable paths \<le> 1 ?*)

definition path_accept :: "abstract_path \<Rightarrow> exp \<Rightarrow> bool" where
  "path_accept \<pi> e \<equiv> (\<exists> \<V> \<C> . (\<V>, \<C>) \<Turnstile> e \<and> path_sub_accept \<V> \<pi> e)"

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


definition paths :: "var set \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "paths sites c e = {path @ [Inl x] | path x . 
    (x \<in> sites) \<and>  path_accept (path @ [Inl x]) e
  }" 

definition processes :: "var set \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "processes sites c e = {\<pi> \<in> paths sites c e .
    (\<pi> @ [Inr ()]) \<in> paths sites c e \<or>
    (\<forall> \<pi>' . (\<pi> @ \<pi>') \<notin> paths sites c e)
  }" 

definition send_paths where 
  "send_paths c e = paths (send_sites c e) c e"

definition recv_paths where 
  "recv_paths c e = paths (recv_sites c e) c e"

definition exactly_one :: "abstract_path set \<Rightarrow> bool" where
  "exactly_one \<T> \<longleftrightarrow> (\<exists> p \<in> \<T> . (\<forall> p' \<in> \<T> . p = p'))"

definition empty_set :: "abstract_path set \<Rightarrow> bool" where
  "empty_set \<T> \<longleftrightarrow> (\<nexists> p . p \<in> \<T>)"

inductive one_path_max :: "abstract_path set \<Rightarrow> bool"  where
  "
    \<lbrakk>
      \<And> path . path \<in> pset \<Longrightarrow> no_path_loop path (* TO DO *)
    \<rbrakk> \<Longrightarrow>
    one_path_max pset
  "

inductive one_process_max :: "abstract_path set \<Rightarrow> bool"  where
  "
    \<lbrakk>
      \<And> path . path \<in> pset \<Longrightarrow> no_process_loop path (* TO DO *)
    \<rbrakk> \<Longrightarrow>
    one_process_max pset
  "

(*
value "one_path_max (send_paths (Var ''x'') (RESULT (Var ''x'')))"
*)

datatype topo_class = OneShot | OneToOne | FanOut | FanIn | Any

type_synonym topo_class_pair = "var \<times> topo_class"

inductive class_pair_accept :: "topo_class_pair \<Rightarrow> exp \<Rightarrow> bool" where
  OneShot: "
    one_path_max (send_paths c e) \<Longrightarrow> 
    class_pair_accept (c, OneShot) e
  " | 

  OneToOne: "
    \<lbrakk> 
      one_process_max (send_paths c e) ;
      one_process_max (recv_paths c e) 
    \<rbrakk> \<Longrightarrow> 
    class_pair_accept (c, OneToOne) e
  " | 

  FanOut: "
    \<lbrakk> 
      one_process_max (send_paths c e)
    \<rbrakk> \<Longrightarrow> 
    class_pair_accept (c, FanOut) e
  " | 

  FanIn: "
    one_process_max (receive_paths c e) \<Longrightarrow> 
    class_pair_accept (c, OneToOne) e
  " | 

  Any: "class_pair_accept (c, OneToOne) e"


type_synonym topo_class_env = "var \<Rightarrow> topo_class"

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
