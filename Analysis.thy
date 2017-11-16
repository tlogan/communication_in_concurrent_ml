theory Analysis
  imports Main Syntax
begin

datatype abstract_value = Chan var | Unit | Prim prim

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"

fun result_var :: "exp \<Rightarrow> var" where
  "result_var (RESULT x) = x" |
  "result_var (LET _ = _ in e) = result_var e"

inductive val_env_accept :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>" 55) where
  Result: "
    \<rho> \<Turnstile> (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk> {Unit} \<subseteq> (\<rho> x); \<rho> \<Turnstile> e \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Abs : "
    \<lbrakk> 
      {Prim (P_Abs f' x' e')} \<subseteq> (\<rho> f');
      \<rho> \<Turnstile> e';
      {Prim (P_Abs f' x' e')} \<subseteq> (\<rho> x);
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = B_Prim (P_Abs f' x' e') in e)
  " |
  Let_Pair : "
    \<lbrakk> 
      {Prim (P_Pair x1 x2)} \<subseteq> (\<rho> x);
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = B_Prim (P_Pair x1 x2) in e)
  " |
  Let_Left : "
    \<lbrakk> 
      {Prim (P_Left x_p)} \<subseteq> (\<rho> x);
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = B_Prim (P_Left x_p) in e)
  " |
  Let_Right : "
    \<lbrakk> 
      {Prim (P_Right x_p)} \<subseteq> (\<rho> x);
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = B_Prim (P_Right x_p) in e)
  " |
  Let_Send_Evt : "
    \<lbrakk> 
      {Prim (P_Send_Evt x_ch x_m)} \<subseteq> (\<rho> x);
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = B_Prim (P_Send_Evt x_ch x_m) in e)
  " |
  Let_Recv_Evt : "
    \<lbrakk> 
      {Prim (P_Recv_Evt x_ch)} \<subseteq> (\<rho> x);
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = B_Prim (P_Recv_Evt x_ch) in e)
  " |
  Let_Case: "
    \<lbrakk>
      \<And> x_l' . (Prim (P_Left x_l')) \<in> \<rho> x_sum \<Longrightarrow> 
        (\<rho> x_l' \<subseteq> \<rho> x_l) \<and> (\<rho> (result_var e_l) \<subseteq> \<rho> x) \<and> \<rho> \<Turnstile> e_l;
      \<And> x_r' :: var . Prim (P_Right x_r') \<in> \<rho> x_sum \<Longrightarrow>
        \<rho> x_r' \<subseteq> \<rho> x_r \<and> \<rho> (result_var e_r) \<subseteq> \<rho> x \<and> \<rho> \<Turnstile> e_r
    \<rbrakk>\<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = CASE x_sum LEFT x_l |> e_l RIGHT x_r |> e_r in e)
  " |
  Let_Fst: "
    \<lbrakk> 
      \<And> x1 x2. Prim (P_Pair x1 x2) \<in> (\<rho> x_p) \<Longrightarrow> \<rho> x1 \<subseteq> \<rho> x; 
      \<rho> \<Turnstile> e 
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = FST x_p in e)
  " |
  Let_Snd: "
    \<lbrakk> 
      \<And> x1 x2 . Prim (P_Pair x1 x2) \<in> (\<rho> x_p) \<Longrightarrow> \<rho> x2 \<subseteq> \<rho> x; 
      \<rho> \<Turnstile> e
    \<rbrakk> \<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = SND x_p in e)
  " |
  Let_App: "
    \<lbrakk>
      \<And> x' e' . Prim (P_Abs _ x' e') \<in> \<rho> x_f \<Longrightarrow>
        \<rho> x_a \<subseteq> \<rho> x' \<and>
        \<rho> (result_var e') \<subseteq> \<rho> x
      ;
      \<rho> \<Turnstile> e
    \<rbrakk>\<Longrightarrow> 
    \<rho> \<Turnstile> (LET x = APP x_f x_a in e)
  " |
  Let_Sync  : "
    \<lbrakk>
      \<And> x_ch x_m . Prim (P_Send_Evt x_ch x_m) \<in> \<rho> x_evt \<Longrightarrow> 
        {Unit} \<subseteq> \<rho> x;
      \<And> x_ch . Prim (P_Recv_Evt x_ch) \<in> \<rho> x_evt \<Longrightarrow>
        (\<Union> x'. {v . \<exists> x_m . v \<in> \<rho> x_m \<and> Prim (P_Send_Evt x_ch x_m) \<in> \<rho> x'}) \<subseteq> \<rho> x;
      \<rho> \<Turnstile> e
    \<rbrakk>\<Longrightarrow>  
    \<rho> \<Turnstile> (LET x = SYNC x_evt in e)
  " |
  Let_Chan: "
    \<lbrakk>
      {Chan x} \<subseteq> \<rho> x;
      \<rho> \<Turnstile> e
    \<rbrakk>\<Longrightarrow>  
    \<rho> \<Turnstile> (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    \<lbrakk>
      {Unit} \<subseteq> \<rho> x;
      \<rho> \<Turnstile> e_child;
      \<rho> \<Turnstile> e
    \<rbrakk>\<Longrightarrow>  
    \<rho> \<Turnstile> (LET x = SPAWN e_child in e)
  "


type_synonym abstract_path = "(var + unit) list"

inductive path_sub_accept :: "abstract_value_env \<Rightarrow> abstract_path \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "path_sub_accept \<rho> [Inl x] (RESULT x)" |
  Let_Unit: "
    path_sub_accept \<rho> \<pi> e \<Longrightarrow> 
    path_sub_accept \<rho> ((Inl x) # \<pi>) (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Prim: "
    path_sub_accept \<rho> \<pi> e \<Longrightarrow> 
    path_sub_accept \<rho> ((Inl x) # \<pi>) (LET x = B_Prim p in e)
  " |
  Let_Case_Left: "
    \<lbrakk>
      path_sub_accept \<rho> \<pi>_l e_l; 
      path_sub_accept \<rho> \<pi> e 
    \<rbrakk>\<Longrightarrow> 
    path_sub_accept \<rho> (\<pi>_l @ ((Inl x) # \<pi>)) (LET x = CASE x_sum LEFT x_l |> e_l RIGHT _ |> _ in e)
  " |
  Let_Case_Right: "
    \<lbrakk>
      path_sub_accept \<rho> \<pi>_r e_r;
      path_sub_accept \<rho> \<pi> e
    \<rbrakk> \<Longrightarrow> 
    path_sub_accept \<rho> (\<pi>_r @ ((Inl x) # \<pi>)) (LET x = CASE x_sum LEFT _ |> _ RIGHT x_r |> e_r in e)
  " |
  Let_Fst: "
    path_sub_accept \<rho> \<pi> e \<Longrightarrow> 
    path_sub_accept \<rho> ((Inl x) # \<pi>) (LET x = FST _ in e)
  " |
  Let_Snd: "
    path_sub_accept \<rho> \<pi> e \<Longrightarrow> 
    path_sub_accept \<rho> ((Inl x) # \<pi>) (LET x = SND _ in e)
  " |
  Let_App: "
    \<lbrakk>
      (Prim (P_Abs f' x' e' )) \<in> (\<rho> x_f);
       path_sub_accept (\<rho>(x' := (\<rho> x') \<inter> (\<rho> x_a))) \<pi>' e'
    \<rbrakk>\<Longrightarrow> 
    path_sub_accept \<rho> (\<pi>' @ ((Inl x) # \<pi>)) (LET x = APP x_f x_a in e)
  " |
  Let_Sync: "
   path_sub_accept \<rho> \<pi> e \<Longrightarrow>
   path_sub_accept \<rho> (Inl x # \<pi>) (LET x = SYNC x_evt in e)
  " |
  Let_Chan: "
    path_sub_accept \<rho> \<pi> e \<Longrightarrow>
    path_sub_accept \<rho> (Inl x # \<pi>) (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Spawn_Parent: " 
    path_sub_accept \<rho> \<pi> e \<Longrightarrow>
    path_sub_accept \<rho> (Inl x # \<pi>) (LET x = SPAWN _ in e)
  " |
  Let_Spawn_Child: " 
    path_sub_accept \<rho> \<pi> e_child \<Longrightarrow>
    path_sub_accept \<rho> (Inr () # \<pi>) (LET x = SPAWN e_child in _)
  " 


(*  What's the way to show that the number of acceptable paths \<le> 1 ?*)

definition path_accept :: "abstract_path \<Rightarrow> exp \<Rightarrow> bool" where
  "path_accept \<pi> e \<equiv> (\<exists> \<rho> . \<rho> \<Turnstile> e \<and> path_sub_accept \<rho> \<pi> e)"

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" where
  Refl: "subexp e e" |
  Step: "subexp e' e \<Longrightarrow> subexp e' (LET _ = _ in e)"

definition send_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "send_sites c e = {x . \<exists> y e' \<rho> z. 
    subexp (LET x = SYNC y in e') e \<and> 
    val_env_accept \<rho> e \<and> 
    Prim (P_Send_Evt c z) \<in> (\<rho> y)
  }"

definition recv_sites :: "var \<Rightarrow> exp \<Rightarrow> var set" where
  "recv_sites c e = {x . \<exists> y e' \<rho>. 
    subexp (LET x = SYNC y in e') e \<and> 
    val_env_accept \<rho> e \<and> 
    Prim (P_Recv_Evt c) \<in> (\<rho> y)
  }"

definition paths :: "var set \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> abstract_path set" where 
  "paths sites c e = {path @ [Inl x] | path x . 
    (x \<in> sites) \<and>  path_accept (path @ [Inl x]) e
  }" 

definition send_paths where 
  "send_paths c e = paths (send_sites c e) c e"

definition recv_paths where 
  "recv_paths c e = paths (recv_sites c e) c e"


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