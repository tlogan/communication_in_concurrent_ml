theory Dynamic_Communication_Analysis
  imports Main Syntax Dynamic_Semantics
begin

inductive is_send_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro: "
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
    \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<Longrightarrow>
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c) \<Longrightarrow>
    is_send_path \<E> c \<pi>\<^sub>y
  "

inductive is_recv_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  Intro: "
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<Longrightarrow>
    \<rho> x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e) \<Longrightarrow>
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c) \<Longrightarrow>
    is_recv_path \<E> c \<pi>\<^sub>y
  "


inductive every_two_dynamic_paths  :: "(control_path \<Rightarrow> bool) \<Rightarrow> (control_path \<Rightarrow> control_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "
    (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
      P \<pi>\<^sub>1 \<longrightarrow>
      P \<pi>\<^sub>2 \<longrightarrow>
      R \<pi>\<^sub>1 \<pi>\<^sub>2
    ) \<Longrightarrow>
    every_two_dynamic_paths P R
  "

fun ordered where
  "ordered \<pi>\<^sub>1 \<pi>\<^sub>2 = (prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1)"

inductive one_shot :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "
    every_two_dynamic_paths (is_send_path \<E> c) op= \<Longrightarrow> 
    one_shot \<E> c
  "


inductive one_to_one :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "
    every_two_dynamic_paths (is_send_path \<E> c) ordered \<and> every_two_dynamic_paths (is_recv_path \<E> c) ordered \<Longrightarrow> 
    one_to_one \<E> c
  "
  

inductive fan_out :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "
    every_two_dynamic_paths (is_send_path \<E> c) ordered \<Longrightarrow>
    fan_out \<E> c
  "

  
inductive fan_in :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "
    every_two_dynamic_paths (is_recv_path \<E> c) ordered \<Longrightarrow> 
    fan_in \<E> c
  "


end