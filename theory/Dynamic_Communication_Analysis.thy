theory Dynamic_Communication_Analysis
  imports Main Syntax Dynamic_Semantics
begin

definition is_send_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_send_path \<E> c \<pi>\<^sub>y \<equiv> (\<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<kappa> \<rho> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e.
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<and>
    \<rho> x\<^sub>e = Some (VClosure (Send_Evt x\<^sub>s\<^sub>c x\<^sub>m) \<rho>\<^sub>e) \<and> 
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some (VChan c)
  )"

definition is_recv_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  "is_recv_path \<E> c \<pi>\<^sub>y \<equiv> (\<exists> x\<^sub>y x\<^sub>e e\<^sub>n \<kappa> \<rho> x\<^sub>r\<^sub>c \<rho>\<^sub>e.
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some (VClosure (Recv_Evt x\<^sub>r\<^sub>c) \<rho>\<^sub>e) \<and> 
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some (VChan c)
  )"


definition all  :: "(control_path \<Rightarrow> bool) \<Rightarrow> (control_path \<Rightarrow> control_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "all P R \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    P \<pi>\<^sub>1 \<longrightarrow>
    P \<pi>\<^sub>2 \<longrightarrow>
    R \<pi>\<^sub>1 \<pi>\<^sub>2
  )"

fun ordered where
  "ordered \<pi>\<^sub>1 \<pi>\<^sub>2 = (prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1)"

definition one_shot :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_shot \<E> c \<equiv> all (is_send_path \<E> c) op="


definition one_to_one :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_to_one \<E> c \<equiv> all (is_send_path \<E> c) ordered \<and> all (is_recv_path \<E> c) ordered"
  

definition fan_out :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_out \<E> c \<equiv> all (is_send_path \<E> c) ordered"
  

definition fan_in :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_in \<E> c \<equiv> all (is_recv_path \<E> c) ordered"


end