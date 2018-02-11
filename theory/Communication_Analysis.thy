theory Communication_Analysis
  imports Main Syntax Semantics Abstract_Value_Flow_Analysis
begin

definition send_paths :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_paths \<E> c \<equiv> {\<pi>\<^sub>y ;; `x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e e \<kappa> \<rho> x\<^sub>s\<^sub>c x\<^sub>m \<rho>\<^sub>e. 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e; \<rho>; \<kappa>\<rangle>) \<and>
    \<rho> x\<^sub>e = Some \<lbrace>Send_Evt x\<^sub>s\<^sub>c x\<^sub>m, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>s\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e; \<rho>(x\<^sub>y \<mapsto> \<lbrace>\<rbrace>); \<kappa>\<rangle>)
  }"

definition recv_paths :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_paths \<E> c \<equiv> {\<pi>\<^sub>y ;; `x\<^sub>y | \<pi>\<^sub>y x\<^sub>y x\<^sub>e e \<kappa> \<rho> x\<^sub>r\<^sub>c \<rho>\<^sub>e \<omega>. 
    \<E> \<pi>\<^sub>y = Some (\<langle>LET x\<^sub>y = SYNC x\<^sub>e in e; \<rho>; \<kappa>\<rangle>) \<and> 
    \<rho> x\<^sub>e = Some \<lbrace>Recv_Evt x\<^sub>r\<^sub>c, \<rho>\<^sub>e\<rbrace> \<and> 
    \<rho>\<^sub>e x\<^sub>r\<^sub>c = Some \<lbrace>c\<rbrace> \<and>
    \<E> (\<pi>\<^sub>y;;`x\<^sub>y) = Some (\<langle>e; \<rho>(x\<^sub>y \<mapsto> \<omega>); \<kappa>\<rangle>)
  }"


(*
fun proc_legacy' where 
  "proc_legacy' [] = []" |
  "proc_legacy' (.x # xs) = (.x # xs)" |
  "proc_legacy' (_ # xs) = proc_legacy' xs"

fun proc_legacy :: "control_path \<Rightarrow> control_path" where
  "proc_legacy \<pi> = rev (proc_legacy' (rev \<pi>))"
*)


inductive same_proc :: "control_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "\<cong>" 55) where
  Lin[simp]: "
    \<lbrakk>
      ``\<pi>\<^sub>1``; ``\<pi>\<^sub>2``
    \<rbrakk> \<Longrightarrow>
    \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2
  " |
  Cons[simp]: "
    \<lbrakk>
      \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2
    \<rbrakk> \<Longrightarrow>
    l # \<pi>\<^sub>1 \<cong> l # \<pi>\<^sub>2 
  "

fun proc_spawn' :: "control_path \<Rightarrow> (control_label list) \<Rightarrow> control_path" where
  "proc_spawn' [] r = rev r" |
  "proc_spawn' (.x # \<pi>) r = proc_spawn' \<pi> []" |
  "proc_spawn' (l # \<pi>) r = proc_spawn' \<pi> (l # r)"

fun proc_spawn :: "control_path \<Rightarrow> control_path" where
  "proc_spawn \<pi> = proc_spawn' \<pi> []"


definition noncompetitive  :: "control_path set \<Rightarrow> bool" where
  "noncompetitive \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 .
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
  )"

definition exclusive :: "control_path set \<Rightarrow> bool"  where
  "exclusive \<T> \<equiv> (\<forall> \<pi>\<^sub>1 \<pi>\<^sub>2 . 
    \<pi>\<^sub>1 \<in> \<T> \<longrightarrow> 
    \<pi>\<^sub>2 \<in> \<T> \<longrightarrow>
    \<pi>\<^sub>1 = \<pi>\<^sub>2 \<or> (\<pi>\<^sub>1 \<cong> \<pi>\<^sub>2 \<and> \<not>(prefix (proc_spawn \<pi>\<^sub>1) (proc_spawn \<pi>\<^sub>1)))
  )"


definition one_shot :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_shot \<E> c \<equiv> exclusive (send_paths \<E> c) \<and> exclusive (recv_paths \<E> c)"


definition one_to_one :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "one_to_one \<E> c \<equiv> noncompetitive (send_paths \<E> c) \<and> noncompetitive (recv_paths \<E> c)"
  
definition fan_out :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_out \<E> c \<equiv> noncompetitive (send_paths \<E> c)"
  
definition fan_in :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "fan_in \<E> c \<equiv> noncompetitive (recv_paths \<E> c)"


end