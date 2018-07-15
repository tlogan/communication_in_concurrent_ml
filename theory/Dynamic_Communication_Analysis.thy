theory Dynamic_Communication_Analysis
  imports Main Syntax Dynamic_Semantics
begin

inductive is_send_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    trpl \<pi>y = Some (\<langle>LET xy = SYNC xe in en; env; \<kappa>\<rangle>) \<Longrightarrow>
    env xe = Some (VClosure (Send_Evt xsc xm) enve) \<Longrightarrow>
    enve xsc = Some (VChan c) \<Longrightarrow>
    is_send_path trpl c \<pi>y
  "

inductive is_recv_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    trpl \<pi>y = Some (\<langle>LET xy = SYNC xe in en; env; \<kappa>\<rangle>) \<Longrightarrow>
    env xe = Some (VClosure (Recv_Evt xrc) enve) \<Longrightarrow>
    enve xrc = Some (VChan c) \<Longrightarrow>
    is_recv_path trpl c \<pi>y
  "

inductive every_two  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  intro: "
    (\<forall> \<pi>1 \<pi>2 .
      P \<pi>1 \<longrightarrow>
      P \<pi>2 \<longrightarrow>
      R \<pi>1 \<pi>2
    ) \<Longrightarrow>
    every_two P R
  "

inductive ordered :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  left: "prefix \<pi>1 \<pi>2 \<Longrightarrow> ordered \<pi>1 \<pi>2" |
  right: "prefix \<pi>2 \<pi>1 \<Longrightarrow> ordered \<pi>1 \<pi>2"

inductive one_shot :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    every_two (is_send_path trpl c) op= \<Longrightarrow> 
    one_shot trpl c
  "

inductive fan_out :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    every_two (is_send_path trpl c) ordered \<Longrightarrow>
    fan_out trpl c
  "
  
inductive fan_in :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    every_two (is_recv_path trpl c) ordered \<Longrightarrow> 
    fan_in trpl c
  "

inductive one_to_one :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    fan_out trpl c \<Longrightarrow>
    fan_in trpl c \<Longrightarrow> 
    one_to_one trpl c
  "


end