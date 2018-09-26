theory Dynamic_Communication
  imports Main Syntax Dynamic_Semantics
begin

inductive is_send_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    trpl \<pi>y = Some (\<langle>Let xy (Sync xe) en; env; \<kappa>\<rangle>) \<Longrightarrow>
    env xe = Some (VClsr (SendEvt xsc xm) enve) \<Longrightarrow>
    enve xsc = Some (VChn c) \<Longrightarrow>
    is_send_path trpl c \<pi>y
  "

inductive is_recv_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    trpl \<pi>y = Some (\<langle>Let xy (Sync xe) en; env; \<kappa>\<rangle>) \<Longrightarrow>
    env xe = Some (VClsr (RecvEvt xrc) enve) \<Longrightarrow>
    enve xrc = Some (VChn c) \<Longrightarrow>
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


inductive 
  dynamic_built_on_chan_var :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> var \<Rightarrow> bool" and
  dynamic_built_on_chan_prim :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> prim \<Rightarrow> bool" and
  dynamic_built_on_chan_bound_exp :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> bound_exp \<Rightarrow> bool" and
  dynamic_built_on_chan_exp :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> exp \<Rightarrow> bool" 
where
  Chan: "
    \<rho> x = Some (VChn c) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |
  Closure: "
    dynamic_built_on_chan_prim \<rho>' c p \<Longrightarrow>
    \<rho> x = Some (VClsr p \<rho>') \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |


  Send_Evt: "
    dynamic_built_on_chan_var \<rho> c xSC \<or> dynamic_built_on_chan_var \<rho> c xM \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (SendEvt xSC xM)
  " |
  Recv_Evt: "
    dynamic_built_on_chan_var \<rho> c xRC \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (RecvEvt xRC)
  " |
  Pair: "
    dynamic_built_on_chan_var \<rho> c x1 \<or> dynamic_built_on_chan \<rho> c x2 \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Pair x1 x2)
  " |
  Left: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Lft xSum)
  " |
  Right: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Rght xSum)
  " |
  Abs: "
    dynamic_built_on_chan_exp \<rho>' c e \<Longrightarrow>
    dynamic_built_on_chan_prim \<rho> c (Abs f x e)
  " |

  Prim: "
    dynamic_built_on_chan_prim \<rho> c p \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Prim p)
  " |
  Spawn: "
    dynamic_built_on_chan_exp \<rho> c eCh \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Spwn eCh)
  " |
  Sync: "
    dynamic_built_on_chan_var \<rho> c xY \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Sync xY)
  " |
  Fst: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Fst xP)
  " |
  Snd: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Snd xP)
  " |
  Case: "
    dynamic_built_on_chan_var \<rho> c xS \<or> 
    dynamic_built_on_chan_exp \<rho> c eL \<or> dynamic_built_on_chan_exp \<rho> c eR \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (Case xS xL eL xR eR)
  " |
  App: "
    dynamic_built_on_chan_var \<rho> c f \<or>
    dynamic_built_on_chan_var \<rho> c xA \<Longrightarrow>
    dynamic_built_on_chan_bound_exp \<rho> c (App f xA)
  " |

  Result: "
    dynamic_built_on_chan_var \<rho> c x \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (Rslt x)
  " |
  Let: "
    dynamic_built_on_chan_bound_exp \<rho> c b \<or> dynamic_built_on_chan_exp \<rho> c e \<Longrightarrow>
    dynamic_built_on_chan_exp \<rho> c (Let x b e)
  "




end