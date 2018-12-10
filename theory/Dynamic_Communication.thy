theory Dynamic_Communication
  imports Main Syntax Dynamic_Semantics
begin

inductive is_send_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    pool \<pi>y = Some (\<langle>Bind xy (Sync xe) en; env; \<kappa>\<rangle>) \<Longrightarrow>
    env xe = Some (VClsr (SendEvt xsc xm) enve) \<Longrightarrow>
    enve xsc = Some (VChn c) \<Longrightarrow>
    is_send_path pool c \<pi>y
  "

inductive is_recv_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    pool \<pi>y = Some (\<langle>Bind xy (Sync xe) en; env; \<kappa>\<rangle>) \<Longrightarrow>
    env xe = Some (VClsr (RecvEvt xrc) enve) \<Longrightarrow>
    enve xrc = Some (VChn c) \<Longrightarrow>
    is_recv_path pool c \<pi>y
  "

inductive forEveryTwo  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  intro: "
    (\<forall> \<pi>1 \<pi>2 .
      P \<pi>1 \<longrightarrow>
      P \<pi>2 \<longrightarrow>
      R \<pi>1 \<pi>2
    ) \<Longrightarrow>
    forEveryTwo P R
  "

inductive ordered :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  left: "prefix \<pi>1 \<pi>2 \<Longrightarrow> ordered \<pi>1 \<pi>2" |
  right: "prefix \<pi>2 \<pi>1 \<Longrightarrow> ordered \<pi>1 \<pi>2"

inductive one_shot :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    forEveryTwo (is_send_path pool c) op= \<Longrightarrow> 
    one_shot pool c
  "

inductive fan_out :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    forEveryTwo (is_send_path pool c) ordered \<Longrightarrow>
    fan_out pool c
  "
  
inductive fan_in :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    forEveryTwo (is_recv_path pool c) ordered \<Longrightarrow> 
    fan_in pool c
  "

inductive one_to_one :: "trace_pool \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    fan_out pool c \<Longrightarrow>
    fan_in pool c \<Longrightarrow> 
    one_to_one pool c
  "


inductive 
  dynamic_built_on_chan_var :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> name \<Rightarrow> bool" and
  dynamic_built_on_chan_atom :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> atom \<Rightarrow> bool" and
  dynamic_built_on_chan_complex :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> complex \<Rightarrow> bool" and
  dynamic_built_on_chan_tm :: "(var \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> tm \<Rightarrow> bool" 
where
  Chan: "
    \<rho> x = Some (VChn c) \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |
  Closure: "
    dynamic_built_on_chan_atom \<rho>' c p \<Longrightarrow>
    \<rho> x = Some (VClsr p \<rho>') \<Longrightarrow>
    dynamic_built_on_chan_var \<rho> c x
  " |


  Send_Evt: "
    dynamic_built_on_chan_var \<rho> c xSC \<or> dynamic_built_on_chan_var \<rho> c xM \<Longrightarrow>
    dynamic_built_on_chan_atom \<rho> c (SendEvt xSC xM)
  " |
  Recv_Evt: "
    dynamic_built_on_chan_var \<rho> c xRC \<Longrightarrow>
    dynamic_built_on_chan_atom \<rho> c (RecvEvt xRC)
  " |
  Pair: "
    dynamic_built_on_chan_var \<rho> c x1 \<or> dynamic_built_on_chan \<rho> c x2 \<Longrightarrow>
    dynamic_built_on_chan_atom \<rho> c (Pair x1 x2)
  " |
  Left: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_atom \<rho> c (Lft xSum)
  " |
  Right: "
    dynamic_built_on_chan_var \<rho> c xSum \<Longrightarrow>
    dynamic_built_on_chan_atom \<rho> c (Rht xSum)
  " |
  Fun: "
    dynamic_built_on_chan_tm \<rho>' c e \<Longrightarrow>
    dynamic_built_on_chan_atom \<rho> c (Fun f x e)
  " |

  Atom: "
    dynamic_built_on_chan_atom \<rho> c p \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (Atom p)
  " |
  Spawn: "
    dynamic_built_on_chan_tm \<rho> c eCh \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (Spwn eCh)
  " |
  Sync: "
    dynamic_built_on_chan_var \<rho> c xY \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (Sync xY)
  " |
  Fst: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (Fst xP)
  " |
  Snd: "
    dynamic_built_on_chan_var \<rho> c xP \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (Snd xP)
  " |
  Case: "
    dynamic_built_on_chan_var \<rho> c xS \<or> 
    dynamic_built_on_chan_tm \<rho> c eL \<or> dynamic_built_on_chan_tm \<rho> c eR \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (Case xS xL eL xR eR)
  " |
  App: "
    dynamic_built_on_chan_var \<rho> c f \<or>
    dynamic_built_on_chan_var \<rho> c xA \<Longrightarrow>
    dynamic_built_on_chan_complex \<rho> c (App f xA)
  " |

  Result: "
    dynamic_built_on_chan_var \<rho> c x \<Longrightarrow>
    dynamic_built_on_chan_tm \<rho> c (Rslt x)
  " |
  Bind: "
    dynamic_built_on_chan_complex \<rho> c b \<or> dynamic_built_on_chan_tm \<rho> c e \<Longrightarrow>
    dynamic_built_on_chan_tm \<rho> c (Bind x b e)
  "




end
