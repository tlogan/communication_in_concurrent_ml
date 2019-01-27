theory Dynamic_Communication
  imports Main Syntax Dynamic_Semantics
begin

inductive is_send_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    pool \<pi>y = Some ((Stt (Bind xy (Sync xe) en) env \<kappa>)) \<Longrightarrow>
    env xe = Some (VClsr (SendEvt xsc xm) enve) \<Longrightarrow>
    enve xsc = Some (VChn c) \<Longrightarrow>
    is_send_path pool c \<pi>y
  "

inductive is_recv_path :: "trace_pool \<Rightarrow> chan \<Rightarrow> control_path \<Rightarrow> bool" where
  intro: "
    pool \<pi>y = Some ((Stt (Bind xy (Sync xe) en) env \<kappa>)) \<Longrightarrow>
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
  left: "prefix \<pi>1 \<pi>2 \<Longrightarrow> ordered \<pi>1 \<pi>2"
| right: "prefix \<pi>2 \<pi>1 \<Longrightarrow> ordered \<pi>1 \<pi>2"

inductive fan_out :: "tm \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (pool, H') \<Longrightarrow>
    forEveryTwo (is_send_path pool c) ordered \<Longrightarrow>
    fan_out e c
  "
  
inductive fan_in :: "tm \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (pool, H') \<Longrightarrow>
    forEveryTwo (is_recv_path pool c) ordered \<Longrightarrow> 
    fan_in e c
  "

inductive one_to_one :: "tm \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (pool, H') \<Longrightarrow>
    forEveryTwo (is_send_path pool c) ordered \<Longrightarrow>
    forEveryTwo (is_recv_path pool c) ordered \<Longrightarrow> 
    one_to_one e c
  "


inductive one_shot :: "tm \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (pool, H') \<Longrightarrow>
    forEveryTwo (is_send_path pool c) op= \<Longrightarrow> 
    one_shot e c
  "


inductive one_sync :: "tm \<Rightarrow> chan \<Rightarrow> bool" where
  intro: "
    star dynamicEval ([[] \<mapsto> (Stt e empty [])], {}) (pool, H') \<Longrightarrow>
    forEveryTwo (is_send_path pool c) op= \<Longrightarrow> 
    forEveryTwo (is_recv_path pool c) ordered \<Longrightarrow> 
    one_sync e c
  "

inductive 
    dynamicBuiltOnChanVal :: "val \<Rightarrow> chan \<Rightarrow> bool" 
and dynamicBuiltOnChanEnv :: "(name \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> bool" 
where
  dynamicBuiltOnChanVal_chan: "
    dynamicBuiltOnChanVal (VChn c) c
  "
| dynamicBuiltOnChanVal_closure: "
    dynamicBuiltOnChanEnv \<rho>' c \<Longrightarrow>
    dynamicBuiltOnChanVal (VClsr p \<rho>') c
  " 
| dynamicBuiltOnChanEnv_intro:
  "
    \<rho> n = Some v \<Longrightarrow>
    dynamicBuiltOnChanVal v c \<Longrightarrow>
    dynamicBuiltOnChanEnv \<rho> c
  "

inductive dynamicBuiltOnChanStack :: "contin list \<Rightarrow> chan \<Rightarrow> bool" where
  Env: 
  "
     dynamicBuiltOnChanEnv envk c \<Longrightarrow>
     dynamicBuiltOnChanStack (Ctn nk tk envk # stack') c
  "
| Stack:
  "
    dynamicBuiltOnChanStack stack' c \<Longrightarrow>
    dynamicBuiltOnChanStack (Ctn nk tk envk # stack') c
  "

inductive dynamicBuiltOnChanState :: "state \<Rightarrow> chan \<Rightarrow> bool" where
  Env: 
  "
     dynamicBuiltOnChanEnv env c \<Longrightarrow>
     dynamicBuiltOnChanState (Stt tm env stack) c
  "
| Stack:
  "
     dynamicBuiltOnChanStack stack c \<Longrightarrow>
     dynamicBuiltOnChanState (Stt tm env stack) c
  "



end
