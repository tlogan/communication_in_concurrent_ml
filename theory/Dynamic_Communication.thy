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
  dynamicBuiltOnChan :: "(name \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> name \<Rightarrow> bool" and
  dynamicBuiltOnChanAtom :: "(name \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> atom \<Rightarrow> bool" and
  dynamicBuiltOnChanComplex :: "(name \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> complex \<Rightarrow> bool" and
  dynamicBuiltOnChanTm :: "(name \<rightharpoonup> val) \<Rightarrow> chan \<Rightarrow> tm \<Rightarrow> bool" 
where
  DynBuiltChan: "
    \<rho> x = Some (VChn c) \<Longrightarrow>
    dynamicBuiltOnChan \<rho> c x
  "
| DynBuiltChanClosure: "
    dynamicBuiltOnChanAtom \<rho>' c p \<Longrightarrow>
    \<rho> x = Some (VClsr p \<rho>') \<Longrightarrow>
    dynamicBuiltOnChan \<rho> c x
  " 
| DynBuiltChanSendEvt: "
    dynamicBuiltOnChan \<rho> c xSC \<or> dynamicBuiltOnChan \<rho> c xM \<Longrightarrow>
    dynamicBuiltOnChanAtom \<rho> c (SendEvt xSC xM)
  "
| Recv_Evt: "
    dynamicBuiltOnChan \<rho> c xRC \<Longrightarrow>
    dynamicBuiltOnChanAtom \<rho> c (RecvEvt xRC)
  "
| Pair: "
    dynamicBuiltOnChan \<rho> c x1 \<or> dynamicBuiltOnChan \<rho> c x2 \<Longrightarrow>
    dynamicBuiltOnChanAtom \<rho> c (Pair x1 x2)
  "
| Left: "
    dynamicBuiltOnChan \<rho> c xSum \<Longrightarrow>
    dynamicBuiltOnChanAtom \<rho> c (Lft xSum)
  "
| Right: "
    dynamicBuiltOnChan \<rho> c xSum \<Longrightarrow>
    dynamicBuiltOnChanAtom \<rho> c (Rht xSum)
  "
| Fun: "
    dynamicBuiltOnChanTm \<rho> c e \<Longrightarrow>
    dynamicBuiltOnChanAtom \<rho> c (Fun f x e)
  "
| Atom: "
    dynamicBuiltOnChanAtom \<rho> c p \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (Atom p)
  "
| Spawn: "
    dynamicBuiltOnChanTm \<rho> c eCh \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (Spwn eCh)
  "
| DynBuiltChanSync: "
    dynamicBuiltOnChan \<rho> c xY \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (Sync xY)
  "
| Fst: "
    dynamicBuiltOnChan \<rho> c xP \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (Fst xP)
  "
| Snd: "
    dynamicBuiltOnChan \<rho> c xP \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (Snd xP)
  "
| Case: "
    dynamicBuiltOnChan \<rho> c xS \<or> 
    dynamicBuiltOnChanTm \<rho> c eL \<or> dynamicBuiltOnChanTm \<rho> c eR \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (Case xS xL eL xR eR)
  "
| App: "
    dynamicBuiltOnChan \<rho> c f \<or>
    dynamicBuiltOnChan \<rho> c xA \<Longrightarrow>
    dynamicBuiltOnChanComplex \<rho> c (App f xA)
  "
| dynamicBuiltOnChanTm_Rslt: "
    dynamicBuiltOnChan \<rho> c x \<Longrightarrow>
    dynamicBuiltOnChanTm \<rho> c (Rslt x)
  "
| Bind: "
    dynamicBuiltOnChanComplex \<rho> c b \<or> dynamicBuiltOnChanTm \<rho> c e \<Longrightarrow>
    dynamicBuiltOnChanTm \<rho> c (Bind x b e)
  "

inductive dynamicBuiltOnChanStack :: "contin list \<Rightarrow> chan \<Rightarrow> bool" where
  Tm:
  "
    dynamicBuiltOnChanTm envk c tk \<Longrightarrow>
    dynamicBuiltOnChanStack (Ctn nk tk envk # stack') c
  "
| Stack:
  "
    dynamicBuiltOnChanStack stack' c \<Longrightarrow>
    dynamicBuiltOnChanStack (Ctn nk tk envk # stack') c
  "

inductive dynamicBuiltOnChanState :: "state \<Rightarrow> chan \<Rightarrow> bool" where
  Tm: 
  "
     dynamicBuiltOnChanTm env c tm \<Longrightarrow>
     dynamicBuiltOnChanState (Stt tm env stack) c
  "
| Stack:
  "
     dynamicBuiltOnChanStack stack c \<Longrightarrow>
     dynamicBuiltOnChanState (Stt tm env stack) c
  "



end
