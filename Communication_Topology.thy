theory Communication_Topology
  imports Main "~~/src/HOL/Library/Sublist"
begin
  
datatype var = Var string
  
value " Var ''x''"
  
datatype chan = Ch "var list"
  
datatype exp = 
  E_Let var bind exp ("LET _ = _ in _" [0,0, 61] 61) |
  E_Result var ("RESULT _" [61] 61)

and prim = 
  P_Abs var var exp |
  P_Pair var var |
  P_Left var |
  P_Right var |
  P_Send_Evt var var |
  P_Recv_Evt var |
  P_Always_Evt var

and bind = 
  B_Unit ("\<lparr>\<rparr>") |
  B_Chan ("CHAN \<lparr>\<rparr>") |
  B_Spawn exp ("SPAWN _" [61] 61) |
  B_Sync var ("SYNC _" [61] 61) |
  B_Fst var ("FST _" [61] 61) |
  B_Snd var ("SND _" [61] 61) |
  B_Case var var exp var exp ("CASE _ LEFT _ |> _ RIGHT _ |> _" [0,0,0,0, 61] 61) |
  B_Prim prim |
  B_App var var ("APP _ _" [61, 61] 61)
  
abbreviation bind_send_evt :: "var => var => bind" ("SEND EVT _ _" [0, 61] 61) where
  "SEND EVT x y \<equiv> B_Prim (P_Send_Evt x y)"
  
abbreviation bind_recv_evt :: "var => bind" ("RECV EVT _" [61] 61) where
  "RECV EVT x \<equiv> B_Prim (P_Recv_Evt x)"

abbreviation bind_always_evt :: "var \<Rightarrow> bind" ("ALWAYS EVT _" [61] 61) where
  "ALWAYS EVT x \<equiv> B_Prim (P_Always_Evt x)"
  
abbreviation bind_abs :: "var => var => exp => bind" ("FN _ _ . _" [0, 0, 61] 61) where
  "FN f x . e \<equiv> B_Prim (P_Abs f x e)"
  
abbreviation bind_pair :: "var => var => bind" ("\<lparr>_, _\<rparr>" [0, 0] 61) where
  "\<lparr>x, y\<rparr> \<equiv> B_Prim (P_Pair x y)"
  
abbreviation bind_inl :: "var => bind" ("LEFT _" [61] 61) where
  "LEFT x \<equiv> B_Prim (P_Left x)"
  
abbreviation bind_inr :: "var => bind" ("RIGHT _" [61] 61) where
  "RIGHT x \<equiv> B_Prim (P_Right x)"
  
value "Map.empty (Var ''x'' \<mapsto> 4)"

  
datatype val = 
  V_Chan chan ("\<lbrace>_\<rbrace>") |
  V_Closure prim "var \<rightharpoonup> val" ("\<lbrace>_, _\<rbrace>") |
  V_Unit ("\<lbrace>\<rbrace>")

  
fun closure :: "bind \<Rightarrow> (var \<rightharpoonup> val) \<Rightarrow> val option" ("\<lbrace>_, _\<rbrace>?") where
  "\<lbrace>B_Prim p, \<rho>\<rbrace>? = Some (V_Closure p \<rho>)" |
  "\<lbrace>_, _\<rbrace>? = None"


datatype cont = Cont var exp "var \<rightharpoonup> val" ("\<langle>_,_,_\<rangle>" [0, 0, 0] 70) 

type_synonym state = "exp \<times> (var \<rightharpoonup> val) \<times> cont list"
  
inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<hookrightarrow>" 55) where 
  Seq_Result: "
    (\<rho> x) = Some \<omega>
    \<Longrightarrow>
    (RESULT x, \<rho>, \<langle>x_ct, e_ct, \<rho>_ct\<rangle> # \<kappa>) \<hookrightarrow> (e_ct, \<rho>_ct(x_ct \<mapsto> \<omega>), \<kappa>)
  " |
   Seq_Let_Unit: "
    \<lbrace>\<rbrace> = \<omega>
    \<Longrightarrow>
    (LET x = \<lparr>\<rparr> in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Let_Prim: "
    \<lbrace>b, \<rho>\<rbrace>? = Some \<omega>
    \<Longrightarrow>
    (LET x = b in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Let_Case_Left: "
    \<lbrakk>(\<rho> x_sum) = \<lbrace>LEFT x_ll, \<rho>_l\<rbrace>? ; (\<rho>_l x_ll) = Some \<omega>_l \<rbrakk>
    \<Longrightarrow>
    (LET x = CASE x_sum LEFT x_l |> e_l RIGHT _ |> _ in e, \<rho>, \<kappa>) \<hookrightarrow> (e_l, \<rho>(x_l \<mapsto> \<omega>_l), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  Seq_Let_Case_Right: "
    \<lbrakk>(\<rho> x_sum) = \<lbrace>RIGHT x_rr, \<rho>_r\<rbrace>? ; (\<rho>_r x_rr) = Some \<omega>_r \<rbrakk>
    \<Longrightarrow>
    (LET x = CASE x_sum LEFT _ |> _ RIGHT x_r |> e_r in e, \<rho>, \<kappa>) \<hookrightarrow> (e_r, \<rho>(x_r \<mapsto> \<omega>_r), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  Seq_Fst: "
    \<lbrakk> (\<rho> x_p) = \<lbrace>\<lparr>x1, _\<rparr>, \<rho>_p\<rbrace>? ; (\<rho>_p x1) = Some \<omega> \<rbrakk>
    \<Longrightarrow>
    (LET x = FST x_p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Snd: "
    \<lbrakk> (\<rho> x_p) = \<lbrace>\<lparr>_, x2\<rparr>, \<rho>_p\<rbrace>? ; (\<rho>_p x2) = Some \<omega> \<rbrakk>
    \<Longrightarrow>
    (LET x = FST x_p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Let_App: "
    \<lbrakk>
    (\<rho> x_f) = Some \<omega>_f ; 
    Some \<omega>_f = \<lbrace>FN x_f_abs x_a_abs. e_abs, \<rho>_abs\<rbrace>? ; 
    (\<rho> x_a) = Some \<omega>_a 
    \<rbrakk>
    \<Longrightarrow>
    (LET x = APP x_f x_a in e, \<rho>, \<kappa>) \<hookrightarrow> (e_abs, \<rho>_abs(x_f_abs \<mapsto> \<omega>_f, x_a_abs \<mapsto> \<omega>_a), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "
  
inductive seq_steps :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<hookrightarrow>*" 55) where
  Seqs_Refl: "x \<hookrightarrow>* x" |
  Seqs_Step: "\<lbrakk>x \<hookrightarrow> y ; y \<hookrightarrow>* z\<rbrakk> \<Longrightarrow> x \<hookrightarrow>* z"
  
type_synonym trace = "var list"
  
inductive leaf :: "(trace \<rightharpoonup> state) \<Rightarrow> trace \<Rightarrow> bool" where
  Leaf: "
  \<lbrakk>
  (t \<pi>) = Some _ ;
  \<nexists> \<pi>' . (t \<pi>') = Some _ \<and> (strict_prefix \<pi> \<pi>')
  \<rbrakk> 
  \<Longrightarrow>
  leaf t \<pi>
  "

inductive sync_step :: "(trace \<rightharpoonup> val) \<Rightarrow> (trace \<rightharpoonup> val) \<Rightarrow> bool" (infix "\<leadsto>" 55) where 
  Sync_Send_Recv: "
  \<lbrakk>
  \<not>(prefix \<pi>_s \<pi>_r) ; \<not>(prefix \<pi>_r \<pi>_s) ;
  Some \<omega>_s = \<lbrace>SEND EVT x_ch x_m, \<rho>_s\<rbrace>? ;
  Some \<omega>_r = \<lbrace>RECV EVT x_ch, \<rho>_r\<rbrace>? ;
  \<lbrace>ALWAYS EVT x_a_s, [x_a_s \<mapsto> \<lbrace>\<rbrace>]\<rbrace>? = Some \<omega>_s' ;
  (\<rho>_s x_m) = Some \<omega>_m ;
  \<lbrace>ALWAYS EVT x_a_r, [x_a_r \<mapsto> \<omega>_m]\<rbrace>? = Some \<omega>_r'
  \<rbrakk>
  \<Longrightarrow>
  s(\<pi>_s \<mapsto> \<omega>_s, \<pi>_r \<mapsto> \<omega>_r) \<leadsto> s(\<pi>_s \<mapsto> \<omega>_s', \<pi>_r \<mapsto> \<omega>_r')
  "

inductive concur_step :: "(trace \<rightharpoonup> state) \<Rightarrow> (trace \<rightharpoonup> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Concur_Seq_Lift: "
  \<lbrakk> (t \<pi>) = Some st; st = (LET x = _ in _, _, _); st \<hookrightarrow> st'\<rbrakk>
  \<Longrightarrow>
  t \<rightarrow> t(\<pi>@[x] \<mapsto> st')
  " |
  Concur_Sync_Lift: "
  \<lbrakk> 
  leaf t \<pi>_1 ;
  (t \<pi>_1) = Some st_1 ; st_1 = (LET x_1 = SYNC x_evt_1 in e_1, \<rho>_1, \<kappa>_1) ;
  (\<rho>_1 x_evt_1) = Some \<omega>_1 ;
  \<omega>_1 \<leadsto> \<omega>_1' ;
  SOME \<omega>_1' = \<lbrace>ALWAYS EVT x_a_1, [x_a_1 \<mapsto> \<omega>_a_1]\<rbrace>? ;
  st_1' = (e_1, \<rho>_1(x_1 \<mapsto> \<omega>_a_1), \<kappa>_1)
  \<rbrakk>
  \<Longrightarrow>
  t \<rightarrow> t(\<pi>_1@[x_1] \<mapsto> st_1')
  "

  
  
abbreviation a where "a \<equiv> Var ''a''"
abbreviation b where "b \<equiv> Var ''b''"
abbreviation c where "c \<equiv> Var ''c''"
  
abbreviation d where "d \<equiv> Var ''d''"
abbreviation e where "e \<equiv> Var ''e''"
abbreviation f where "f \<equiv> Var ''f''"
  
abbreviation x where "x \<equiv> Var ''x''"
abbreviation y where "y \<equiv> Var ''y''"
abbreviation z where "z \<equiv> Var ''z''"
  
value "LET y = \<lparr>\<rparr> in VAR y"

value "
LET a = \<lparr>\<rparr> in
LET b = CHAN \<lparr>\<rparr> in
LET c = \<lparr>a, b\<rparr> in
LET x = SEND EVT b a in
LET x = SYNC x in
LET y = FST c in
LET z = RIGHT y in
LET d = 
  CASE z
  LEFT d |> RESULT d
  RIGHT d |> RESULT d
in
LET e = FN f x .
  LET a = APP f x in
  RESULT a
in
RESULT c
" 
  
end