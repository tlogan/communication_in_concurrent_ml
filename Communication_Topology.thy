theory Communication_Topology
  imports Main "~~/src/HOL/Library/Sublist"
begin
  
datatype var = Var string
  
value " Var ''x''"
  
type_synonym control_path = "(var + unit) list"
datatype chan = Ch control_path
  
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


datatype cont = Cont var exp "var \<rightharpoonup> val" ("\<langle>_,_,_\<rangle>" [0, 0, 0] 70) 

type_synonym state = "exp \<times> (var \<rightharpoonup> val) \<times> cont list"
  
type_synonym val_pool = "control_path \<rightharpoonup> val"
type_synonym state_pool = "control_path \<rightharpoonup> state"
  
inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<hookrightarrow>" 55) where 
  Seq_Result: "
    (\<rho> x) = Some \<omega> \<Longrightarrow>
    (RESULT x, \<rho>, \<langle>x_ct, e_ct, \<rho>_ct\<rangle> # \<kappa>) \<hookrightarrow> (e_ct, \<rho>_ct(x_ct \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Let_Unit: "
    (LET x = \<lparr>\<rparr> in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<lbrace>\<rbrace>), \<kappa>)
  " |
  Seq_Let_Prim: "
    (LET x = B_Prim p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>), \<kappa>)
  " |
  Seq_Let_Case_Left: "
    \<lbrakk>(\<rho> x_sum) = Some \<lbrace>P_Left x_ll, \<rho>_l\<rbrace> ; (\<rho>_l x_ll) = Some \<omega>_l \<rbrakk> \<Longrightarrow>
    (LET x = CASE x_sum LEFT x_l |> e_l RIGHT _ |> _ in e, \<rho>, \<kappa>) \<hookrightarrow> (e_l, \<rho>(x_l \<mapsto> \<omega>_l), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  Seq_Let_Case_Right: "
    \<lbrakk>(\<rho> x_sum) = Some \<lbrace>P_Right x_rr, \<rho>_r\<rbrace> ; (\<rho>_r x_rr) = Some \<omega>_r \<rbrakk> \<Longrightarrow>
    (LET x = CASE x_sum LEFT _ |> _ RIGHT x_r |> e_r in e, \<rho>, \<kappa>) \<hookrightarrow> (e_r, \<rho>(x_r \<mapsto> \<omega>_r), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  Seq_Fst: "
    \<lbrakk> (\<rho> x_p) = Some \<lbrace>P_Pair x1 _, \<rho>_p\<rbrace> ; (\<rho>_p x1) = Some \<omega> \<rbrakk> \<Longrightarrow>
    (LET x = FST x_p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Snd: "
    \<lbrakk> (\<rho> x_p) = Some \<lbrace>P_Pair _ x2, \<rho>_p\<rbrace> ; (\<rho>_p x2) = Some \<omega> \<rbrakk> \<Longrightarrow>
    (LET x = FST x_p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Let_App: "
    \<lbrakk>
      (\<rho> x_f) = Some \<lbrace>P_Abs x_f_abs x_a_abs e_abs, \<rho>_abs\<rbrace> ; 
      (\<rho> x_a) = Some \<omega>_a 
    \<rbrakk> \<Longrightarrow>
    (LET x = APP x_f x_a in e, \<rho>, \<kappa>) \<hookrightarrow> 
    (e_abs, \<rho>_abs(
      x_f_abs \<mapsto> \<lbrace>P_Abs x_f_abs x_a_abs e_abs, \<rho>_abs\<rbrace>, 
      x_a_abs \<mapsto> \<omega>_a
    ), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "
  
inductive seq_steps :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<hookrightarrow>*" 55) where
  Seqs_Refl: "x \<hookrightarrow>* x" |
  Seqs_Step: "\<lbrakk>x \<hookrightarrow> y ; y \<hookrightarrow>* z\<rbrakk> \<Longrightarrow> x \<hookrightarrow>* z"
  


  
  
abbreviation control_path_append_var :: "control_path => var => control_path" (infixl ";;" 61) where
  "\<pi>;;x \<equiv> \<pi> @ [Inl x]"
  
abbreviation control_path_append_unit :: "control_path  => control_path" ("_;;." [60]61) where
  "\<pi>;;. \<equiv> \<pi> @ [Inr ()]"
  
  
inductive leaf :: "(control_path \<rightharpoonup> state) \<Rightarrow> control_path \<Rightarrow> bool" where
  Leaf: "
    \<lbrakk>
      (stpool \<pi>) = Some _ ;
      \<nexists> \<pi>' . (stpool \<pi>') = Some _ \<and> (strict_prefix \<pi> \<pi>')
    \<rbrakk> \<Longrightarrow>
    leaf stpool \<pi>
  "


inductive sync_step :: "val_pool \<Rightarrow> val_pool \<Rightarrow> bool" (infix "\<leadsto>" 55) where 
  Sync_Send_Recv: "
    \<lbrakk>
      Some (V_Chan _) = \<rho>_s x_ch_s;
      \<rho>_r x_ch_r = \<rho>_s x_ch_s ;
      (\<rho>_s x_m) = Some \<omega>_m
    \<rbrakk> \<Longrightarrow>
    vpool(\<pi>_s \<mapsto> \<lbrace>P_Send_Evt x_ch_s x_m, \<rho>_s\<rbrace>, \<pi>_r \<mapsto> \<lbrace>P_Recv_Evt x_ch_r, \<rho>_r\<rbrace>) \<leadsto> 
    vpool(\<pi>_s \<mapsto> \<lbrace>P_Always_Evt x_a_s, [x_a_s \<mapsto> \<lbrace>\<rbrace>]\<rbrace>, \<pi>_r \<mapsto> \<lbrace>P_Always_Evt x_a_r, [x_a_r \<mapsto> \<omega>_m]\<rbrace>)
  "

inductive concur_step :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Concur_Lift_Seq: "
    \<lbrakk> (stpool \<pi>) = Some st; st = (LET x = _ in _, _, _); st \<hookrightarrow> st'\<rbrakk> \<Longrightarrow>
    stpool \<rightarrow> stpool(\<pi>;;x \<mapsto> st')
  " |
  Concur_Lift_Sync: "
    \<lbrakk>
      vpool \<leadsto> vpool';
      (stpool_sync []) = None ;
      (\<forall> \<pi> x. stpool_sync (\<pi>;;x) = Some _ \<longrightarrow> vpool' \<pi> = Some _ );
      (\<forall> \<pi> x y. stpool_sync (\<pi>;;x) = Some _ \<longrightarrow> stpool_sync (\<pi>;;y) = Some _ \<longrightarrow> x = y) ;
      (\<forall> \<pi> .
        leaf stpool \<pi> \<longrightarrow>
        (stpool \<pi>) = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<longrightarrow>
        (vpool \<pi>) = (\<rho> x_evt) \<longrightarrow>
        (vpool' \<pi>) = Some \<lbrace>P_Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<longrightarrow>
        stpool_sync (\<pi>;;x) = Some (e, \<rho>(x \<mapsto> \<omega>_a), \<kappa>)
      )
    \<rbrakk> \<Longrightarrow>
    stpool \<rightarrow> stpool ++ stpool_sync
  " |
  Concur_Let_Chan: "
    stpool \<pi> = Some (LET x = CHAN \<lparr>\<rparr> in e, \<rho>, \<kappa>) \<Longrightarrow>
    stpool \<rightarrow> stpool(
       \<pi>;;x \<mapsto> (e, \<rho>(x \<mapsto> \<lbrace>Chan (\<pi>;;x)\<rbrace>), \<kappa>)
    )
  " |
  Concur_Let_Spawn: "
    stpool \<pi> = Some (LET x = SPAWN e_child in e, \<rho>, \<kappa>) \<Longrightarrow>
    stpool \<rightarrow> stpool(
      \<pi>;;x \<mapsto> (e, \<rho>(x \<mapsto> \<lbrace>\<rbrace>), \<kappa>), 
      \<pi>;;. \<mapsto> (e_child, \<rho>, \<kappa>) 
    )
  "
  
inductive concur_steps :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where
  Concurs_Refl: "x \<rightarrow>* x" |
  Concurs_Step: "\<lbrakk>x \<rightarrow> y ; y \<rightarrow>* z\<rbrakk> \<Longrightarrow> x \<rightarrow>* z"
  
definition send_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_sites stpool ch = {\<pi>. \<exists> x x_evt e \<kappa> \<rho> x_ch x_m \<rho>_evt. 
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and> 
    \<rho> x_evt = Some \<lbrace>P_Send_Evt x_ch x_m, \<rho>_evt\<rbrace> \<and> 
    \<rho>_evt x_ch = Some \<lbrace>ch\<rbrace>
  }"
  
definition recv_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_sites stpool ch = {\<pi>. \<exists> x x_evt e \<kappa> \<rho> x_ch \<rho>_evt. 
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and> 
    \<rho> x_evt = Some \<lbrace>P_Recv_Evt x_ch, \<rho>_evt\<rbrace> \<and> 
    \<rho>_evt x_ch = Some \<lbrace>ch\<rbrace>
  }"
  
fun channel_exists :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "channel_exists stpool (Ch \<pi>) \<longleftrightarrow> (\<exists> x e \<rho> \<kappa>. stpool \<pi> = Some (LET x = CHAN \<lparr>\<rparr> in e, \<rho>, \<kappa>))"
  
definition state_pool_possible :: "exp \<Rightarrow> state_pool \<Rightarrow> bool" where
  "state_pool_possible e stpool \<longleftrightarrow> [[] \<mapsto> (e, Map.empty, [])] \<rightarrow>* stpool"
  
definition one_shot :: "exp \<Rightarrow> var \<Rightarrow> bool" where
  "one_shot e x \<longleftrightarrow> (\<forall> stpool \<pi>. 
    state_pool_possible e stpool \<longrightarrow>
    channel_exists stpool (Ch (\<pi>;;x)) \<longrightarrow> (*chan_exists doesn't seem necessary*)
    card (send_sites stpool (Ch (\<pi>;;x))) \<le> 1
  )"
  
definition single_side :: "(state_pool \<Rightarrow> chan \<Rightarrow> control_path set) \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  "single_side sites e x \<longleftrightarrow> (\<forall> stpool \<pi> \<pi>_1 \<pi>_2 .
    state_pool_possible e stpool \<longrightarrow>
    channel_exists stpool (Ch (\<pi>;;x)) \<longrightarrow>
    (let site_set = (sites stpool (Ch (\<pi>;;x))) in 
      \<pi>_1 \<in> site_set \<and> \<pi>_2 \<in> site_set
    ) \<longrightarrow>
    (prefix \<pi>_1 \<pi>_2 \<or> prefix \<pi>_2 \<pi>_1) 
  )"
  
definition single_receiver :: "exp \<Rightarrow> var \<Rightarrow> bool" where 
  "single_receiver = single_side recv_sites"
  
definition single_sender :: "exp \<Rightarrow> var \<Rightarrow> bool" where 
  "single_sender = single_side send_sites"
  
definition point_to_point :: "exp \<Rightarrow> var \<Rightarrow> bool" where
  "point_to_point e x \<longleftrightarrow> single_sender e x \<and> single_receiver e x"
  
definition fan_out :: "exp \<Rightarrow> var \<Rightarrow> bool" where
  "fan_out e x \<longleftrightarrow> single_sender e x \<and> \<not> single_receiver e x "
  
definition fan_in :: "exp \<Rightarrow> var \<Rightarrow> bool" where
  "fan_in e x \<longleftrightarrow> \<not> single_sender e x \<and> single_receiver e x "
  
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