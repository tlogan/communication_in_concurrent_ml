theory Communication_Topology
  imports Main "~~/src/HOL/Library/Sublist"
begin
  
datatype var = Var string
  
value " Var ''x''"
  
type_synonym control_path = "(var + unit) list"
datatype chan = Ch control_path
  
(* ANF grammar *)
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


(* unrestricted grammar*)

datatype u_exp =
  U_Let var  u_exp u_exp (".LET _ = _ in _" [0,0, 61] 61) |
  U_Var var ("._" [61] 61)|
  U_Abs var var u_exp (".FN _ _ .  _" [0, 0, 61] 61)|
  U_Pair u_exp u_exp (".\<lparr>_, _\<rparr>" [0, 0] 61)|
  U_Left u_exp (".LEFT _" [61] 61)|
  U_Right u_exp (".RIGHT _" [61] 61)|
  U_Send_Evt u_exp u_exp (".SEND EVT _ _" [61] 61)|
  U_Recv_Evt u_exp (".RECV EVT _" [61] 61)|
  U_Always_Evt u_exp (".ALWAYS EVT _" [61] 61)|
  U_Unit (".\<lparr>\<rparr>") |
  U_Chan (".CHAN \<lparr>\<rparr>") |
  U_Spawn u_exp (".SPAWN _" [61] 61) |
  U_Sync u_exp (".SYNC _" [61] 61) |
  U_Fst u_exp (".FST _" [61] 61) |
  U_Snd u_exp (".SND _" [61] 61) |
  U_Case u_exp var u_exp var u_exp (".CASE _ LEFT _ |> _ RIGHT _ |> _" [0,0,0,0, 61] 61) |
  U_App u_exp u_exp (".APP _ _" [61, 61] 61)
  
  
fun program_size :: "u_exp \<Rightarrow> nat" where
  "program_size (.y) = 1" |
  "program_size (.LET x2 = eb in e) = 1 + (program_size eb) + (program_size e)" |
  "program_size (.FN f x2 . e) = 1 + (program_size e)" | 
  "program_size (.\<lparr>e1, e2\<rparr>) = 1 + (program_size e1) + (program_size e2)" |
  "program_size (.LEFT e) = 1 + (program_size e)" |
  "program_size (.RIGHT e) = 1 + (program_size e)" |
  "program_size (.SEND EVT e1 e2) = 1 + (program_size e1) + (program_size e2)" |
  "program_size (.RECV EVT e) =  1 + (program_size e)" |
  "program_size (.ALWAYS EVT e) = 1 + (program_size e)" |
  "program_size (.\<lparr>\<rparr>) = 1" |
  "program_size (.CHAN \<lparr>\<rparr>) = 1" |
  "program_size (.SPAWN e) = 1 + (program_size e)" |
  "program_size (.SYNC e) = 1 + (program_size e)" |
  "program_size (.FST e) = 1 + (program_size e)" |
  "program_size (.SND e) = 1 + (program_size e)" |
  "program_size (.CASE e1 LEFT x2 |> e2 RIGHT x3 |> e3) = 1 + (program_size e1) + (program_size e2) + (program_size e3)" |
  "program_size (.APP e1 e2) = 1 + (program_size e1) + (program_size e2)"
  
  
fun rename :: "var \<Rightarrow> var \<Rightarrow> u_exp \<Rightarrow> u_exp" where
  "rename x0 x1 (.y) = (if x0 = y then .x1 else .y)" |
  "rename x0 x1 (.LET x2 = eb in e) = (.LET x2 = rename x0 x1 eb in
    (if x0 = x2 then e else (rename x0 x1 e))
  )" |
  "rename x0 x1 (.FN f x2 . e) = (.FN f x2 .
    (if x0 = f \<or> x0 = x2 then e else (rename x0 x1 e))
  )" | 
  "rename x0 x1 (.\<lparr>e1, e2\<rparr>) = .\<lparr>rename x0 x1 e1, rename x0 x1 e2\<rparr>" |
  "rename x0 x1 (.LEFT e) = .LEFT (rename x0 x1 e)" |
  "rename x0 x1 (.RIGHT e) = .RIGHT (rename x0 x1 e)" |
  "rename x0 x1 (.SEND EVT e1 e2) = .SEND EVT (rename x0 x1 e1) (rename x0 x1 e2)" |
  "rename x0 x1 (.RECV EVT e) = .RECV EVT (rename x0 x1 e)" |
  "rename x0 x1 (.ALWAYS EVT e) = .ALWAYS EVT (rename x0 x1 e)" |
  "rename x0 x1 (.\<lparr>\<rparr>) = .\<lparr>\<rparr>" |
  "rename x0 x1 (.CHAN \<lparr>\<rparr>) = .CHAN \<lparr>\<rparr>" |
  "rename x0 x1 (.SPAWN e) = .SPAWN (rename x0 x1 e)" |
  "rename x0 x1 (.SYNC e) = .SYNC (rename x0 x1 e)" |
  "rename x0 x1 (.FST e) = .FST (rename x0 x1 e)" |
  "rename x0 x1 (.SND e) = .SND (rename x0 x1 e)" |
  "rename x0 x1 (.CASE e1 LEFT x2 |> e2 RIGHT x3 |> e3) = 
    (.CASE rename x0 x1 e1 
      LEFT x2 |> (if x0 = x2 then e2 else (rename x0 x1 e2)) 
      RIGHT x3 |> (if x0 = x3 then e3 else (rename x0 x1 e3)) 
    )
  " |
  "rename x0 x1 (.APP e1 e2) = .APP (rename x0 x1 e1) (rename x0 x1 e2)"
  
  
theorem program_size_rename_equal[simp]: "program_size (rename x0 x1 e) = program_size e"
by (induction e) auto
  
definition sym :: "nat \<Rightarrow> var" where "sym i = Var (''g'' @ [char_of_nat i])"
  

function (sequential) normalize_cont :: "nat \<Rightarrow> u_exp \<Rightarrow> (var \<Rightarrow> exp) \<Rightarrow> exp" where
  "normalize_cont i (.x) k = k x" |
  "normalize_cont i (.LET x = .xb in e) k = 
    normalize_cont i (rename x xb e) k
  " |
  "normalize_cont i (.LET x = eb in e) k = 
    normalize_cont i eb (\<lambda> xb . 
      normalize_cont i (rename x xb e) k
    )
  " |
  "normalize_cont i (.FN f x . e) k =
    (let g = sym i in
    (let f' = sym (i+1) in
    (let x' = sym (i+2) in
    (let e' = (rename f f' (rename x x' e)) in
      LET g = (FN f x . normalize_cont (i+3) e' (\<lambda> x . RESULT x)) in (k g)
    ))))
  " |
  "normalize_cont i (.\<lparr>e1, e2\<rparr>) k =
    (let g = sym i in
    normalize_cont (i+1) e1 (\<lambda> x1 .
      normalize_cont (i+2) e2 (\<lambda> x2 .
        LET g = \<lparr>x1, x2\<rparr> in (k g)
      )
    ))
  " |
  "normalize_cont i (.LEFT e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = LEFT xb in (k g)
      )
    )
  " |
  "normalize_cont i (.RIGHT e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = RIGHT xb in (k g)
      )
    )
  " |
  "normalize_cont i (.SEND EVT e1 e2) k =
    (let g = sym i in
      normalize_cont (i+1) e1 (\<lambda> x1 .
        normalize_cont (i+2) e2 (\<lambda> x2 .
          LET g = SEND EVT x1 x2 in (k g)
        ) 
      )
    )
  " |
  "normalize_cont i (.RECV EVT e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = RECV EVT xb in (k g)
      )
    )
  " |
  "normalize_cont i (.ALWAYS EVT e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = ALWAYS EVT xb in (k g)
      )
    )
  " |
  "normalize_cont i (.\<lparr>\<rparr>) k =
    (let g = sym i in
      LET g = \<lparr>\<rparr> in (k g)
    )
  "|
  "normalize_cont i (.CHAN \<lparr>\<rparr>) k =
    (let g = sym i in
      LET g = CHAN \<lparr>\<rparr> in (k g)
    )
  "|
  "normalize_cont i (.SPAWN e) k = 
    (let g = sym i in
      LET g = SPAWN (normalize_cont (i+1) e (\<lambda> x . RESULT x)) in (k g)
    )
  " |
  "normalize_cont i (.SYNC e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = SYNC xb in (k g)
      )
    )
  " |
  "normalize_cont i(.FST e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = FST xb in (k g)
      )
    )
  " |
  "normalize_cont i (.SND e) k =
    (let g = sym i in
      normalize_cont (i+1) e (\<lambda> xb .
        LET g = SND xb in (k g)
      )
    )
  " |
  "normalize_cont i (.CASE e LEFT xl |> el RIGHT xr |> er) k =
    (let g = sym i in
    (let xl' = sym (i+1) in
    (let el' = (rename xl xl' el) in
    (let xr' = sym (i+2) in  
    (let er' = (rename xr xr' er) in
      normalize_cont (i+3) e (\<lambda> x .
        LET g = 
          CASE x 
          LEFT xl' |> (normalize_cont (i+4) el' (\<lambda> x . RESULT x)) 
          RIGHT xr' |> (normalize_cont (i+5) er' (\<lambda> x . RESULT x)) 
        in (k g)  
    ))))))
  " |
  "normalize_cont i (.APP e1 e2) k =
    (let g = sym i in
      normalize_cont (i+1) e1 (\<lambda> x1 .
        normalize_cont (i+2) e2 (\<lambda> x2 .
          LET g = APP x1 x2 in (k g)
        ) 
      )
    )
  "
by pat_completeness auto
termination by (relation "measure (\<lambda>(i, e, k). program_size e)") auto

    
definition normalize :: "u_exp \<Rightarrow> exp" where
  "normalize e = normalize_cont 100 e  (\<lambda> x . RESULT x)"

  
  
abbreviation a where "a \<equiv> Var ''a''"
abbreviation b where "b \<equiv> Var ''b''"
abbreviation c where "c \<equiv> Var ''c''"
  
abbreviation d where "d \<equiv> Var ''d''"
abbreviation e where "e \<equiv> Var ''e''"
abbreviation f where "f \<equiv> Var ''f''"
abbreviation w where "w \<equiv> Var ''w''"
abbreviation x where "x \<equiv> Var ''x''"
abbreviation y where "y \<equiv> Var ''y''"
abbreviation z where "z \<equiv> Var ''z''"
  
definition prog_one where 
  "prog_one = 
    LET a = CHAN \<lparr>\<rparr> in
    LET b = SPAWN (
      LET c = CHAN \<lparr>\<rparr> in
      LET x = SEND EVT a c in
      LET y = SYNC x in
      LET z = RECV EVT c in
      RESULT z
    ) in
    LET d = RECV EVT a in
    LET e = SYNC d in
    LET f = SEND EVT e b in
    LET w = SYNC f in
    RESULT w
  "
(*
theorem prog_one_properties: "
  single_receiver prog_one a \<and>
  single_sender prog_one a \<and>
  single_receiver prog_one c \<and>
  single_sender prog_one c
"
*) 

(*  
definition prog_two where 
  "prog_two = 
    .LET a = .CHAN \<lparr>\<rparr> in
    .LET b = .SPAWN (
      .LET c = .CHAN \<lparr>\<rparr> in
      .LET x = .SEND EVT .a .c in
      .LET y = .SYNC .x in
      .LET z = .RECV EVT .c in
      .z
    ) in
    .LET d = .RECV EVT .a in
    .LET e = .SYNC .d in
    .LET f = .SEND EVT .e .b in
    .LET w = .SYNC .f in
    .w
  "
*)
