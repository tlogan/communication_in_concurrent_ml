theory Semantics
  imports Main Syntax "~~/src/HOL/Library/Sublist" "~~/src/HOL/IMP/Star"
begin

  
type_synonym control_path = "(var + unit) list"
datatype chan = Ch control_path

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
    (LET x = Prim p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<lbrace>p, \<rho>\<rbrace>), \<kappa>)
  " |
  Seq_Let_Case_Left: "
    \<lbrakk>(\<rho> x_sum) = Some \<lbrace>Left x_ll, \<rho>_l\<rbrace> ; (\<rho>_l x_ll) = Some \<omega>_l \<rbrakk> \<Longrightarrow>
    (LET x = CASE x_sum LEFT x_l |> e_l RIGHT _ |> _ in e, \<rho>, \<kappa>) \<hookrightarrow> (e_l, \<rho>(x_l \<mapsto> \<omega>_l), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  Seq_Let_Case_Right: "
    \<lbrakk>(\<rho> x_sum) = Some \<lbrace>Right x_rr, \<rho>_r\<rbrace> ; (\<rho>_r x_rr) = Some \<omega>_r \<rbrakk> \<Longrightarrow>
    (LET x = CASE x_sum LEFT _ |> _ RIGHT x_r |> e_r in e, \<rho>, \<kappa>) \<hookrightarrow> (e_r, \<rho>(x_r \<mapsto> \<omega>_r), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  Seq_Fst: "
    \<lbrakk> (\<rho> x_p) = Some \<lbrace>Pair x1 _, \<rho>_p\<rbrace> ; (\<rho>_p x1) = Some \<omega> \<rbrakk> \<Longrightarrow>
    (LET x = FST x_p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Snd: "
    \<lbrakk> (\<rho> x_p) = Some \<lbrace>Pair _ x2, \<rho>_p\<rbrace> ; (\<rho>_p x2) = Some \<omega> \<rbrakk> \<Longrightarrow>
    (LET x = SND x_p in e, \<rho>, \<kappa>) \<hookrightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  Seq_Let_App: "
    \<lbrakk>
      (\<rho> x_f) = Some \<lbrace>Abs x_f_abs x_a_abs e_abs, \<rho>_abs\<rbrace> ; 
      (\<rho> x_a) = Some \<omega>_a 
    \<rbrakk> \<Longrightarrow>
    (LET x = APP x_f x_a in e, \<rho>, \<kappa>) \<hookrightarrow> 
    (e_abs, \<rho>_abs(
      x_f_abs \<mapsto> \<lbrace>Abs x_f_abs x_a_abs e_abs, \<rho>_abs\<rbrace>, 
      x_a_abs \<mapsto> \<omega>_a
    ), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "

inductive_cases Seq_Result_E[elim!]: "(RESULT x, \<rho>, \<langle>x_ct, e_ct, \<rho>_ct\<rangle> # \<kappa>) \<hookrightarrow> st"
inductive_cases Seq_Let_Unit_E: "(LET x = \<lparr>\<rparr> in e, \<rho>, \<kappa>) \<hookrightarrow> st"
inductive_cases Seq_Let_Prim_E[elim!]: "(LET x = Prim p in e, \<rho>, \<kappa>) \<hookrightarrow> st" 
inductive_cases Seq_Let_Case_Left_E[elim!]: "(LET x = CASE x_sum LEFT x_l |> e_l RIGHT x_r |> e_r in e, \<rho>, \<kappa>) \<hookrightarrow> st" 
inductive_cases Seq_Let_Case_Right_E[elim!]: "(LET x = CASE x_sum LEFT x_l |> e_l RIGHT x_r |> e_r in e, \<rho>, \<kappa>) \<hookrightarrow> st" 
inductive_cases Seq_Fst_E[elim!] : "(LET x = FST x_p in e, \<rho>, \<kappa>) \<hookrightarrow> st"
inductive_cases Seq_Snd_E[elim!] : "(LET x = SND x_p in e, \<rho>, \<kappa>) \<hookrightarrow> st"
inductive_cases Seq_Let_App_E[elim!]: "(LET x = APP x_f x_a in e, \<rho>, \<kappa>) \<hookrightarrow> st"
  
lemma "(\<And> x . S \<Longrightarrow> (P x \<longrightarrow> R x) \<Longrightarrow> T \<Longrightarrow> Q) \<Longrightarrow> (S \<Longrightarrow> (\<forall> x. P x \<longrightarrow> R x) \<Longrightarrow> T \<Longrightarrow> Q)"
  by auto

abbreviation control_path_append_var :: "control_path => var => control_path" (infixl ";;" 61) where
  "\<pi>;;x \<equiv> \<pi> @ [Inl x]"
  
abbreviation control_path_append_unit :: "control_path  => control_path" ("_;;." [60]61) where
  "\<pi>;;. \<equiv> \<pi> @ [Inr ()]"
  
  
definition leaf :: "(control_path \<rightharpoonup> state) \<Rightarrow> control_path \<Rightarrow> bool" where
  "leaf stpool \<pi> \<equiv>
      (stpool \<pi>) \<noteq> None \<and>
      (\<nexists> \<pi>' . (stpool \<pi>') \<noteq> None \<and> (strict_prefix \<pi> \<pi>'))
  "
  
lemma leaf_elim: "
  \<lbrakk> leaf stpool \<pi>; strict_prefix \<pi> \<pi>' \<rbrakk>
\<Longrightarrow>
   stpool \<pi>' = None 
"
  apply (simp add: leaf_def)
  by (metis option.exhaust prod_cases3)


inductive sync_step :: "val_pool \<Rightarrow> val_pool \<Rightarrow> bool" (infix "\<leadsto>" 55) where 
  Sync_Send_Recv: "
    \<lbrakk>
      Some (V_Chan _) = \<rho>_s x_ch_s; \<rho>_r x_ch_r = \<rho>_s x_ch_s ; (\<rho>_s x_m) = Some \<omega>_m
    \<rbrakk> \<Longrightarrow>
    [\<pi>_s \<mapsto> \<lbrace>Send_Evt x_ch_s x_m, \<rho>_s\<rbrace>, \<pi>_r \<mapsto> \<lbrace>Recv_Evt x_ch_r, \<rho>_r\<rbrace>] \<leadsto> 
    [\<pi>_s \<mapsto> \<lbrace>Always_Evt x_a_s, [x_a_s \<mapsto> \<lbrace>\<rbrace>]\<rbrace>, \<pi>_r \<mapsto> \<lbrace>Always_Evt x_a_r, [x_a_r \<mapsto> \<omega>_m]\<rbrace>]
  "

lemma "
(\<And> x y z.\<lbrakk> S y ; P x ; R x z; T y\<rbrakk> \<Longrightarrow> Q y) 
\<Longrightarrow> 
(\<And> y . \<lbrakk>S y ; (\<forall> x. P x \<longrightarrow> (\<exists> z . R x z)); (\<exists> x . P x) ; T y \<rbrakk> \<Longrightarrow> Q y)
"
by (metis (mono_tags))
(*         
 * Instead of stating a theorem as
 * (\<And> y . \<lbrakk>S y ; (\<forall> x. P x \<longrightarrow> (\<exists> z . R x z)); (\<exists> x . P x) ; T y \<rbrakk> \<Longrightarrow> Q y)
 * we can observe that it is necessitated by 
 * (\<And> x y z . \<lbrakk> S y ; P x ; R x z; T y\<rbrakk> \<Longrightarrow> Q y)
 * and state the theorem as such, the stronger statement.
 *) 

lemma "
(
  \<And> vpool vpool' stpool stpool_sync . 
    vpool \<leadsto> vpool' \<Longrightarrow>
    (\<forall> \<pi>' e \<rho>' \<kappa> .
      stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) \<longrightarrow>
      (\<exists> x \<omega>_a x_a \<rho> x_evt \<pi> .
        \<pi>' = \<pi>;;x \<and>
        \<rho>' = \<rho>(x \<mapsto> \<omega>_a) \<and>
        vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<and>
        vpool \<pi> = \<rho> x_evt \<and>
        stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and>
        leaf stpool \<pi>
      )
    ) \<Longrightarrow>
    (\<exists> \<pi>' e \<rho>' \<kappa> . stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) )
  
)
 \<Longrightarrow>
(
  \<And> vpool vpool' stpool stpool_sync \<pi> \<pi>' e \<rho>' \<kappa> x \<omega>_a x_a \<rho> x_evt .
    vpool \<leadsto> vpool' \<Longrightarrow>
    stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) \<Longrightarrow>
    \<rho>' = \<rho>(x \<mapsto> \<omega>_a) \<Longrightarrow>
    vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<Longrightarrow>
    vpool \<pi> = \<rho> x_evt \<Longrightarrow>
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<Longrightarrow>
    leaf stpool \<pi>
)
"
  using option.simps(3) by fastforce

lemma "
(
  \<And> vpool vpool' stpool stpool_sync \<pi> \<pi>' e \<rho>' \<kappa> x \<omega>_a x_a \<rho> x_evt . \<lbrakk>
    vpool \<leadsto> vpool' ;
    stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) ;
    \<pi>' = \<pi>;;x ;
    \<rho>' = \<rho>(x \<mapsto> \<omega>_a) ;
    vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> ;
    vpool \<pi> = \<rho> x_evt ;
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) ;
    leaf stpool \<pi>
  \<rbrakk> \<Longrightarrow>
  step stpool (stpool ++ stpool_sync)
) 

\<Longrightarrow>

(
  \<And> vpool vpool' stpool stpool_sync . \<lbrakk>
    vpool \<leadsto> vpool' ;
    (\<forall> \<pi>' e \<rho>' \<kappa> .
      stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) \<longrightarrow>
      (\<exists> x \<omega>_a x_a \<rho> x_evt \<pi> .
        \<pi>' = \<pi>;;x \<and>
        \<rho>' = \<rho>(x \<mapsto> \<omega>_a) \<and>
        vpool' \<pi> = Some \<lbrace>Always_Evt x_a, [x_a \<mapsto> \<omega>_a]\<rbrace> \<and>
        vpool \<pi> = \<rho> x_evt \<and>
        stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and>
        leaf stpool \<pi>
      )
    ) ;
    (\<exists> \<pi>' e \<rho>' \<kappa> . stpool_sync \<pi>' = Some (e, \<rho>', \<kappa>) )
  \<rbrakk> \<Longrightarrow>
  step stpool (stpool ++ stpool_sync)
)
"
by meson
  
  
inductive concur_step :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  Concur_Seq: "
    \<lbrakk> 
      leaf stpool \<pi> ;
      (stpool \<pi>) = Some (LET x = b in e, \<rho>, \<kappa>) ;
      (LET x = b in e, \<rho>, \<kappa>) \<hookrightarrow> st'
    \<rbrakk> \<Longrightarrow>
    stpool \<rightarrow> stpool(
      \<pi>;;x \<mapsto> st'
    )
  " |
  Concur_Sync: "
    \<lbrakk>
   
      leaf stpool \<pi>1 ;
      stpool \<pi>1 = Some (LET x1 = SYNC x1_evt in e1, \<rho>1, \<kappa>1) ;
      \<rho>1 x1_evt = Some \<lbrace>Send_Evt x_ch1 x_m, \<rho>_s\<rbrace> ;
      \<rho>_s x_ch1 = Some (V_Chan c); 
      
      \<rho>_s x_m = Some \<omega>_m ;

      leaf stpool \<pi>2 ;
      stpool \<pi>2 = Some (LET x2 = SYNC x2_evt in e2, \<rho>2, \<kappa>2) ;
      \<rho>2 x2_evt = Some \<lbrace>Recv_Evt x_ch2, \<rho>_r\<rbrace> ;
      \<rho>_r x_ch2 = Some (V_Chan c)

    \<rbrakk> \<Longrightarrow>
    stpool \<rightarrow> stpool ++ [\<pi>1;;x1 \<mapsto> (e1, \<rho>1(x1 \<mapsto> \<lbrace>\<rbrace>), k1), \<pi>2;;x2 \<mapsto> (e1, \<rho>2(x2 \<mapsto> \<omega>_m), k2)]
  " |
  Concur_Let_Chan: "
    \<lbrakk> 
      leaf stpool \<pi> ;
      stpool \<pi> = Some (LET x = CHAN \<lparr>\<rparr> in e, \<rho>, \<kappa>)
    \<rbrakk> \<Longrightarrow>
    stpool \<rightarrow> stpool(
      \<pi>;;x \<mapsto> (e, \<rho>(x \<mapsto> \<lbrace>Ch (\<pi>;;x)\<rbrace>), \<kappa>)
    )
  " |
  Concur_Let_Spawn: "
    \<lbrakk> 
      leaf stpool \<pi> ;
      stpool \<pi> = Some (LET x = SPAWN e_child in e, \<rho>, \<kappa>)
    \<rbrakk> \<Longrightarrow>
    stpool \<rightarrow> stpool(
      \<pi>;;x \<mapsto> (e, \<rho>(x \<mapsto> \<lbrace>\<rbrace>), \<kappa>), 
      \<pi>;;. \<mapsto> (e_child, \<rho>, \<kappa>) 
    )
  "

      

abbreviation concur_steps :: "state_pool \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where 
  "x \<rightarrow>* y \<equiv> star concur_step x y"
  
definition send_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "send_sites stpool ch = {\<pi>. \<exists> x x_evt e \<kappa> \<rho> x_ch x_m \<rho>_evt. 
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and> 
    \<rho> x_evt = Some \<lbrace>Send_Evt x_ch x_m, \<rho>_evt\<rbrace> \<and> 
    \<rho>_evt x_ch = Some \<lbrace>ch\<rbrace>
  }"
  
definition recv_sites :: "state_pool \<Rightarrow> chan \<Rightarrow> control_path set" where
  "recv_sites stpool ch = {\<pi>. \<exists> x x_evt e \<kappa> \<rho> x_ch \<rho>_evt. 
    stpool \<pi> = Some (LET x = SYNC x_evt in e, \<rho>, \<kappa>) \<and> 
    \<rho> x_evt = Some \<lbrace>Recv_Evt x_ch, \<rho>_evt\<rbrace> \<and> 
    \<rho>_evt x_ch = Some \<lbrace>ch\<rbrace>
  }"
    
  
fun channel_exists :: "state_pool \<Rightarrow> chan \<Rightarrow> bool" where
  "channel_exists stpool (Ch \<pi>) \<longleftrightarrow> (\<exists> x e \<rho> \<kappa>. stpool \<pi> = Some (LET x = CHAN \<lparr>\<rparr> in e, \<rho>, \<kappa>))"
  
definition state_pool_possible :: "exp \<Rightarrow> state_pool \<Rightarrow> bool" where
  "state_pool_possible e stpool \<longleftrightarrow> [[] \<mapsto> (e, Map.empty, [])] \<rightarrow>* stpool"
  
definition one_shot :: "exp \<Rightarrow> var \<Rightarrow> bool" where
  "one_shot e x \<longleftrightarrow> (\<forall> stpool \<pi>. 
    state_pool_possible e stpool \<longrightarrow>
    (* channel_exists stpool (Ch (\<pi>;;x)) \<longrightarrow> *) (*chan_exists doesn't seem necessary*)
    card (send_sites stpool (Ch (\<pi>;;x))) \<le> 1
  )"
  
definition single_side :: "(state_pool \<Rightarrow> chan \<Rightarrow> control_path set) \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  "single_side sites_of e x \<longleftrightarrow> (\<forall> stpool \<pi> \<pi>_1 \<pi>_2 .
    state_pool_possible e stpool \<longrightarrow>
    (* channel_exists stpool (Ch (\<pi>;;x)) \<longrightarrow> *)
    \<pi>_1 \<in> (sites_of stpool (Ch (\<pi>;;x))) \<longrightarrow>
    \<pi>_2 \<in> (sites_of stpool (Ch (\<pi>;;x))) \<longrightarrow>
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

end
