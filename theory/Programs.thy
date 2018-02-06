theory Programs
  imports Main "~~/src/HOL/Library/Sublist" "~~/src/HOL/Eisbach/Eisbach_Tools"
    Syntax 
    Semantics Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Analysis Abstract_Communication_Analysis
    Communication_Analysis
begin


definition infinite_prog where
  "infinite_prog \<equiv> normalize (
    $LET (Var ''ch'') = $CHAN \<lparr>\<rparr> in
    $LET (Var ''u'') = $SPAWN (
      $APP ($FN (Var ''f'') (Var ''x'') .
        $LET (Var ''u'') = $SYNC ($SEND EVT ($(Var ''ch'')) ($(Var ''x''))) in  
        ($APP ($(Var ''f'')) ($(Var ''x'')))  
      ) $\<lparr>\<rparr>
    ) in
    $LET (Var ''u'') = $SPAWN (
      $APP ($FN (Var ''f'') (Var ''x'') .
        $LET (Var ''r'') = $SYNC ($RECV EVT ($(Var ''ch''))) in  
        ($APP ($(Var ''f'')) ($(Var ''x'')))  
      ) $\<lparr>\<rparr>
    ) in
    $\<lparr>\<rparr>
  )"

value "infinite_prog"
(***
LET Var ''g100'' = CHAN \<lparr>\<rparr> in 
LET Var ''g101'' = SPAWN 
        LET Var ''g102'' = FN Var ''g103'' Var ''g104'' . 
                LET Var ''g105'' = SEND EVT Var ''g100'' Var ''g104'' in 
                LET Var ''g106'' = SYNC Var ''g105'' in 
                LET Var ''g107'' = APP Var ''g103'' Var ''g104'' in 
                RESULT Var ''g107'' 
        in 
        LET Var ''g108'' = \<lparr>\<rparr> in 
        LET Var ''g109'' = APP Var ''g102'' Var ''g108'' in 
        RESULT Var ''g109'' 
in 
LET Var ''g110'' = SPAWN 
        LET Var ''g111'' = FN Var ''g112'' Var ''g113'' . 
                LET Var ''g114'' = RECV EVT Var ''g100'' in 
                LET Var ''g115'' = SYNC Var ''g114'' in 
                LET Var ''g116'' = APP Var ''g112'' Var ''g113'' in 
                RESULT Var ''g116'' 
        in 
        LET Var ''g117'' = \<lparr>\<rparr> in 
        LET Var ''g118'' = APP Var ''g111'' Var ''g117'' in 
        RESULT Var ''g118'' 
in 
LET Var ''g119'' = \<lparr>\<rparr> in 
RESULT Var ''g119''
***)

theorem infinite_prog_single_sender: "
   \<E> \<rightarrow>* \<E>' \<Longrightarrow>
   \<E> = [[] \<mapsto> \<langle>infinite_one_to_one_prog;Map.empty;[]\<rangle>] \<longrightarrow>
   single_proc (send_paths \<E>' (Ch [] (Var ''g100'')))
"
  apply (simp add: single_proc_def, auto)
  sorry
(*
strategy:

if 
  prefixes hold for \<E> and \<E> \<rightarrow> \<E>', where \<E>' = \<E>[\<pi>;;`x \<mapsto> ...], 
then 
  prefixes hold for \<E>'.

if 
  infinite loop has no recursive call inside spawn.
then
  each step inside loop only appends `x label.

if 
  prefixes hold for \<E> and \<E> \<rightarrow> \<E>' where the new path is inside the infinite loop w/out recursive call inside spawn,
then 
  prefixes hold for \<E> and \<E> \<rightarrow> \<E>', where \<E>' = \<E>[\<pi>;;`x \<mapsto> ...]
thus 
  prefixes hold for \<E>' 

*)


theorem infinite_prog_single_receiver: "
  [[] \<mapsto> \<langle>infinite_one_to_one_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<longrightarrow>
   single_proc (recv_paths \<E>' (Ch [] (Var ''g100'')))
"
sorry

theorem "
  start_state infinite_prog \<rightarrow>* \<E>' 
  \<Longrightarrow>
  one_to_one \<E>' (Ch [] (Var ''g100''))
"
  apply (simp add: one_to_one_def, auto)
  using infinite_prog_single_sender apply blast
  using infinite_prog_single_receiver apply blast
done


definition infinite_prog_\<V> :: "abstract_value_env" where 
  "infinite_prog_\<V> \<equiv> (\<lambda> _ . {})(
    Var ''g100'' := {^Chan (Var ''g100'')}, 

    Var ''g101'' := {^\<lparr>\<rparr>},
    Var ''g102'' := {^(Abs (Var ''g103'') (Var ''g104'') (
      LET Var ''g105'' = SEND EVT (Var ''g100'') (Var ''g104'') in 
      LET Var ''g106'' = SYNC Var ''g105'' in 
      LET Var ''g107'' = APP (Var ''g103'') (Var ''g104'') in 
      RESULT Var ''g107'' 
    ))},
    Var ''g103'' := {^(Abs (Var ''g103'') (Var ''g104'') (
      LET Var ''g105'' = SEND EVT (Var ''g100'') (Var ''g104'') in 
      LET Var ''g106'' = SYNC Var ''g105'' in 
      LET Var ''g107'' = APP (Var ''g103'') (Var ''g104'') in 
      RESULT Var ''g107''
    ))}, Var ''g104'' := {^\<lparr>\<rparr>},
    Var ''g105'' := {^(Send_Evt (Var ''g100'') (Var ''g104''))},
    Var ''g106'' := {^\<lparr>\<rparr>}, Var ''g107'' := {},
    Var ''g108'' := {^\<lparr>\<rparr>}, Var ''g109'' := {},

    Var ''g110'' := {^\<lparr>\<rparr>},
    Var ''g111'' := {^(Abs (Var ''g112'') (Var ''g113'') (
              LET Var ''g114'' = RECV EVT Var ''g100'' in 
              LET Var ''g115'' = SYNC Var ''g114'' in 
              LET Var ''g116'' = APP (Var ''g112'') (Var ''g113'') in 
              RESULT Var ''g116'' 
    ))},
    Var ''g112'' := {^(Abs (Var ''g112'') (Var ''g113'') (
              LET Var ''g114'' = RECV EVT Var ''g100'' in 
              LET Var ''g115'' = SYNC Var ''g114'' in 
              LET Var ''g116'' = APP (Var ''g112'') (Var ''g113'') in 
              RESULT Var ''g116'' 
    ))}, Var ''g113'' := {^\<lparr>\<rparr>},
    Var ''g114'' := {^(Recv_Evt (Var ''g100''))},
    Var ''g115'' := {^\<lparr>\<rparr>}, Var ''g116'' := {},
    Var ''g117'' := {^\<lparr>\<rparr>}, Var ''g118'' := {}
  )"

definition infinite_prog_\<C> :: "abstract_value_env" where 
  "infinite_prog_\<C>  \<equiv> (\<lambda> _ . {})(
    Var ''g100'' := {^\<lparr>\<rparr>}
  )"


theorem infinite_prog_has_intuitive_avf_analysis: "
  (infinite_prog_\<V>, infinite_prog_\<C>) \<Turnstile>\<^sub>e infinite_prog 
"
sorry

theorem infinite_prog_has_single_sender_communication_analysis: "
  single_proc (abstract_send_paths (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) (Var ''g100''))
"
   apply (simp add: single_proc_def, auto)
sorry

theorem infinite_prog_has_single_receiver_communication_analysis: "
  single_proc (abstract_recv_paths (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) (Var ''g100''))
"
sorry

theorem infinite_prog_has_one_to_one_communication_analysis: "
  abstract_one_to_one (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) (Var ''g100'')
"
 apply (simp add: abstract_one_to_one_def, auto)
 apply (simp add: infinite_prog_has_single_sender_communication_analysis)
 apply (simp add: infinite_prog_has_single_receiver_communication_analysis)
done      


(**
(* finite representation of paths *)
datatype finite_path =
  Empty |
  Atom control_label |
  Concat finite_path finite_path |
  Star finite_path


(*** TO DO ***)
fun control_path_set_from_finite_path :: "finite_path \<Rightarrow> control_path set" where
 "control_path_set_from_finite_path Empty = {[]}" | 
 "control_path_set_from_finite_path (Atom l) = {[]}" |
 "control_path_set_from_finite_path (Concat p1 p2) = {[]}" |
 "control_path_set_from_finite_path (Star p) = {[]}"

fun control_path_set :: "finite_path set \<Rightarrow> control_path set" where
  "control_path_set ps = UNION ps (\<lambda> p . control_path_set_from_finite_path p)"

theorem paths_are_finitely_representable: "
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e) \<Longrightarrow>
  \<exists> p_set . finite (p_set) \<and> \<pi> \<in> (control_path_set p_set)
"
  sorry

fun abstract_prefix :: "finite_path \<Rightarrow> finite_path \<Rightarrow> bool" where
  "abstract_prefix p1 p2 = True"


lemma linear_finite_path_implies_linear_control_path: "
  \<lbrakk>
    finite (p_set);
    p1 \<in> p_set; p2 \<in> p_set;
    (abstract_prefix p1 p2 \<or> abstract_prefix p2 p1);
    \<pi>\<^sub>1 \<in> (control_path_set p_set);
    \<pi>\<^sub>2 \<in> (control_path_set p_set)
  \<rbrakk> \<Longrightarrow>
  prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<or> prefix \<pi>\<^sub>1 \<pi>\<^sub>2
"
  sorry
**)


    
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


method condition_split = (
  match premises in 
    I: "(if P then _ else _) = Some _" for P \<Rightarrow> \<open>cases P\<close>
, auto)


method leaf_elim_loop for m :: state_pool and stpool :: state_pool and l :: control_path uses I = (
  match (m) in 
    "Map.empty" \<Rightarrow> \<open> fail \<close> \<bar>
    "m'((p :: control_path) \<mapsto> (_ :: state))" for m' p \<Rightarrow> 
        \<open>((insert I, (drule leaf_elim[of stpool l p]), auto); leaf_elim_loop m' stpool l I: I)\<close>
)

method leaf_elim_search = (
  match premises in 
    I: "leaf stpool lf" for stpool lf \<Rightarrow> \<open>(leaf_elim_loop stpool stpool lf I: I)\<close>
)

(*
method topo_solve = 
  (
    (erule star.cases, auto),
    (simp add: recv_sites_def send_sites_def leaf_def, auto),
    (condition_split+),
    (erule concur_step.cases, auto),
    (erule seq_step.cases),
    (condition_split | leaf_elim_search)+
  )

definition prog_one where 
  "prog_one = 
    LET a = CHAN \<lparr>\<rparr> in
    LET b = SPAWN (
      LET c = CHAN \<lparr>\<rparr> in
      LET d = SEND EVT a b in
      LET w = SYNC d in
      RESULT d
    ) in
    LET e = RECV EVT a in
    LET f = SYNC e in
    RESULT f
  "
 
theorem prog_one_properties: "single_receiver prog_one a"
  apply (unfold single_receiver_def single_side_def single_side'_def recv_sites_def prog_one_def)
  apply auto
  apply topo_solve+
done


theorem prog_one_properties2: "single_sender prog_one a"
  apply (unfold single_sender_def single_side_def single_side'_def send_sites_def prog_one_def)
  apply auto
  apply topo_solve+
done

definition prog_two where 
  "prog_two = 
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
    
definition prog_three where 
  "prog_three = 
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
  
definition prog_four where
  "prog_four = 
    .LET a = .FN f x .
      .CASE .x
      LEFT b |> .RIGHT (.APP .f .b)
      RIGHT b |> .LEFT .b
    in
    .APP .a (.LEFT (.LEFT (.LEFT (.RIGHT .\<lparr>\<rparr>))))
  "


*)

end
