theory Programs
  imports Main Syntax Semantics "~~/src/HOL/Library/Sublist" "~~/src/HOL/Eisbach/Eisbach_Tools"
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Analysis
begin


(**** Strategy for deriving analysis of program with infinite paths on a single process ****

- show  



****)
value "($\<lparr>\<rparr>)"
definition infinite_one_to_one_prog where
  "infinite_one_to_one_prog \<equiv> normalize (
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

value "infinite_one_to_one_prog"
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
