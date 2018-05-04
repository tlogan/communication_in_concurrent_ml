theory Program1
 imports Main Syntax
begin

abbreviation no_chan_loop where "no_chan_loop \<equiv> Var ''no_chan_loop''"
abbreviation make_server where "make_server \<equiv> Var ''make_server''"
abbreviation ch where "ch \<equiv> Var ''ch''"
abbreviation loop where "loop \<equiv> Var ''loop''"
abbreviation pair where "pair \<equiv> Var ''pair''"
abbreviation replCh where "replCh \<equiv> Var ''replCh''"
abbreviation w where "w \<equiv> Var ''w''"
abbreviation x where "x \<equiv> Var ''x''"
abbreviation y where "y \<equiv> Var ''y''"
abbreviation z where "z \<equiv> Var ''z''"
abbreviation call_server where "call_server \<equiv> Var ''call_server''"


value "normalize (

  $LET no_chan_loop = ($FN no_chan_loop x .
    $CASE $x
    LEFT y |> $APP $no_chan_loop $y
    RIGHT z |> $\<lparr>\<rparr>
  ) in

  $LET make_server = ($FN make_server x .
    $LET ch = $CHAN \<lparr>\<rparr> in
    $LET loop = ($FN loop x .
      $LET pair = $SYNC ($RECV EVT $ch) in
      $LET w = $FST $pair in
      $LET replCh = $SND $pair in 
      $LET z = $SYNC ($SEND EVT $replCh $x) in
      $APP $loop $z
    ) in
    $LET z  = $SPAWN ($APP $loop ($RIGHT $\<lparr>\<rparr>)) in
    $ch
  ) in

  $LET call_server = ($FN call_server pair .
    $LET ch = $FST $pair in
    $LET w = $SND $pair in
    $LET replCh = $CHAN \<lparr>\<rparr> in
    $LET z = $SYNC ($SEND EVT $ch ($\<lparr>$w, $replCh\<rparr>)) in
    $LET y = $SYNC ($RECV EVT $replCh) in
    $y
  ) in

  $\<lparr>\<rparr>
)"

end