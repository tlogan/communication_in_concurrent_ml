theory Program1
 imports Main 
  Syntax
  Static_Semantics
  Static_Framework
  Static_Communication_Analysis
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
abbreviation server where "server \<equiv> Var ''server''"


definition program where "program = (

  $LET no_chan_loop = ($FN no_chan_loop x .
    $CASE $x
    LEFT y |> $APP $no_chan_loop $y
    RIGHT z |> $\<lparr>\<rparr>
  ) in

  $LET make_server = ($FN make_server x .
    $LET ch = $CHAN \<lparr>\<rparr> in
    $LET z = $APP $no_chan_loop ($LEFT ($LEFT ($RIGHT $\<lparr>\<rparr>))) in
    $LET loop = ($FN loop x .
      $LET pair = $SYNC ($RECV EVT $ch) in
      $LET w = $FST $pair in
      $LET replCh = $SND $pair in 
      $LET z = $SYNC ($SEND EVT $replCh $x) in
      $APP $loop $w
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

  $LET server = $APP $make_server $\<lparr>\<rparr> in
  $LET z = $SPAWN
    $APP $call_server $\<lparr>$server, $RIGHT $\<lparr>\<rparr>\<rparr>
  in
  $LET z = $SPAWN
    $LET z = $APP $call_server $\<lparr>$server, $LEFT ($RIGHT $\<lparr>\<rparr>)\<rparr> in
    $LET z = $APP $call_server $\<lparr>$server, ($RIGHT $\<lparr>\<rparr>)\<rparr> in
    $z
  in
  $LET z = $APP $call_server $\<lparr>$server, $LEFT ($RIGHT $\<lparr>\<rparr>)\<rparr> in
  $\<lparr>\<rparr>
)"

value "normalize program"

abbreviation g100 where "g100 \<equiv> Var ''g100''"
abbreviation g101 where "g101 \<equiv> Var ''g101''"
abbreviation g102 where "g102 \<equiv> Var ''g102''"
abbreviation g103 where "g103 \<equiv> Var ''g103''"
abbreviation g104 where "g104 \<equiv> Var ''g104''"
abbreviation g105 where "g105 \<equiv> Var ''g105''"
abbreviation g106 where "g106 \<equiv> Var ''g106''"
abbreviation g107 where "g107 \<equiv> Var ''g107''"
abbreviation g108 where "g108 \<equiv> Var ''g108''"
abbreviation g109 where "g109 \<equiv> Var ''g109''"
abbreviation g110 where "g110 \<equiv> Var ''g110''"
abbreviation g111 where "g111 \<equiv> Var ''g111''"
abbreviation g112 where "g112 \<equiv> Var ''g112''"
abbreviation g113 where "g113 \<equiv> Var ''g113''"
abbreviation g114 where "g114 \<equiv> Var ''g114''"
abbreviation g115 where "g115 \<equiv> Var ''g115''"
abbreviation g116 where "g116 \<equiv> Var ''g116''"
abbreviation g117 where "g117 \<equiv> Var ''g117''"
abbreviation g118 where "g118 \<equiv> Var ''g118''"
abbreviation g119 where "g119 \<equiv> Var ''g119''"
abbreviation g120 where "g120 \<equiv> Var ''g120''"
abbreviation g121 where "g121 \<equiv> Var ''g121''"
abbreviation g122 where "g122 \<equiv> Var ''g122''"
abbreviation g123 where "g123 \<equiv> Var ''g123''"
abbreviation g124 where "g124 \<equiv> Var ''g124''"
abbreviation g125 where "g125 \<equiv> Var ''g125''"
abbreviation g126 where "g126 \<equiv> Var ''g126''"
abbreviation g127 where "g127 \<equiv> Var ''g127''"
abbreviation g128 where "g128 \<equiv> Var ''g128''"
abbreviation g129 where "g129 \<equiv> Var ''g129''"
abbreviation g130 where "g130 \<equiv> Var ''g130''"
abbreviation g131 where "g131 \<equiv> Var ''g131''"
abbreviation g132 where "g132 \<equiv> Var ''g132''"
abbreviation g133 where "g133 \<equiv> Var ''g133''"
abbreviation g134 where "g134 \<equiv> Var ''g134''"
abbreviation g135 where "g135 \<equiv> Var ''g135''"
abbreviation g136 where "g136 \<equiv> Var ''g136''"
abbreviation g137 where "g137 \<equiv> Var ''g137''"
abbreviation g138 where "g138 \<equiv> Var ''g138''"
abbreviation g139 where "g139 \<equiv> Var ''g139''"
abbreviation g140 where "g140 \<equiv> Var ''g140''"
abbreviation g141 where "g141 \<equiv> Var ''g141''"
abbreviation g142 where "g142 \<equiv> Var ''g142''"
abbreviation g143 where "g143 \<equiv> Var ''g143''"
abbreviation g144 where "g144 \<equiv> Var ''g144''"
abbreviation g145 where "g145 \<equiv> Var ''g145''"
abbreviation g146 where "g146 \<equiv> Var ''g146''"
abbreviation g147 where "g147 \<equiv> Var ''g147''"
abbreviation g148 where "g148 \<equiv> Var ''g148''"
abbreviation g149 where "g149 \<equiv> Var ''g149''"
abbreviation g150 where "g150 \<equiv> Var ''g150''"
abbreviation g151 where "g151 \<equiv> Var ''g151''"
abbreviation g152 where "g152 \<equiv> Var ''g152''"
abbreviation g153 where "g153 \<equiv> Var ''g153''"
abbreviation g154 where "g154 \<equiv> Var ''g154''"
abbreviation g155 where "g155 \<equiv> Var ''g155''"
abbreviation g156 where "g156 \<equiv> Var ''g156''"
abbreviation g157 where "g157 \<equiv> Var ''g157''"
abbreviation g158 where "g158 \<equiv> Var ''g158''"
abbreviation g159 where "g159 \<equiv> Var ''g159''"                       
abbreviation g160 where "g160 \<equiv> Var ''g160''"
abbreviation g161 where "g161 \<equiv> Var ''g161''"
abbreviation g162 where "g162 \<equiv> Var ''g162''"
abbreviation g163 where "g163 \<equiv> Var ''g163''"
abbreviation g164 where "g164 \<equiv> Var ''g164''"
abbreviation g165 where "g165 \<equiv> Var ''g165''"
abbreviation g166 where "g166 \<equiv> Var ''g166''"
abbreviation g167 where "g167 \<equiv> Var ''g167''"
abbreviation g168 where "g168 \<equiv> Var ''g168''"
abbreviation g169 where "g169 \<equiv> Var ''g169''"



definition anf_program where "anf_program = (
LET g100 = FN g101 g102 . 

  LET g103 = CASE g102 

    LEFT g104 |> 
      LET g105 = APP g101 g104 in 
      RESULT g105 

    RIGHT g106 |> 
      LET g107 = \<lparr>\<rparr> in 
      RESULT g107 

  in 
  RESULT g103 
in 

LET g108 = FN g109 g110 . 
  LET g111 = CHAN \<lparr>\<rparr> in 
  LET g112 = \<lparr>\<rparr> in 
  LET g113 = RIGHT g112 in 
  LET g114 = LEFT g113 in 
  LET g115 = LEFT g114 in 
  LET g116 = APP g100 g115 in 
  LET g117 = FN g118 g119 . 
    LET g120 = RECV EVT g111 in 
    LET g121 = SYNC g120 in 
    LET g122 = FST g121 in 
    LET g123 = SND g121 in 
    LET g124 = SEND EVT g123 g119 in 
    LET g125 = SYNC g124 in 
    LET g126 = APP g118 g122 in 
    RESULT g126 
  in 
  LET g127 = SPAWN 
    LET g128 = \<lparr>\<rparr> in 
    LET g129 = RIGHT g128 in 
    LET g130 = APP g117 g129 in 
    RESULT g130 
  in 
  RESULT g111 
in 
LET g131 = FN g132 g133 . 
  LET g134 = FST g133 in 
  LET g135 = SND g133 in 
  LET g136 = CHAN \<lparr>\<rparr> in 
  LET g137 = \<lparr>g135, g136\<rparr> in 
  LET g138 = SEND EVT g134 g137 in 
  LET g139 = SYNC g138 in 
  LET g140 = RECV EVT g136 in 
  LET g141 = SYNC g140 in 
  RESULT g141 
in 
LET g142 = \<lparr>\<rparr> in 
LET g143 = APP g108 g142 in 
LET g144 = SPAWN 
  LET g145 = \<lparr>\<rparr> in 
  LET g146 = RIGHT g145 in
  LET g147 = \<lparr>g143, g146\<rparr> in
  LET g148 = APP g131 g147 in
  RESULT g148 
in
LET g149 = SPAWN 
  LET g150 = \<lparr>\<rparr> in
  LET g151 = RIGHT g150 in
  LET g152 = LEFT g151 in
  LET g153 = \<lparr>g143, g152\<rparr> in
  LET g154 = APP g131 g153 in
  LET g155 = \<lparr>\<rparr> in
  LET g156 = RIGHT g155 in
  LET g157 = \<lparr>g143, g156\<rparr> in
  LET g158 = APP g131 g157 in
  RESULT g158 
in
LET g159 = \<lparr>\<rparr> in
LET g160 = RIGHT g159 in
LET g161 = LEFT g160 in
LET g162 = \<lparr>g143, g161\<rparr> in
LET g163 = APP g131 g162 in
LET g164 = \<lparr>\<rparr> in
RESULT g164
)"

definition C where "C =
  (\<lambda> _ . {})(
    g111 := {^Pair g135 g136},
    g136 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    }
  )
"

definition V where "V =
  (\<lambda> _ . {})(
    g100 := {^Abs g101 g102 (
      LET g103 = CASE g102 
        LEFT g104 |> 
          LET g105 = APP g101 g104 in 
          RESULT g105
        RIGHT g106 |> 
          LET g107 = \<lparr>\<rparr> in 
          RESULT g107
      in 
      RESULT g103)},
    g101 :=  {^Abs g101 g102 (
      LET g103 = CASE g102 
        LEFT g104 |> 
          LET g105 = APP g101 g104 in 
          RESULT g105
        RIGHT g106 |> 
          LET g107 = \<lparr>\<rparr> in 
          RESULT g107
      in 
      RESULT g103
    )},
    g102 := {^Left g114},
    g103 := {^\<lparr>\<rparr>},
    g104 := {^Left g113, ^Right g112},
    g105 := {^\<lparr>\<rparr>},
    g106 := {^\<lparr>\<rparr>},
    g107 := {^\<lparr>\<rparr>},
    g108 := {^Abs g109 g110 (
      LET g111 = CHAN \<lparr>\<rparr> in 
      LET g112 = \<lparr>\<rparr> in 
      LET g113 = RIGHT g112 in 
      LET g114 = LEFT g113 in 
      LET g115 = LEFT g114 in 
      LET g116 = APP g100 g115 in 
      LET g117 = FN g118 g119 . 
        LET g120 = RECV EVT g111 in 
        LET g121 = SYNC g120 in 
        LET g122 = FST g121 in 
        LET g123 = SND g121 in 
        LET g124 = SEND EVT g123 g119 in 
        LET g125 = SYNC g124 in 
        LET g126 = APP g118 g125 in 
        RESULT g126 
      in 
      LET g127 = SPAWN 
        LET g128 = \<lparr>\<rparr> in 
        LET g129 = RIGHT g128 in 
        LET g130 = APP g117 g129 in 
        RESULT g130 
      in 
      RESULT g111 
    )},
    g109 :=  {^Abs g109 g110 (
      LET g111 = CHAN \<lparr>\<rparr> in 
      LET g112 = \<lparr>\<rparr> in 
      LET g113 = RIGHT g112 in 
      LET g114 = LEFT g113 in 
      LET g115 = LEFT g114 in 
      LET g116 = APP g100 g115 in 
      LET g117 = FN g118 g119 . 
        LET g120 = RECV EVT g111 in 
        LET g121 = SYNC g120 in 
        LET g122 = FST g121 in 
        LET g123 = SND g121 in 
        LET g124 = SEND EVT g123 g119 in 
        LET g125 = SYNC g124 in 
        LET g126 = APP g118 g125 in 
        RESULT g126 
      in 
      LET g127 = SPAWN 
        LET g128 = \<lparr>\<rparr> in 
        LET g129 = RIGHT g128 in 
        LET g130 = APP g117 g129 in 
        RESULT g130 
      in 
      RESULT g111 
    )},
    g110 := {^\<lparr>\<rparr>},
    g111 := {^Chan g111},
    g112 := {^\<lparr>\<rparr>},
    g113 := {^Right g112},
    g114 := {^Left g113},
    g115 := {^Left g114},
    g116 := {},
    g117 :=  {^Abs g118 g119 (
      LET g120 = RECV EVT g111 in 
      LET g121 = SYNC g120 in 
      LET g122 = FST g121 in 
      LET g123 = SND g121 in 
      LET g124 = SEND EVT g123 g119 in 
      LET g125 = SYNC g124 in 
      LET g126 = APP g118 g125 in 
      RESULT g126 
    )},
    g118 :=  {^Abs g118 g119 (
      LET g120 = RECV EVT g111 in 
      LET g121 = SYNC g120 in 
      LET g122 = FST g121 in 
      LET g123 = SND g121 in 
      LET g124 = SEND EVT g123 g119 in 
      LET g125 = SYNC g124 in 
      LET g126 = APP g118 g125 in 
      RESULT g126 
    )},
    g119 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g120 := {^Recv_Evt g111},
    g121 := {^Pair g135 g136},
    g122 := {
      ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g123 := {^Chan g136},
    g124 := {^Send_Evt g123 g119},
    g125 := {^\<lparr>\<rparr>},
    g126 := {},
    g127 := {^\<lparr>\<rparr>},
    g128 := {^\<lparr>\<rparr>},
    g129 := {^Right g128},
    g130 := {},
    g131 :=  {^Abs g132 g133 (
      LET g134 = FST g133 in 
      LET g135 = SND g133 in 
      LET g136 = CHAN \<lparr>\<rparr> in LET g137 = \<lparr>g135, g136\<rparr> in 
      LET g138 = SEND EVT g134 g137 in 
      LET g139 = SYNC g138 in 
      LET g140 = RECV EVT g136 in 
      LET g141 = SYNC g140 in 
      RESULT g141 
    )},
    g132 :=  {^Abs g132 g133 (
      LET g134 = FST g133 in 
      LET g135 = SND g133 in 
      LET g136 = CHAN \<lparr>\<rparr> in LET g137 = \<lparr>g135, g136\<rparr> in 
      LET g138 = SEND EVT g134 g137 in 
      LET g139 = SYNC g138 in 
      LET g140 = RECV EVT g136 in 
      LET g141 = SYNC g140 in 
      RESULT g141 
    )},
    g133 := {
      ^Pair g143 g146, ^Pair g143 g152, 
      ^Pair g143 g156, ^Pair g143 g161
    },
    g134 := {^Chan g111},
    g135 := {^Right g145},
    g136 := {^Chan g136},
    g137 := {^Pair g135 g136},
    g138 := {^Send_Evt g134 g137},
    g139 := {^\<lparr>\<rparr>},
    g140 := {^Recv_Evt g136},
    g141 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g142 := {^\<lparr>\<rparr>},
    g143 := {^Chan g111},
    g144 := {^\<lparr>\<rparr>},
    g145 := {^\<lparr>\<rparr>},
    g146 := {^Right g145},
    g147 := {^Pair g143 g146},
    g148 := {
      ^Right g128,
      ^Left g151, ^Right g155, ^Left g160
    },
    g149 := {^\<lparr>\<rparr>},
    g150 := {^\<lparr>\<rparr>},
    g151 := {^Right g150},
    g152 := {^Left g151},
    g153 := {^Pair g143 g152},
    g154 := {
      ^Right g128, ^Right g145, 
      ^Left g160
    },
    g155 := {^\<lparr>\<rparr>},
    g156 := {^Right g156},
    g157 := {^Pair g143 g156},
    g158 := {
      ^Right g145, 
      ^Left g160,
      ^Left g151
    },
    g159 := {^\<lparr>\<rparr>},
    g160 := {^Right g159},
    g161 := {^Left g160},
    g162 := {^Pair g143 g161},
    g163 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155
    },
    g164 := {^\<lparr>\<rparr>}
  )
"

definition F :: flow_set where "F = {

  (NLet g103, ECall g103, NLet g105),
  (NLet g105, ECall g105, NLet g103),
  (NResult g103, EReturn g105, NResult g105),
  (NResult g105, EReturn g103, NResult g103),
  (NLet g107, ENext, NResult g107),
  (NResult g107, EReturn g103, NResult g103),
  (NLet g103, ECall g103, NLet g107),
  (NLet g100, ENext, NLet g108),
  (NLet g111, ENext, NLet g112),
  (NLet g112, ENext, NLet g113),
  (NLet g113, ENext, NLet g114),
  (NLet g114, ENext, NLet g115),
  (NLet g116, ECall g116, NLet g103),
  (NResult g103, EReturn g116, NLet g117),
  (NLet g120, ENext, NLet g121),
  (NLet g121, ENext, NLet g122),
  (NLet g122, ENext, NLet g123),
  (NLet g123, ENext, NLet g124),
  (NLet g124, ENext, NLet g125),
  (NLet g125, ESend g124, NLet g141),
  (NLet g125, ENext, NLet g126),
  (NLet g126, ECall g126, NLet g120),
  (NResult g126, EReturn g126, NResult g126),
  (NLet g117, ENext, NLet g127),
  (NLet g127, ESpawn, NLet g128),
  (NLet g128, ENext, NLet g129),
  (NLet g129, ENext, NLet g130),
  (NLet g130, ECall g130, NLet g120),
  (NResult g126, EReturn g130, NResult g130),
  (NLet g127, ENext, NResult g111),
  (NLet g108, ENext, NLet g131),
  (NLet g134, ENext, NLet g135),
  (NLet g135, ENext, NLet g136),
  (NLet g136, ENext, NLet g137),
  (NLet g137, ENext, NLet g138),
  (NLet g138, ENext, NLet g139),
  (NLet g139, ESend g138, NLet g121),
  (NLet g139, ENext, NLet g140),
  (NLet g140, ENext, NLet g141),
  (NLet g141, ENext, NResult g141),
  (NLet g131, ENext, NLet g142),
  (NLet g142, ENext, NLet g143),
  (NLet g143, ENext, NLet g144),
  (NLet g144, ESpawn, NLet g145),
  (NLet g145, ENext, NLet g146),
  (NLet g146, ENext, NLet g147),
  (NLet g147, ENext, NLet g148),
  (NLet g148, ECall g148, NLet g134),
  (NResult g141, EReturn g148, NResult g148),
  (NLet g144, ENext, NLet g149),
  (NLet g149, ESpawn, NLet g150),
  (NLet g150, ENext, NLet g151),
  (NLet g151, ENext, NLet g152),
  (NLet g153, ENext, NLet g154),
  (NLet g154, ECall g154, NLet g134),
  (NResult g141, EReturn g154, NLet g155),
  (NLet g155, ENext, NLet g156),
  (NLet g156, ENext, NLet g157),
  (NLet g157, ENext, NLet g158),
  (NLet g158, ECall g158, NLet g134),
  (NResult g141, EReturn g158, NResult g158),
  (NLet g149, ENext, NLet g159),
  (NLet g159, ENext, NLet g160),
  (NLet g160, ENext, NLet g161),
  (NLet g161, ENext, NLet g162),
  (NLet g163, ECall g163, NLet g134),
  (NResult g141, EReturn g163, NLet g164),
  (NLet g164, ENext, NResult g164)
}"

definition Ln_g111 :: node_map where "Ln_g111 = 
  (\<lambda> _ . {})(
    NLet g108 := {},
    NLet g111 := {},
    NLet g112 := {g111},
    NLet g113 := {g111},
    NLet g114 := {g111},
    NLet g115 := {g111},
    NLet g116 := {g111},
    NLet g117 := {g111},
    NLet g120 := {g111, g118},
    NLet g121 := {g120, g118},
    NLet g122 := {g118},
    NLet g123 := {g118},
    NLet g124 := {g118},
    NLet g125 := {g118},
    NLet g126 := {g118},
    NResult g126 := {},
    NLet g127 := {g111, g117},
    NLet g128 := {g117},
    NLet g129 := {g117},
    NLet g130 := {g117},
    NResult g130 := {},
    NResult g111 := {g111},
    NLet g131 := {},
    NLet g134 := {g133},
    NLet g135 := {g134},
    NLet g136 := {g134},
    NLet g137 := {g134},
    NLet g138 := {g134},
    NLet g139 := {g138},
    NLet g140 := {},
    NLet g141 := {},
    NResult g141 := {},
    NLet g142 := {},
    NLet g143 := {},
    NLet g144 := {g143},
    NLet g145 := {g143},
    NLet g146 := {g143},
    NLet g147 := {g143},
    NLet g148 := {g147},
    NResult g148 := {},
    NLet g149 := {g143},
    NLet g150 := {g143},
    NLet g151 := {g143},
    NLet g152 := {g143},
    NLet g153 := {g143},
    NLet g154 := {g143, g153},
    NLet g155 := {g143},
    NLet g156 := {g143},
    NLet g157 := {g143},
    NLet g158 := {g157},
    NResult g158 := {},
    NLet g159 := {g143},
    NLet g160 := {g143},
    NLet g161 := {g143},
    NLet g162 := {g143},
    NLet g163 := {g162},
    NLet g164 := {},
    NResult g164 := {}
  )
"

definition Lx_g111 :: node_map where "Lx_g111 = 
  (\<lambda> _ . {})(
    NLet g108 := {},
    NLet g111 := {g111},
    NLet g112 := {g111},
    NLet g113 := {g111},
    NLet g114 := {g111},
    NLet g115 := {g111},
    NLet g116 := {g111},
    NLet g117 := {g111, g117},
    NLet g120 := {g120, g118},
    NLet g121 := {g118},
    NLet g122 := {g118},
    NLet g123 := {g118},
    NLet g124 := {g118},
    NLet g125 := {g118},
    NLet g126 := {},
    NResult g126 := {},
    NLet g127 := {g111, g117},
    NLet g128 := {g117},
    NLet g129 := {g117},
    NLet g130 := {},
    NResult g130 := {},
    NResult g111 := {},
    NLet g131 := {},
    NLet g134 := {g134},
    NLet g135 := {g134},
    NLet g136 := {g134},
    NLet g137 := {g134},
    NLet g138 := {g138},
    NLet g139 := {},
    NLet g140 := {},
    NLet g141 := {},
    NResult g141 := {},
    NLet g142 := {},
    NLet g143 := {g143},
    NLet g144 := {g143},
    NLet g145 := {g143},
    NLet g146 := {g143},
    NLet g147 := {g147},
    NLet g148 := {},
    NResult g148 := {},
    NLet g149 := {g143},
    NLet g150 := {g143},
    NLet g151 := {g143},
    NLet g152 := {g143},
    NLet g153 := {g143, g153},
    NLet g154 := {g143},
    NLet g155 := {g143},
    NLet g156 := {g143},
    NLet g157 := {g157},
    NLet g158 := {},
    NResult g158 := {},
    NLet g159 := {g143},
    NLet g160 := {g143},
    NLet g161 := {g143},
    NLet g162 := {g162},
    NLet g163 := {},
    NLet g164 := {},
    NResult g164 := {}
  )
"

definition Ln_g136 :: node_map where "Ln_g136 = 
  (\<lambda> _ . {})(
    NLet g121 := {},
    NLet g122 := {g121},
    NLet g123 := {g121},
    NLet g124 := {g123},
    NLet g125 := {g124},
    NLet g126 := {},
    NResult g126 := {},
    NLet g136 := {},
    NLet g137 := {g136},
    NLet g138 := {g136, g137},
    NLet g139 := {g136, g138},
    NLet g140 := {g136},
    NLet g141 := {g140},
    NResult g141 := {}
  )
"

definition Lx_g136 :: node_map where "Lx_g136 = 
  (\<lambda> _ . {})(
    NLet g121 := {g121},
    NLet g122 := {g121},
    NLet g123 := {g123},
    NLet g124 := {g124},
    NLet g125 := {},
    NLet g126 := {},
    NResult g126 := {},
    NLet g136 := {g136},
    NLet g137 := {g136, g137},
    NLet g138 := {g136, g137},
    NLet g139 := {g136},
    NLet g140 := {g140},
    NLet g141 := {},
    NResult g141 := {}
  )
"


lemma path_with_tangent_call_is_live_for_g111: "
  may_be_static_live_path V F Ln_g111 Lx_g111 (NLet g111) (\<lambda> x . True) [
    (NLet g111, ENext),
    (NLet g112, ENext),
    (NLet g113, ENext),
    (NLet g114, ENext),
    (NLet g115, ENext),
    (NLet g116, ECall g116),
    (NLet g103, ECall g103),
    (NLet g105, ECall g105),
    (NLet g103, ECall g103),
    (NLet g105, ECall g105),
    (NLet g103, ECall g103),
    (NLet g107, ENext),
    (NResult g107, EReturn g103),
    (NResult g103, EReturn g105),
    (NResult g105, EReturn g103),
    (NResult g103, EReturn g105),
    (NResult g105, EReturn g103),
    (NResult g103, EReturn g116),
    (NLet g117, ENext),
    (NLet g127, ESpawn),
    (NLet g128, ENext)
  ]
"
 apply (rule may_be_static_live_path.Step_Next)
 apply (rule may_be_static_live_path.Step_Next)
 apply (rule may_be_static_live_path.Step_Next)
 apply (rule may_be_static_live_path.Step_Next)
 apply (rule may_be_static_live_path.Step_Next)
 apply (rule may_be_static_live_path.Step_Next)
 apply (rule may_be_static_live_path.Pre_Return[of 
   V F Ln_g111 Lx_g111 g103 _ g116 _
   "[(NLet g103, ECall g103), (NLet g105, ECall g105), 
     (NLet g103, ECall g103), (NLet g105, ECall g105), 
     (NLet g103, ECall g103), (NLet g107, ENext), 
     (NResult g107, EReturn g103), (NResult g103, EReturn g105), 
     (NResult g105, EReturn g103), (NResult g103, EReturn g105),
     (NResult g105, EReturn g103)]"
 ]; auto?)
 apply (rule may_be_static_live_path.Step_Next)+
 apply (rule may_be_static_live_path.Edge; auto?)
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )
 apply (
  (rule may_be_static_live_flow.Spawn; auto?),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )
 apply (
  (rule may_be_static_live_flow.Return; auto?),
  (unfold F_def; auto),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Step; auto?)
 apply (rule may_be_static_path.Edge; auto?)
 apply (unfold F_def; auto)+
 apply (erule static_balanced.cases; auto?)
sorry


lemma "
  static_balanced [(NLet g103, ECall g103), 

    (NLet g105, ECall g105),  (NLet g103, ECall g103),


    (NLet g105, ECall g105), (NLet g103, ECall g103),
    (NLet g107, ENext), (NResult g107, EReturn g103), 
    (NResult g103, EReturn g105), (*(NResult g105, EReturn g103), 
    (NResult g103, EReturn g105), (NResult g105, EReturn g103), 
    *)
    (NResult g103, EReturn g116)
  ] \<Longrightarrow>
  False
"

 apply (
   (erule static_balanced.cases; auto?),
   ((match premises in 
      I: "_ = (pre @ _)" for pre \<Rightarrow> 
          \<open>insert I; (cases pre)\<close>
    ); auto)+,
  (rotate_tac -1)?
 )+

done



lemma path_with_server_loop_is_live_for_g111: "
  may_be_static_live_path V F Ln_g111 Lx_g111 (NLet g128) (\<lambda> x . True) [
    (NLet g128, ENext),
    (NLet g129, ENext),
    (NLet g130, ECall g130),
    (NLet g120, ENext),
    (NLet g121, ENext),
    (NLet g122, ENext),
    (NLet g123, ENext),
    (NLet g124, ENext),
    (NLet g125, ENext),
    (NLet g126, ECall g126),
    (NLet g120, ENext),
    (NLet g121, ENext),
    (NLet g122, ENext),
    (NLet g123, ENext),
    (NLet g124, ENext),
    (NLet g125, ENext),
    (NLet g126, ECall g126)
  ]
"
sorry


lemma path_with_chan_message_is_live_for_g136: "
  may_be_static_live_path V F Ln_g136 Lx_g136 (NLet g136) (\<lambda> x . x = (NLet g125)) [
    (NLet g136, ENext),
    (NLet g137, ENext),
    (NLet g138, ENext),
    (NLet g139, ESend g138),
    (NLet g121, ENext),
    (NLet g122, ENext),
    (NLet g123, ENext),
    (NLet g124, ENext)
  ]
"
 apply (rule may_be_static_live_path.Step_Next)+
 apply (rule may_be_static_live_path.Edge; auto?)
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g136_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g136_def; auto),
  (simp add: Set.is_empty_def)
 )+
 apply (rule may_be_static_live_flow.Send; auto?)
 apply (unfold F_def; auto)
 apply (unfold Ln_g136_def; auto)
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g136_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g136_def; auto),
  (simp add: Set.is_empty_def)
 )+
done


lemma path_with_server_loop_is_not_live_for_g136: "
  \<not> may_be_static_live_path V F Ln_g136 Lx_g136 (NLet g136) (\<lambda> x . x = (NLet g125)) [
    (NLet g121, ENext),
    (NLet g122, ENext),
    (NLet g123, ENext),
    (NLet g124, ENext),
    (NLet g125, ENext),
    (NLet g126, ECall g126),
    (NLet g120, ENext),
    (NLet g121, ENext),
    (NLet g122, ENext)
  ]
"
  apply (rule notI)
  apply (erule may_be_static_live_path.cases; auto)
  apply (case_tac pre; auto)
  apply (case_tac list; auto)
  apply (case_tac lista; auto)
  apply (case_tac list; auto)
  apply (case_tac lista; auto)
  apply (case_tac list; auto)
  apply (case_tac lista; auto)
  apply (case_tac list; auto)
  apply (case_tac lista; auto)
done
(*
    (V, C) \<Turnstile>\<^sub>e e;
    static_flow_set V F e \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
*)


end