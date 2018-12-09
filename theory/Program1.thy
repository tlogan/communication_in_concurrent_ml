theory Program1
 imports Main 
  Syntax
  Static_Semantics
  Static_Communication
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
    g100 := {^Fun g101 g102 (
      LET g103 = CASE g102 
        LEFT g104 |> 
          LET g105 = APP g101 g104 in 
          RESULT g105
        RIGHT g106 |> 
          LET g107 = \<lparr>\<rparr> in 
          RESULT g107
      in 
      RESULT g103)},
    g101 :=  {^Fun g101 g102 (
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
    g102 := {^Left g114, ^Left g113, ^Right g112},
    g103 := {^\<lparr>\<rparr>},
    g104 := {^Left g113, ^Right g112},
    g105 := {^\<lparr>\<rparr>},
    g106 := {^\<lparr>\<rparr>},
    g107 := {^\<lparr>\<rparr>},
    g108 := {^Fun g109 g110 (
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
    )},
    g109 := {^Fun g109 g110 (
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
    )},
    g110 := {^\<lparr>\<rparr>},
    g111 := {^Chan g111},
    g112 := {^\<lparr>\<rparr>},
    g113 := {^Right g112},
    g114 := {^Left g113},
    g115 := {^Left g114},
    g116 := {^\<lparr>\<rparr>},
    g117 :=  {^Fun g118 g119 (
      LET g120 = RECV EVT g111 in 
      LET g121 = SYNC g120 in 
      LET g122 = FST g121 in 
      LET g123 = SND g121 in 
      LET g124 = SEND EVT g123 g119 in 
      LET g125 = SYNC g124 in 
      LET g126 = APP g118 g122 in 
      RESULT g126 
    )},
    g118 :=  {^Fun g118 g119 (
      LET g120 = RECV EVT g111 in 
      LET g121 = SYNC g120 in 
      LET g122 = FST g121 in 
      LET g123 = SND g121 in 
      LET g124 = SEND EVT g123 g119 in 
      LET g125 = SYNC g124 in 
      LET g126 = APP g118 g122 in 
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
    g131 :=  {^Fun g132 g133 (
      LET g134 = FST g133 in 
      LET g135 = SND g133 in 
      LET g136 = CHAN \<lparr>\<rparr> in LET g137 = \<lparr>g135, g136\<rparr> in 
      LET g138 = SEND EVT g134 g137 in 
      LET g139 = SYNC g138 in 
      LET g140 = RECV EVT g136 in 
      LET g141 = SYNC g140 in 
      RESULT g141 
    )},
    g132 :=  {^Fun g132 g133 (
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
    g135 := {^Right g145, ^Left g151, ^Right g155, ^Left g160},
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
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g149 := {^\<lparr>\<rparr>},
    g150 := {^\<lparr>\<rparr>},
    g151 := {^Right g150},
    g152 := {^Left g151},
    g153 := {^Pair g143 g152},
    g154 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g155 := {^\<lparr>\<rparr>},
    g156 := {^Right g155},
    g157 := {^Pair g143 g156},
    g158 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g159 := {^\<lparr>\<rparr>},
    g160 := {^Right g159},
    g161 := {^Left g160},
    g162 := {^Pair g143 g161},
    g163 := {
      ^Right g128, ^Right g145, 
      ^Left g151, ^Right g155, ^Left g160
    },
    g164 := {^\<lparr>\<rparr>}
  )
"

definition F :: flow_set where "F = {

  (IdBind g103, ECall g103, IdBind g105),
  (IdBind g105, ECall g105, IdBind g103),
  (IdRslt g103, EReturn g105, IdRslt g105),
  (IdRslt g105, EReturn g103, IdRslt g103),
  (IdBind g107, ENext, IdRslt g107),
  (IdRslt g107, EReturn g103, IdRslt g103),
  (IdBind g103, ECall g103, IdBind g107),
  (IdBind g100, ENext, IdBind g108),
  (IdBind g111, ENext, IdBind g112),
  (IdBind g112, ENext, IdBind g113),
  (IdBind g113, ENext, IdBind g114),
  (IdBind g114, ENext, IdBind g115),
  (IdBind g115, ENext, IdBind g116),
  (IdBind g116, ECall g116, IdBind g103),
  (IdRslt g103, EReturn g116, IdBind g117),
  (IdBind g120, ENext, IdBind g121),
  (IdBind g121, ENext, IdBind g122),
  (IdBind g122, ENext, IdBind g123),
  (IdBind g123, ENext, IdBind g124),
  (IdBind g124, ENext, IdBind g125),
  (IdBind g125, ESend g124, IdBind g141),
  (IdBind g125, ENext, IdBind g126),
  (IdBind g126, ECall g126, IdBind g120),
  (IdRslt g126, EReturn g126, IdRslt g126),
  (IdBind g117, ENext, IdBind g127),
  (IdBind g127, ESpawn, IdBind g128),
  (IdBind g128, ENext, IdBind g129),
  (IdBind g129, ENext, IdBind g130),
  (IdBind g130, ECall g130, IdBind g120),
  (IdRslt g126, EReturn g130, IdRslt g130),
  (IdBind g127, ENext, IdRslt g111),
  (IdBind g108, ENext, IdBind g131),
  (IdBind g134, ENext, IdBind g135),
  (IdBind g135, ENext, IdBind g136),
  (IdBind g136, ENext, IdBind g137),
  (IdBind g137, ENext, IdBind g138),
  (IdBind g138, ENext, IdBind g139),
  (IdBind g139, ESend g138, IdBind g121),
  (IdBind g139, ENext, IdBind g140),
  (IdBind g140, ENext, IdBind g141),
  (IdBind g141, ENext, IdRslt g141),
  (IdBind g131, ENext, IdBind g142),
  (IdBind g142, ENext, IdBind g143),
  (IdBind g143, ECall g143, IdBind g111),
  (IdRslt g111, EReturn g143, IdBind g144),
  (IdBind g144, ESpawn, IdBind g145),
  (IdBind g145, ENext, IdBind g146),
  (IdBind g146, ENext, IdBind g147),
  (IdBind g147, ENext, IdBind g148),
  (IdBind g148, ECall g148, IdBind g134),
  (IdRslt g141, EReturn g148, IdRslt g148),
  (IdBind g144, ENext, IdBind g149),
  (IdBind g149, ESpawn, IdBind g150),
  (IdBind g150, ENext, IdBind g151),
  (IdBind g151, ENext, IdBind g152),
  (IdBind g152, ENext, IdBind g153),
  (IdBind g153, ENext, IdBind g154),
  (IdBind g154, ECall g154, IdBind g134),
  (IdRslt g141, EReturn g154, IdBind g155),
  (IdBind g155, ENext, IdBind g156),
  (IdBind g156, ENext, IdBind g157),
  (IdBind g157, ENext, IdBind g158),
  (IdBind g158, ECall g158, IdBind g134),
  (IdRslt g141, EReturn g158, IdRslt g158),
  (IdBind g149, ENext, IdBind g159),
  (IdBind g159, ENext, IdBind g160),
  (IdBind g160, ENext, IdBind g161),
  (IdBind g161, ENext, IdBind g162),
  (IdBind g162, ENext, IdBind g163),
  (IdBind g163, ECall g163, IdBind g134),
  (IdRslt g141, EReturn g163, IdBind g164),
  (IdBind g164, ENext, IdRslt g164)
}"

definition Ln_g111 :: node_map where "Ln_g111 = 
  (\<lambda> _ . {})(
    IdBind g108 := {},
    IdBind g111 := {},
    IdBind g112 := {g111},
    IdBind g113 := {g111},
    IdBind g114 := {g111},
    IdBind g115 := {g111},
    IdBind g116 := {g111},
    IdBind g117 := {g111},
    IdBind g120 := {g111, g118},
    IdBind g121 := {g120, g118},
    IdBind g122 := {g118},
    IdBind g123 := {g118},
    IdBind g124 := {g118},
    IdBind g125 := {g118},
    IdBind g126 := {g118},
    IdRslt g126 := {},
    IdBind g127 := {g111, g117},
    IdBind g128 := {g117},
    IdBind g129 := {g117},
    IdBind g130 := {g117},
    IdRslt g130 := {},
    IdRslt g111 := {g111},
    IdBind g131 := {},
    IdBind g134 := {g133},
    IdBind g135 := {g134},
    IdBind g136 := {g134},
    IdBind g137 := {g134},
    IdBind g138 := {g134},
    IdBind g139 := {g138},
    IdBind g140 := {},
    IdBind g141 := {},
    IdRslt g141 := {},
    IdBind g142 := {},
    IdBind g143 := {},
    IdBind g144 := {g143},
    IdBind g145 := {g143},
    IdBind g146 := {g143},
    IdBind g147 := {g143},
    IdBind g148 := {g147},
    IdRslt g148 := {},
    IdBind g149 := {g143},
    IdBind g150 := {g143},
    IdBind g151 := {g143},
    IdBind g152 := {g143},
    IdBind g153 := {g143},
    IdBind g154 := {g143, g153},
    IdBind g155 := {g143},
    IdBind g156 := {g143},
    IdBind g157 := {g143},
    IdBind g158 := {g157},
    IdRslt g158 := {},
    IdBind g159 := {g143},
    IdBind g160 := {g143},
    IdBind g161 := {g143},
    IdBind g162 := {g143},
    IdBind g163 := {g162},
    IdBind g164 := {},
    IdRslt g164 := {}
  )
"

definition Lx_g111 :: node_map where "Lx_g111 = 
  (\<lambda> _ . {})(
    IdBind g108 := {},
    IdBind g111 := {g111},
    IdBind g112 := {g111},
    IdBind g113 := {g111},
    IdBind g114 := {g111},
    IdBind g115 := {g111},
    IdBind g116 := {g111},
    IdBind g117 := {g111, g117},
    IdBind g120 := {g120, g118},
    IdBind g121 := {g118},
    IdBind g122 := {g118},
    IdBind g123 := {g118},
    IdBind g124 := {g118},
    IdBind g125 := {g118},
    IdBind g126 := {},
    IdRslt g126 := {},
    IdBind g127 := {g111, g117},
    IdBind g128 := {g117},
    IdBind g129 := {g117},
    IdBind g130 := {},
    IdRslt g130 := {},
    IdRslt g111 := {},
    IdBind g131 := {},
    IdBind g134 := {g134},
    IdBind g135 := {g134},
    IdBind g136 := {g134},
    IdBind g137 := {g134},
    IdBind g138 := {g138},
    IdBind g139 := {},
    IdBind g140 := {},
    IdBind g141 := {},
    IdRslt g141 := {},
    IdBind g142 := {},
    IdBind g143 := {g143},
    IdBind g144 := {g143},
    IdBind g145 := {g143},
    IdBind g146 := {g143},
    IdBind g147 := {g147},
    IdBind g148 := {},
    IdRslt g148 := {},
    IdBind g149 := {g143},
    IdBind g150 := {g143},
    IdBind g151 := {g143},
    IdBind g152 := {g143},
    IdBind g153 := {g143, g153},
    IdBind g154 := {g143},
    IdBind g155 := {g143},
    IdBind g156 := {g143},
    IdBind g157 := {g157},
    IdBind g158 := {},
    IdRslt g158 := {},
    IdBind g159 := {g143},
    IdBind g160 := {g143},
    IdBind g161 := {g143},
    IdBind g162 := {g162},
    IdBind g163 := {},
    IdBind g164 := {},
    IdRslt g164 := {}
  )
"

definition Ln_g136 :: node_map where "Ln_g136 = 
  (\<lambda> _ . {})(
    IdBind g121 := {},
    IdBind g122 := {g121},
    IdBind g123 := {g121},
    IdBind g124 := {g123},
    IdBind g125 := {g124},
    IdBind g126 := {},
    IdRslt g126 := {},
    IdBind g136 := {},
    IdBind g137 := {g136},
    IdBind g138 := {g136, g137},
    IdBind g139 := {g136, g138},
    IdBind g140 := {g136},
    IdBind g141 := {g140},
    IdRslt g141 := {}
  )
"

definition Lx_g136 :: node_map where "Lx_g136 = 
  (\<lambda> _ . {})(
    IdBind g121 := {g121},
    IdBind g122 := {g121},
    IdBind g123 := {g123},
    IdBind g124 := {g124},
    IdBind g125 := {},
    IdBind g126 := {},
    IdRslt g126 := {},
    IdBind g136 := {g136},
    IdBind g137 := {g136, g137},
    IdBind g138 := {g136, g137},
    IdBind g139 := {g136},
    IdBind g140 := {g140},
    IdBind g141 := {},
    IdRslt g141 := {}
  )
"




lemma path_with_tangent_call_is_live_for_g111: "
  may_be_static_live_path V F Ln_g111 Lx_g111 (IdBind g111) (\<lambda> x . True) [
    (IdBind g111, ENext),
    (IdBind g112, ENext),
    (IdBind g113, ENext),
    (IdBind g114, ENext),
    (IdBind g115, ENext),
    (IdBind g116, ECall g116),
    (IdBind g103, ECall g103),
    (IdBind g105, ECall g105),
    (IdBind g103, ECall g103),
    (IdBind g105, ECall g105),
    (IdBind g103, ECall g103),
    (IdBind g107, ENext),
    (IdRslt g107, EReturn g103),
    (IdRslt g103, EReturn g105),
    (IdRslt g105, EReturn g103),
    (IdRslt g103, EReturn g105),
    (IdRslt g105, EReturn g103),
    (IdRslt g103, EReturn g116),
    (IdBind g117, ENext),
    (IdBind g127, ESpawn),
    (IdBind g128, ENext)
  ]
"
 apply (rule may_be_static_live_path.Step)
 apply (rule may_be_static_live_path.Step)
 apply (rule may_be_static_live_path.Step)
 apply (rule may_be_static_live_path.Step)
 apply (rule may_be_static_live_path.Step)
 apply (rule may_be_static_live_path.Step)
 apply (rule may_be_static_live_path.Pre_Return[of 
   V F Ln_g111 Lx_g111 g103 _ g116 _
   "[(IdBind g103, ECall g103), (IdBind g105, ECall g105), 
     (IdBind g103, ECall g103), (IdBind g105, ECall g105), 
     (IdBind g103, ECall g103), (IdBind g107, ENext), 
     (IdRslt g107, EReturn g103), (IdRslt g103, EReturn g105), 
     (IdRslt g105, EReturn g103), (IdRslt g103, EReturn g105),
     (IdRslt g105, EReturn g103)]"
 ]; auto?)
 apply (rule may_be_static_live_path.Step)+
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
 apply (
   (erule static_balanced.cases; auto?),
   ((match premises in 
      I: "_ = (pre @ _)" for pre \<Rightarrow> 
          \<open>insert I; (cases pre)\<close>
    ); auto)+,
  (rotate_tac -1)?
 )+

 apply (unfold Lx_g111_def; auto)
 apply (simp add: Set.is_empty_def)
 apply (rule may_be_static_live_flow.Call_Live_Outer)
 apply (unfold F_def; auto)
 apply (unfold Lx_g111_def; auto)
 apply (simp add: Set.is_empty_def)
 apply (
  (rule may_be_static_live_flow.Next),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )+
done


lemma path_with_server_loop_is_live_for_g111: "
  may_be_static_live_path V F Ln_g111 Lx_g111 (IdBind g128) (\<lambda> x . True) [
    (IdBind g128, ENext),
    (IdBind g129, ENext),
    (IdBind g130, ECall g130),
    (IdBind g120, ENext),
    (IdBind g121, ENext),
    (IdBind g122, ENext),
    (IdBind g123, ENext),
    (IdBind g124, ENext),
    (IdBind g125, ENext),
    (IdBind g126, ECall g126),
    (IdBind g120, ENext),
    (IdBind g121, ENext),
    (IdBind g122, ENext),
    (IdBind g123, ENext),
    (IdBind g124, ENext),
    (IdBind g125, ENext),
    (IdBind g126, ECall g126)
  ]
"
 apply (rule may_be_static_live_path.Step)+
 apply (rule may_be_static_live_path.Edge; auto?)
 apply (rule may_be_static_live_flow.Call_Live_Inner; auto?)
 apply (unfold F_def; auto)
 apply (unfold Ln_g111_def; auto)
 apply (simp add: Set.is_empty_def)
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )+
 apply (rule may_be_static_live_flow.Call_Live_Inner; auto?)
 apply (unfold F_def; auto)
 apply (unfold Ln_g111_def; auto)
 apply (simp add: Set.is_empty_def)
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )+
 apply (rule may_be_static_live_flow.Call_Live_Inner; auto?)
 apply (unfold F_def; auto)
 apply (unfold Ln_g111_def; auto)
 apply (simp add: Set.is_empty_def)
 apply (
  (rule may_be_static_live_flow.Next; auto?),
  (unfold F_def; auto),
  (unfold Lx_g111_def; auto),
  (simp add: Set.is_empty_def),
  (unfold Ln_g111_def; auto),
  (simp add: Set.is_empty_def)
 )+
done


lemma path_with_chan_message_is_live_for_g136: "
  may_be_static_live_path V F Ln_g136 Lx_g136 (IdBind g136) (\<lambda> x . x = (IdBind g125)) [
    (IdBind g136, ENext),
    (IdBind g137, ENext),
    (IdBind g138, ENext),
    (IdBind g139, ESend g138),
    (IdBind g121, ENext),
    (IdBind g122, ENext),
    (IdBind g123, ENext),
    (IdBind g124, ENext)
  ]
"
 apply (rule may_be_static_live_path.Step)+
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
  \<not> may_be_static_live_path V F Ln_g136 Lx_g136 (IdBind g136) (\<lambda> x . x = (IdBind g125)) [
    (IdBind g121, ENext),
    (IdBind g122, ENext),
    (IdBind g123, ENext),
    (IdBind g124, ENext),
    (IdBind g125, ENext),
    (IdBind g126, ECall g126),
    (IdBind g120, ENext),
    (IdBind g121, ENext),
    (IdBind g122, ENext)
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
definition may_be_recv_site where "may_be_recv_site = 
 (may_be_static_recv_node_tm_id V anf_program)
"

lemma "
  static_flow_set V F may_be_recv_site anf_program
"
 apply (unfold 
    V_def F_def 
    may_be_recv_site_def may_be_static_send_node_tm_id.simps
    anf_program_def
 )
 apply (rule; auto?)+
 apply (simp add: may_be_static_recv_node_tm_id.simps; auto?)
 apply (erule is_super_tm.cases; auto?; simp?)+
 apply (rule; auto?)+
 apply (simp add: may_be_static_recv_node_tm_id.simps; auto?)
 apply (erule is_super_tm.cases; auto?; simp?)+
 apply (rule; auto?)+
done


lemma "
  (V, C) \<Turnstile>\<^sub>e anf_program
"
 apply (simp add: V_def C_def anf_program_def)
 apply (rule; auto?)+
done


lemma "
  static_chan_liveness V Ln_g111 Lx_g111 g111 anf_program
"
 apply (unfold V_def Ln_g111_def Lx_g111_def anf_program_def)
 apply (rule; auto?)+
 apply (erule may_be_built_on_abstract_chan.cases; auto)+
 apply (auto simp: Set.is_empty_def)



 apply (rule may_be_built_on_abstract_chan.Pair; auto)
 apply (rule may_be_built_on_abstract_chan.Chan; auto)
 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+

 apply (rule may_be_built_on_abstract_chan.Chan; auto)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+

 apply (rule; auto?)+

 apply (erule may_be_built_on_abstract_chan.cases; auto)+
 apply (auto simp: Set.is_empty_def)

 apply (rule may_be_built_on_abstract_chan.Pair; auto)
 apply (rule may_be_built_on_abstract_chan.Chan; auto)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+

 apply (rule may_be_built_on_abstract_chan.Chan; auto)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)


 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)


 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (auto simp: Set.is_empty_def)


 apply (rule may_be_built_on_abstract_chan.Pair; auto)
 apply (rule may_be_built_on_abstract_chan.Chan; auto)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+

 apply (rule; auto?)+

 apply (erule may_be_built_on_abstract_chan.cases; auto)+
 apply (auto simp: Set.is_empty_def)


 apply (rule may_be_built_on_abstract_chan.Pair; auto)
 apply (rule may_be_built_on_abstract_chan.Chan; auto)


 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+
 apply (rule may_be_built_on_abstract_chan.Chan; auto)
 apply (erule may_be_built_on_abstract_chan.cases; auto)+
 apply (auto simp: Set.is_empty_def)

 apply ((rotate_tac 1), (erule may_be_built_on_abstract_chan.cases; auto))+

 apply (rule; auto?)
 apply (rule; auto?)
 apply (rule; auto?)
 apply (rule; auto?)
 apply (rule; auto?)

 apply (fold V_def Ln_g111_def Lx_g111_def anf_program_def)

sorry





lemma "
  static_chan_liveness V Ln_g136 Lx_g136 g136 anf_program
"
sorry

*)



end
