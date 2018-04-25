theory Static_Communication_Analysis
  imports Main Syntax 
    Dynamic_Semantics Static_Semantics
    Dynamic_Communication_Analysis
    Static_Framework
begin


inductive built_on_chan :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool"  where
  Chan: "
    \<lbrakk>
      ^Chan x\<^sub>c \<in> V x 
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Send_Evt: "
    \<lbrakk>
      ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>s\<^sub>c \<or> built_on_chan V x\<^sub>c x\<^sub>m 
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Recv_Evt: "
    \<lbrakk>
      ^Recv_Evt x\<^sub>r\<^sub>c \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>r\<^sub>c
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Pair: "
    \<lbrakk>
      ^(Pair x\<^sub>1 x\<^sub>2) \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>1 \<or> built_on_chan V x\<^sub>c x\<^sub>2
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Left: "
    \<lbrakk>
      ^(Left x\<^sub>a) \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  " |
  Right: "
    \<lbrakk>
      ^(Right x\<^sub>a) \<in> V x;
      built_on_chan V x\<^sub>c x\<^sub>a
    \<rbrakk> \<Longrightarrow> 
    built_on_chan V x\<^sub>c x
  "


fun chanSet :: "abstract_value_env \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var set" where
  "chanSet V x\<^sub>c x = (if built_on_chan V x\<^sub>c x then {x} else {})"


type_synonym label_map = "node_label \<Rightarrow> var set"
inductive static_chan_liveness :: "abstract_value_env \<Rightarrow> label_map \<Rightarrow> label_map \<Rightarrow> var \<Rightarrow> exp \<Rightarrow> bool" where
  Result: "
    \<lbrakk>
      chanSet V x\<^sub>c y \<subseteq> Ln (NResult y)
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (RESULT y)
  " |
  Let_Unit: "
    \<lbrakk>
      Ln (nodeLabel e) \<subseteq> Lx (NLet x);
      Lx (NLet x) \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = \<lparr>\<rparr> in e)
  " |
  Let_Chan: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = CHAN \<lparr>\<rparr> in e)
  " |
  Let_Send_Evt: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (
        (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> 
        chanSet V x\<^sub>c x\<^sub>s\<^sub>c \<union> chanSet V x\<^sub>c x\<^sub>m 
      ) \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SEND EVT x\<^sub>s\<^sub>c x\<^sub>m in e)
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>r\<^sub>c \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = RECV EVT x\<^sub>r\<^sub>c in e)
  " |
  Let_Pair: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (
        (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> 
        chanSet V x\<^sub>c x\<^sub>1 \<union> chanSet V x\<^sub>c x\<^sub>2
      ) \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e)
  " |
  Let_Left: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = LEFT x\<^sub>a in e)
  " |
  Let_Right: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = RIGHT x\<^sub>a in e)
  " |
  Let_Abs: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>b;
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FN f x\<^sub>p . e\<^sub>b  in e)
  " |
  Let_Spawn: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>c;
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SPAWN e\<^sub>c in e)
  " |
  Let_Sync: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      \<forall> xSC xM . {^Send_Evt xSC xM} \<subseteq> V x\<^sub>e \<longrightarrow> (chanSet V x\<^sub>c xM) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>e \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SYNC x\<^sub>e in e)
  " |
  Let_Fst: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = FST x\<^sub>a in e)
  " |
  Let_Snd: "
    \<lbrakk>
      Ln (nodeLabel e) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = SND x\<^sub>a in e)
  " |
  Let_Case: "
    \<lbrakk>
      Ln (nodeLabel e\<^sub>l) \<union> Ln (nodeLabel e\<^sub>r) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x);
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>s \<subseteq> Ln (NLet x);

      Ln (nodeLabel e) \<subseteq> Lx (NResult (\<lfloor>e\<^sub>l\<rfloor>));
      Lx (NResult (\<lfloor>e\<^sub>l\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> Ln (NResult (\<lfloor>e\<^sub>l\<rfloor>));

      Ln (nodeLabel e) \<subseteq> Lx (NResult (\<lfloor>e\<^sub>r\<rfloor>));
      Lx (NResult (\<lfloor>e\<^sub>r\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> Ln (NResult (\<lfloor>e\<^sub>r\<rfloor>));

      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>l;
      static_chan_liveness V Ln Lx x\<^sub>c e\<^sub>r;
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e)
  " |
  Let_App: "
    \<lbrakk>
      (\<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> V f \<longrightarrow> 
        Ln (nodeLabel e) \<subseteq> Lx (NResult (\<lfloor>e\<^sub>b\<rfloor>)) \<and>
        Lx (NResult (\<lfloor>e\<^sub>b\<rfloor>)) \<union> chanSet V x\<^sub>c (\<lfloor>e\<^sub>b\<rfloor>) \<subseteq> Ln (NResult (\<lfloor>e\<^sub>b\<rfloor>)) \<and>
        Ln (nodeLabel e\<^sub>b) \<union> (chanSet V x\<^sub>c x) \<subseteq> Lx (NLet x)
      );
      (Lx (NLet x) - chanSet V x\<^sub>c x) \<union> chanSet V x\<^sub>c x\<^sub>a \<subseteq> Ln (NLet x);
      static_chan_liveness V Ln Lx x\<^sub>c e
    \<rbrakk> \<Longrightarrow>
    static_chan_liveness V Ln Lx x\<^sub>c (LET x = APP f x\<^sub>a in e)
  "


inductive is_static_live_flow :: "label_map \<Rightarrow> label_map \<Rightarrow> flow_set \<Rightarrow> flow_label \<Rightarrow> bool"  where
  Next: "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    is_static_live_flow Ln Lx F (l, ENext, l')
  " |
  Spawn: "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    is_static_live_flow Ln Lx F (l, ENext, l')
  " |
  Call: "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    is_static_live_flow Ln Lx F (l, ENext, l')
  " |
  Return: "
    (l, ENext, l') \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx l) \<Longrightarrow>
    \<not> Set.is_empty (Ln l') \<Longrightarrow>
    is_static_live_flow Ln Lx F (l, ENext, l')
  " |
  Send: "
    ((NLet xSend), ESend, (NLet xRecv)) \<in> F \<Longrightarrow>
    \<not> Set.is_empty (Lx (NLet xSend)) \<Longrightarrow>
    {xRecv} \<subseteq> (Ln (NLet xRecv)) \<Longrightarrow>
    is_static_live_flow Ln Lx F ((NLet xSend), ESend, (NLet xRecv))
  "


inductive static_live_flow_set :: "label_map \<Rightarrow> label_map \<Rightarrow> flow_set \<Rightarrow> flow_set \<Rightarrow> bool"  where
  "
    (\<forall> l cl l' .
      is_static_live_flow Ln Lx F (l, cl, l') \<longrightarrow>
      (l, cl, l') \<in> LF 
    ) \<Longrightarrow>
    static_live_flow_set Ln Lx F LF
  "


inductive is_static_send_node_label :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  Sync: "
    {^Chan xC} \<subseteq> V xSC \<Longrightarrow>
    {^Send_Evt xSC xM} \<subseteq> V xE \<Longrightarrow>
    is_subexp e (LET x = SYNC xE in e') \<Longrightarrow>
    is_static_send_node_label V e xC (NLet x)
  "

inductive is_static_recv_node_label :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> node_label \<Rightarrow> bool" where
  Sync: "
    {^Chan xC} \<subseteq> V xRC \<Longrightarrow>
    {^Recv_Evt xRC} \<subseteq> V xE \<Longrightarrow>
    is_subexp e (LET x = SYNC xE in e') \<Longrightarrow>
    is_static_recv_node_label V e xC (NLet x)
  "


inductive is_static_path :: "flow_set \<Rightarrow> node_label \<Rightarrow> (node_label \<Rightarrow> bool) \<Rightarrow> static_path \<Rightarrow> bool" where
  Empty: "
    isEnd start \<Longrightarrow>
    is_static_path F start isEnd []
  " |
  Edge: "
    isEnd end \<Longrightarrow>
    (start, edge, end) \<in> F \<Longrightarrow>
    is_static_path F start isEnd [(start, el)]
  " |
  Step: "
    is_static_path F middle isEnd ((middle, edge') # path) \<Longrightarrow>
    (start, edge, middle) \<in> F \<Longrightarrow>
    is_static_path F start isEnd ((start, edge) # (middle, edge') # path)
  "


inductive inclusive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" (infix "\<asymp>" 55) where
  Ordered: "
    prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow>
    \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2
  " |
  Spawn_Left: "
    \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Spawn_Right: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESpawn) # \<pi>\<^sub>2
  " |
  Send_Left: "
    \<pi> @ (NLet x, ESend) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ENext) # \<pi>\<^sub>2
  " |
  Send_Right: "
    \<pi> @ (NLet x, ENext) # \<pi>\<^sub>1 \<asymp> \<pi> @ (NLet x, ESend) # \<pi>\<^sub>2
  "

lemma inclusive_commut: "
  \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>2 \<asymp> \<pi>\<^sub>1
"
 apply (erule inclusive.cases; auto)
  apply (simp add: Ordered)
  apply (simp add: Ordered)
  apply (simp add: Spawn_Right)
  apply (simp add: Spawn_Left)
  apply (simp add: Send_Right)
  apply (simp add: Send_Left)
done


lemma inclusive_preserved_under_unordered_extension: "
  \<not> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<Longrightarrow> \<not> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<Longrightarrow> \<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 @ [l] \<asymp> \<pi>\<^sub>2
"
 apply (erule inclusive.cases; auto)
  apply (simp add: Spawn_Left)
  apply (simp add: Spawn_Right)
  apply (simp add: Send_Left)
  apply (simp add: Send_Right)
done

definition singular :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
 "singular \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"

definition noncompetitive :: "static_path \<Rightarrow> static_path \<Rightarrow> bool" where
 "noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2 \<equiv> prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1 \<or> \<not> (\<pi>\<^sub>1 \<asymp> \<pi>\<^sub>2)"


definition every_two_static_paths  :: "(static_path \<Rightarrow> bool) \<Rightarrow> (static_path \<Rightarrow> static_path \<Rightarrow> bool) \<Rightarrow> bool" where
  "every_two_static_paths P R \<equiv> (\<forall> path1 path2 .
    P path1 \<longrightarrow>
    P path2 \<longrightarrow>
    R path1 path2
  )"


inductive static_one_shot :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (is_static_path LF (NLet xC) (is_static_send_node_label V e xC)) singular \<Longrightarrow>
    static_live_flow_set Ln Lx F LF \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F e \<Longrightarrow>
    static_one_shot V e xC 
  "

inductive static_one_to_one :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (is_static_path LF (NLet xC) (is_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    every_two_static_paths (is_static_path LF (NLet xC) (is_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_flow_set Ln Lx F LF \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F e \<Longrightarrow>
    static_one_to_one V e xC 
  "

inductive static_fan_out :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (is_static_path LF (NLet xC) (is_static_send_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_flow_set Ln Lx F LF \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F e \<Longrightarrow>
    static_fan_out V e xC 
  "

inductive static_fan_in :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> var \<Rightarrow> bool" where
  Sync: "
    every_two_static_paths (is_static_path LF (NLet xC) (is_static_recv_node_label V e xC)) noncompetitive \<Longrightarrow>
    static_live_flow_set Ln Lx F LF \<Longrightarrow>
    static_chan_liveness V Ln Lx xC e \<Longrightarrow>
    static_flow_set V F e \<Longrightarrow>
    static_fan_in V e xC 
  "

end
