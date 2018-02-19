theory Programs
  imports Main "~~/src/HOL/Library/Sublist" "~~/src/HOL/Eisbach/Eisbach_Tools"
    Syntax 
    Semantics Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Analysis Abstract_Communication_Analysis
    Communication_Analysis
begin


(* abstract representation of paths *)
datatype abstract_path =
  Empty |
  Atom control_label ("&_" [66]66) |
  Union abstract_path abstract_path (infix ":|:" 64) |
  Star abstract_path ("{_}*" [0]66) |
  Concat abstract_path abstract_path (infixr ":@:" 65)


inductive ap_matches :: "abstract_path \<Rightarrow> control_path \<Rightarrow> bool" (infix "|\<rhd>" 55) where
 Empty: "
   Empty |\<rhd> []
 " |
 Atom: "
   Atom l |\<rhd> [l]
 " |
 Union_Left: "
   \<lbrakk>
     p\<^sub>a |\<rhd> \<pi>
   \<rbrakk> \<Longrightarrow>
   Union p\<^sub>a p\<^sub>b |\<rhd> \<pi>
 " | 
 Union_Right: "
   \<lbrakk>
     p\<^sub>b |\<rhd> \<pi>
   \<rbrakk> \<Longrightarrow>
   Union p\<^sub>a p\<^sub>b |\<rhd> \<pi>
 " | 
 Star_Empty: "
   Star p |\<rhd> []
 " |
 Star: "
   \<lbrakk>
     Star p |\<rhd> \<pi>;
     p |\<rhd> \<pi>'
   \<rbrakk> \<Longrightarrow>
   Star p |\<rhd> \<pi> @ \<pi>'
 " |
 Concat: "
   \<lbrakk>
     p\<^sub>a |\<rhd> \<pi>\<^sub>a;
     p\<^sub>b |\<rhd> \<pi>\<^sub>b
   \<rbrakk> \<Longrightarrow>
   Concat p\<^sub>a p\<^sub>b |\<rhd> \<pi>\<^sub>a @ \<pi>\<^sub>b
 " 

inductive ap_linear :: "abstract_path \<Rightarrow> bool" where
 Empty: "
   ap_linear Empty
 " |
 Atom_Seq: "
   ap_linear (Atom (`x))
 " |
 Atom_Up: "
   ap_linear (Atom (\<upharpoonleft>x))
 " |
 Atom_Down: "
   ap_linear (Atom (\<downharpoonleft>x))
 " |
 Union: "
   \<lbrakk>
     ap_linear p\<^sub>a;
     ap_linear p\<^sub>b
   \<rbrakk> \<Longrightarrow> 
   ap_linear (Union p\<^sub>a p\<^sub>b)
 " |
 Star: "
   \<lbrakk>
     ap_linear p
   \<rbrakk> \<Longrightarrow> 
   ap_linear (Star p)
 " |
 Concat: "
   \<lbrakk>
     ap_linear p\<^sub>a;
     ap_linear p\<^sub>b
   \<rbrakk> \<Longrightarrow> 
   ap_linear (Concat p\<^sub>a p\<^sub>b)
 "

inductive ap_noncompetitive :: "abstract_path \<Rightarrow> bool" where
 Empty: "
   ap_noncompetitive Empty
 " |
 Atom: "
   ap_noncompetitive (Atom l)
 " |
 Union: "
   \<lbrakk>
     ap_linear p\<^sub>a;
     ap_linear p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_noncompetitive (Union p\<^sub>a p\<^sub>b)
 " |
 Star: "
   \<lbrakk>
     ap_linear p
   \<rbrakk> \<Longrightarrow>
   ap_noncompetitive (Star p)
 " |
 Concat: "
   \<lbrakk>
     ap_noncompetitive p\<^sub>a;
     ap_noncompetitive p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_noncompetitive (Concat p\<^sub>a p\<^sub>b)
 "


(** this may be too strong to prove: **)
(*
lemma "
  \<lbrakk>
    ap_noncompetitive ap
  \<rbrakk> \<Longrightarrow>
  noncompetitive {\<pi> . ap |\<rhd> \<pi>}
"
sorry
*)
lemma ap_linear_implies_linear : "
  ap_linear p \<Longrightarrow> p |\<rhd> \<pi> \<Longrightarrow> ``\<pi>``
"
sorry

lemma noncomp_star_linear_implies_same_proc:"
  \<lbrakk>
    ap_noncompetitive p;
    ap_linear p;
    Star p |\<rhd> \<pi>\<^sub>1; 
    Star p |\<rhd> \<pi>\<^sub>2
  \<rbrakk> \<Longrightarrow> 
  \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2
"
sorry

lemma noncomp_star_nonlinear_implies_ordered:"
  \<lbrakk>
    ap_noncompetitive p;
    \<not> (ap_linear p);
    Star p |\<rhd> \<pi>\<^sub>1; 
    Star p |\<rhd> \<pi>\<^sub>2
  \<rbrakk> \<Longrightarrow> 
  prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
"
sorry


lemma abstract_noncompetitve_implies: "
  \<lbrakk>
    ap |\<rhd> \<pi>\<^sub>1;
    ap |\<rhd> \<pi>\<^sub>2;
    ap_noncompetitive ap
  \<rbrakk> \<Longrightarrow>
  \<pi>\<^sub>1 \<cong> \<pi>\<^sub>2 \<or>
  prefix \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> prefix \<pi>\<^sub>2 \<pi>\<^sub>1
"
 apply auto
 apply (erule ap_noncompetitive.cases; auto)
  apply (erule ap_matches.cases; blast)
  apply (erule ap_matches.cases; erule ap_matches.cases; blast)
  using Lin ap_linear.Union ap_linear_implies_linear apply blast
  using Lin ap_linear.Star ap_linear_implies_linear apply blast
  apply (metis Star_Empty ap_matches.Star ap_noncompetitive.simps append_Nil noncomp_star_linear_implies_same_proc noncomp_star_nonlinear_implies_ordered)
done


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

(*
normalize (
  $LET ch = $CHAN \<lparr>\<rparr> in
  $LET u = $SPAWN (
    $APP ($FN f x .
      $LET u = $SYNC ($SEND EVT ($ch) ($x)) in  
      ($APP ($f) ($x))  
    ) $\<lparr>\<rparr>
  ) in
  $LET u = $SPAWN (
    $APP ($FN f x .
      $LET r = $SYNC ($RECV EVT ($ch)) in  
      ($APP ($f) ($x))  
    ) $\<lparr>\<rparr>
  ) in
  $\<lparr>\<rparr>
)"
*)

definition infinite_prog where
  "infinite_prog \<equiv> (
    LET g100 = CHAN \<lparr>\<rparr> in 
    LET g101 = SPAWN 
      LET g102 = FN g103 g104 . 
        LET g105 = SEND EVT g100 g104 in 
        LET g106 = SYNC g105 in 
        LET g107 = APP g103 g104 in 
        RESULT g107 
      in 
      LET g108 = \<lparr>\<rparr> in 
      LET g109 = APP g102 g108 in 
      RESULT g109 
    in 
    LET g110 = SPAWN 
      LET g111 = FN g112 g113 . 
        LET g114 = RECV EVT g100 in 
        LET g115 = SYNC g114 in 
        LET g116 = APP g112 g113 in 
        RESULT g116 
      in 
      LET g117 = \<lparr>\<rparr> in 
      LET g118 = APP g111 g117 in 
      RESULT g118 
    in 
    LET g119 = \<lparr>\<rparr> in 
    RESULT g119
  )"

definition infinite_prog_send_g100_abstract_path :: abstract_path where
  "infinite_prog_send_g100_abstract_path \<equiv> 
    &`g100 :@:
    &.g101 :@: &`g102 :@: &`g108 :@:
    &\<upharpoonleft>g109 :@: &`g105 :@: &`g106 :@: {&\<upharpoonleft>g107 :@: &`g105 :@: &`g106}*
  "

definition infinite_prog_recv_g100_abstract_path :: abstract_path where
  "infinite_prog_recv_g100_abstract_path \<equiv> 
    &`g100 :@: &`g101 :@:
    &.g110 :@: &`g111 :@: &`g117 :@: 
    &\<upharpoonleft>g118 :@: &`g114 :@: &`g115 :@: {&\<upharpoonleft>g116 :@: &`g114 :@: &`g115}*
  "

theorem infinite_prog_single_sender: "
   [[] \<mapsto> \<langle>infinite_one_to_one_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
   noncompetitive (send_paths \<E>' (Ch [] g100))
"
  apply (simp add: noncompetitive_def, (rule allI, rule impI)+)
 
(* strategy:
  step thru one iteration of loop.
  Each step before the recursion may have a distinct p_set.
  induct on star_left.  
  if 
    the ordered paths hold for (send_paths \<E> c) = p_set and
    p_set = p_set'
  then 
    the ordered paths should hold for (send_paths \<E>' c) = p_set'
*)
sorry


theorem infinite_prog_single_receiver: "
  [[] \<mapsto> \<langle>infinite_one_to_one_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<longrightarrow>
   noncompetitive (recv_paths \<E>' (Ch [] g100))
"
sorry

theorem "
  start_state infinite_prog \<rightarrow>* \<E>' 
  \<Longrightarrow>
  one_to_one \<E>' (Ch [] g100)
"
  apply (simp add: one_to_one_def, auto)
  using infinite_prog_single_sender apply blast
  using infinite_prog_single_receiver apply blast
done


definition infinite_prog_\<V> :: "abstract_value_env" where 
  "infinite_prog_\<V> \<equiv> (\<lambda> _ . {})(
    g100 := {^Chan g100}, 

    g101 := {^\<lparr>\<rparr>},
    g102 := {^(Abs g103 g104 (
      LET g105 = SEND EVT g100 g104 in 
      LET g106 = SYNC g105 in 
      LET g107 = APP g103 g104 in 
      RESULT g107 
    ))},
    g103 := {^(Abs g103 g104 (
      LET g105 = SEND EVT g100 g104 in 
      LET g106 = SYNC g105 in 
      LET g107 = APP g103 g104 in 
      RESULT g107
    ))}, g104 := {^\<lparr>\<rparr>},
    g105 := {^(Send_Evt g100 g104)},
    g106 := {^\<lparr>\<rparr>}, g107 := {},
    g108 := {^\<lparr>\<rparr>}, g109 := {},

    g110 := {^\<lparr>\<rparr>},
    g111 := {^(Abs g112 g113 (
              LET g114 = RECV EVT g100 in 
              LET g115 = SYNC g114 in 
              LET g116 = APP g112 g113 in 
              RESULT g116 
    ))},
    g112 := {^(Abs g112 g113 (
              LET g114 = RECV EVT g100 in 
              LET g115 = SYNC g114 in 
              LET g116 = APP g112 g113 in 
              RESULT g116 
    ))}, g113 := {^\<lparr>\<rparr>},
    g114 := {^(Recv_Evt g100)},
    g115 := {^\<lparr>\<rparr>}, g116 := {},
    g117 := {^\<lparr>\<rparr>}, g118 := {},

    g119 := {^\<lparr>\<rparr>}
  )"

definition infinite_prog_\<C> :: "abstract_value_env" where 
  "infinite_prog_\<C>  \<equiv> (\<lambda> _ . {})(
    g100 := {^\<lparr>\<rparr>}
  )"


theorem infinite_prog_has_intuitive_avf_analysis: "
  (infinite_prog_\<V>, infinite_prog_\<C>) \<Turnstile>\<^sub>e infinite_prog 
"
 apply (simp add: infinite_prog_\<V>_def infinite_prog_\<C>_def infinite_prog_def)
 apply (rule; simp?)+
done

method set_elem_condition_split = (
  match premises in 
    I: "_ \<in> (if P then _ else _)" for P \<Rightarrow> \<open>cases P\<close>
, clarsimp)

method subset_condition_split = (
  match premises in 
    I: "(if P then _ else _) \<subseteq> _" for P \<Rightarrow> \<open>cases P\<close>
, clarsimp)

lemma step_down_length_one_implies_false: "
  Suc 0 = length (\<pi> @ \<upharpoonleft>x # (\<pi>' ;; \<downharpoonleft>x)) \<Longrightarrow> False
"
by simp

lemma snoc_length_one_implies_empty_prefix: "
  Suc 0 = length (\<pi> ;; l) \<Longrightarrow> \<pi> = []
"
by simp

lemma step_down_length_two_implies_empty_lists: "
  length (\<pi> @ \<upharpoonleft>x # (\<pi>' ;; \<downharpoonleft>x)) = 2 \<Longrightarrow> \<pi> = [] \<and> \<pi>' = []
"
by simp

(*
lemma abc_base_cases: "
  n = length (\<pi>\<^sub>y ;; `x\<^sub>y) \<Longrightarrow>
  infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<Longrightarrow>
  ^Chan g100 \<in> infinite_prog_\<V> x\<^sub>s\<^sub>c \<Longrightarrow>
  ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> infinite_prog_\<V> x\<^sub>e \<Longrightarrow>
  ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y \<Longrightarrow>
  infinite_prog_\<V> x\<^sub>m \<subseteq> ((\<lambda>_. {})(g100 := {^\<lparr>\<rparr>})) g100 \<Longrightarrow>
  \<not> 7 < n \<Longrightarrow> 
  &`g100 :@: &.g101 :@: &`g102 :@: &`g108 :@: &\<upharpoonleft>g109 :@: &`g105 :@: &`g106 :@: {&\<upharpoonleft>g107 :@: &`g105 :@: &`g106}* |\<rhd> \<pi>\<^sub>y ;; `x\<^sub>y
"
 apply (unfold infinite_prog_def)
 apply (case_tac "n = 0")
  apply (simp)
 apply (case_tac "n = 1")
  apply (simp, erule traceable.cases; blast)
 apply (case_tac "n = 2")
  apply (simp, erule traceable.cases; clarsimp; (erule traceable.cases; blast))
 apply (case_tac "n = 3")
  apply (simp, erule traceable.cases; clarsimp; (erule traceable.cases; clarsimp; (erule traceable.cases; blast)))
 apply (case_tac "n = 4")
  apply (simp, erule traceable.cases; auto)
   apply (case_tac "\<pi>"; case_tac "\<pi>'"; auto?)
    apply (erule traceable.cases; auto; erule traceable.cases; auto)
sorry
*)

value "(abstract_path.Concat (abstract_path.Concat x y) z)"

lemma cons_eq_append: "
  x # xs = [x] @ xs
"
by simp

lemma concat_assoc[simp]: "
  (x :@: y) :@: z |\<rhd> \<pi> \<longleftrightarrow> x :@: (y :@: z) |\<rhd> \<pi>
"
  apply auto
   apply (erule ap_matches.cases; auto; erule ap_matches.cases; auto)
   apply (drule ap_matches.Concat[of y _ z], simp)
   apply (erule ap_matches.Concat, simp)
  apply (erule ap_matches.cases; auto; erule ap_matches.cases[of "y :@: z"]; auto)
  apply (drule ap_matches.Concat, simp)
  apply (drule ap_matches.Concat[of "x :@: y" _ "z"], auto)
done


lemma concat_star_implies_star: "
 {p}* :@: p |\<rhd> \<pi> \<Longrightarrow> {p}* |\<rhd> \<pi>
"
 apply (erule ap_matches.cases; auto)
 apply (erule ap_matches.Star; simp)
done

lemma abc_vacuous: "
  infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<Longrightarrow>
  ^Chan g100 \<in> infinite_prog_\<V> x\<^sub>s\<^sub>c \<Longrightarrow>
  ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> infinite_prog_\<V> x\<^sub>e \<Longrightarrow>
  ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y \<Longrightarrow>
  infinite_prog_\<V> x\<^sub>m \<subseteq> ((\<lambda>_. {})(g100 := {^\<lparr>\<rparr>})) g100 \<Longrightarrow>
  \<pi>\<^sub>y ;; `x\<^sub>y \<noteq> [`g100, .g101, `g102, `g108, \<upharpoonleft>g109, `g105, `g106] \<Longrightarrow>
  \<not> (\<pi>\<^sub>y ;; `x\<^sub>y = (\<pi> ;; `g106) @ [\<upharpoonleft>g107, `g105, `g106] \<and> infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>, LET g106 = SYNC x\<^sub>e in e\<^sub>n)) \<Longrightarrow>
  False
"
  apply (unfold infinite_prog_def, auto)
sorry


lemma abc': "
  (\<forall> \<pi>\<^sub>y x\<^sub>y x\<^sub>e e\<^sub>n x\<^sub>s\<^sub>c x\<^sub>m.
    (n :: nat) = length (\<pi>\<^sub>y ;; `x\<^sub>y) \<longrightarrow>
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n) \<longrightarrow>
    ^Chan g100 \<in> infinite_prog_\<V> x\<^sub>s\<^sub>c \<longrightarrow>
    ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> infinite_prog_\<V> x\<^sub>e \<longrightarrow>
    ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y \<longrightarrow>
    infinite_prog_\<V> x\<^sub>m \<subseteq> infinite_prog_\<C> g100 \<longrightarrow>
    infinite_prog_send_g100_abstract_path |\<rhd> (\<pi>\<^sub>y ;; `x\<^sub>y)
  )
"
 apply (unfold infinite_prog_\<C>_def infinite_prog_send_g100_abstract_path_def)
 apply (rule nat_less_induct[of _ n], (rule allI)+, (rule impI)+)
  (* base case *)
 apply (case_tac "\<pi>\<^sub>y ;; `x\<^sub>y = [`g100, .g101, `g102, `g108, \<upharpoonleft>g109, `g105, `g106]", clarsimp)
  apply (match conclusion in 
    "(&x) :@: _  |\<rhd> x # _" for x \<Rightarrow> \<open>(subst cons_eq_append[of x], rule ap_matches.Concat, rule ap_matches.Atom)\<close>
  )+
  apply (rule ap_matches.Star_Empty)
 (* Inductive case *)
 apply (case_tac "
    \<pi>\<^sub>y ;; `x\<^sub>y = (\<pi> ;; `g106) @ [\<upharpoonleft>g107, `g105, `g106] \<and> 
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>, LET g106 = SYNC x\<^sub>e in e\<^sub>n)
 ", clarsimp)
  apply (drule spec[of _ "(length (\<pi> ;; `g106))"], clarsimp)
  apply (drule spec[of _ "\<pi>"], clarsimp)
  apply (drule spec[of _ "g106"])
  apply (drule_tac x = "x\<^sub>e" in spec, erule impE, rule_tac x = "e\<^sub>n" in exI, assumption)
  apply (drule_tac x = "x\<^sub>s\<^sub>c" in spec, erule impE, assumption)
  apply (drule_tac x = "x\<^sub>m" in spec, (erule impE, assumption)+)
  apply (subgoal_tac "&\<upharpoonleft>g107 :@: &`g105 :@: &`g106 |\<rhd> [\<upharpoonleft>g107, `g105, `g106]")
  apply (drule ap_matches.Concat; simp)
  apply (thin_tac "&\<upharpoonleft>g107 :@: &`g105 :@: &`g106 |\<rhd> [\<upharpoonleft>g107, `g105, `g106]")
  apply (match premises in 
    I: "(&x) :@: _  |\<rhd> _" for x \<Rightarrow> \<open>(subgoal_tac "&x |\<rhd> [x]"); (rule ap_matches.Atom)?\<close>
  , (erule ap_matches.cases; auto), erule ap_matches.Concat)+
  apply (erule concat_star_implies_star)
  apply (match conclusion in 
    "(&x) :@: _  |\<rhd> x # _" for x \<Rightarrow> \<open>(subst cons_eq_append[of x], rule ap_matches.Concat, rule ap_matches.Atom)\<close>
  )+
  apply (rule ap_matches.Atom)
 (* vacuous cases *)
 apply (drule abc_vacuous; auto)
done

lemma abc: "
  \<pi> \<in> abstract_send_paths (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100 \<Longrightarrow> 
  infinite_prog_send_g100_abstract_path |\<rhd> \<pi>
"
 apply (simp add: abstract_send_paths_def; clarsimp)
 apply (insert abc', blast)
done

lemma xyz: "
  ap_noncompetitive infinite_prog_send_g100_abstract_path
"
 apply (simp add: infinite_prog_send_g100_abstract_path_def)
 apply (rule; simp?)+
done

theorem infinite_prog_has_single_sender_communication_analysis: "
  noncompetitive (abstract_send_paths (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100)
"
   apply (simp add: noncompetitive_def, (rule allI, rule impI)+)
   apply (rule abstract_noncompetitve_implies[of infinite_prog_send_g100_abstract_path])
   apply (simp add: abc)
   apply (simp add: abc)
   apply (simp add: xyz)
done


theorem infinite_prog_has_single_receiver_communication_analysis: "
  noncompetitive (abstract_recv_paths (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100)
"
 apply (simp add: noncompetitive_def)
 apply (simp add: abstract_recv_paths_def, auto)
sorry

theorem infinite_prog_has_one_to_one_communication_analysis: "
  abstract_one_to_one (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100
"
 apply (simp add: abstract_one_to_one_def, auto)
 apply (simp add: infinite_prog_has_single_sender_communication_analysis)
 apply (simp add: infinite_prog_has_single_receiver_communication_analysis)
done


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
