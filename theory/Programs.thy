theory Programs
  imports Main "~~/src/HOL/Library/Sublist" "~~/src/HOL/Eisbach/Eisbach_Tools"
    Syntax 
    Runtime_Semantics Static_Semantics Static_Semantics_Soundness
    Runtime_Communication_Analysis Static_Communication_Analysis
    Static_Communication_Analysis_Soundness
begin


lemma traceable_result_implies_traceable_case_left: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>\<bar>x # \<pi>', RESULT y); \<downharpoonright>\<pi>'\<upharpoonleft>;
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n)
  \<rbrakk> \<Longrightarrow>
  b = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r \<and> y = \<lfloor>e\<^sub>l\<rfloor>
"
sorry

lemma traceable_result_implies_traceable_case_right: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>:x # \<pi>', RESULT y); \<downharpoonright>\<pi>'\<upharpoonleft>;
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n)
  \<rbrakk> \<Longrightarrow>
  b = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r \<and> y = \<lfloor>e\<^sub>r\<rfloor>
"
sorry

lemma traceable_result_implies_traceable_app: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi> @ \<upharpoonleft>x # \<pi>', RESULT y); \<downharpoonright>\<pi>'\<upharpoonleft>;
    \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, LET x = b in e\<^sub>n)
  \<rbrakk> \<Longrightarrow>
  b = APP f x\<^sub>a \<and> y \<in> {\<lfloor>e\<^sub>b\<rfloor> |  f' x\<^sub>p . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f} (*not sure which function is bound to f; do I need unique names for f in labels?*)
"
sorry

(*
lemma traceable_functional: "
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e\<^sub>1) \<Longrightarrow>
  \<V> \<turnstile> e\<^sub>0 \<down> (\<pi>, e\<^sub>2) \<Longrightarrow>
  e\<^sub>1 = e\<^sub>2
"
(* 
  this could be true if CASE steps created distinct control_labels for left and right 
  and functions had unique names and control labels with the names
*)
sorry
*)


(*
inductive ap_linear :: "abstract_path \<Rightarrow> bool" where
 Empty: "
   ap_linear Empty
 " |
 Atom_Seq: "
   ap_linear (&(`x))
 " |
 Atom_Up: "
   ap_linear (&(\<upharpoonleft>x))
 " |
 Atom_Down: "
   ap_linear (&(\<downharpoonleft>x))
 " |
 Union: "
   \<lbrakk>
     ap_linear p\<^sub>a;
     ap_linear p\<^sub>b
   \<rbrakk> \<Longrightarrow> 
   ap_linear (p\<^sub>a :|: p\<^sub>b)
 " |
 Star: "
   \<lbrakk>
     ap_linear p
   \<rbrakk> \<Longrightarrow> 
   ap_linear ({p}* )
 " |
 Concat: "
   \<lbrakk>
     ap_linear p\<^sub>a;
     ap_linear p\<^sub>b
   \<rbrakk> \<Longrightarrow> 
   ap_linear (p\<^sub>a :@: p\<^sub>b)
 "
*)



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
   &l |\<rhd> [l]
 " |
 Union_Left: "
   \<lbrakk>
     p\<^sub>a |\<rhd> \<pi>
   \<rbrakk> \<Longrightarrow>
   p\<^sub>a :|: p\<^sub>b |\<rhd> \<pi>
 " | 
 Union_Right: "
   \<lbrakk>
     p\<^sub>b |\<rhd> \<pi>
   \<rbrakk> \<Longrightarrow>
   p\<^sub>a :|: p\<^sub>b |\<rhd> \<pi>
 " | 
 Star_Empty: "
   {p}* |\<rhd> []
 " |
 Star: "
   \<lbrakk>
     p |\<rhd> \<pi>;
     {p}* |\<rhd> \<pi>'
   \<rbrakk> \<Longrightarrow>
   {p}* |\<rhd> \<pi> @ \<pi>'
 " |
 Concat: "
   \<lbrakk>
     p\<^sub>a |\<rhd> \<pi>\<^sub>a;
     p\<^sub>b |\<rhd> \<pi>\<^sub>b
   \<rbrakk> \<Longrightarrow>
   p\<^sub>a :@: p\<^sub>b |\<rhd> \<pi>\<^sub>a @ \<pi>\<^sub>b
 " 

inductive ap_single :: "abstract_path \<Rightarrow> bool" where
 Empty: "
   ap_single Empty
 " |
 Atom: "
   ap_single (&l)
 " |
 Concat: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_single p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_single (p\<^sub>a :@: p\<^sub>b)
 "

inductive ap_ordered :: "abstract_path \<Rightarrow> bool" where
 Single: "
   ap_single ap \<Longrightarrow> ap_ordered ap
 " |
 Star: "
   \<lbrakk>
     ap_single p
   \<rbrakk> \<Longrightarrow>
   ap_ordered ({p}*)
 " |
 Concat: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_ordered p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_ordered (p\<^sub>a :@: p\<^sub>b)
 " |
 Union_Right: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_ordered p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_ordered (p\<^sub>a :@: (Empty :|: p\<^sub>b))
 " |
 Union_Left: "
   \<lbrakk>
     ap_single p\<^sub>a;
     ap_ordered p\<^sub>b
   \<rbrakk> \<Longrightarrow>
   ap_ordered (p\<^sub>a :@: (p\<^sub>b :|: Empty))
 "


definition ap_noncompetitive :: "abstract_path \<Rightarrow> bool" where 
  "ap_noncompetitive ap = ap_ordered ap"

lemma atom_matches_implies: "
 &l |\<rhd> \<pi> \<Longrightarrow> [l] = \<pi>
"
 apply (erule ap_matches.cases; auto)
done

lemma union_matches_implies: "
  p\<^sub>a :|: p\<^sub>b |\<rhd> \<pi> \<Longrightarrow> p\<^sub>a |\<rhd> \<pi> \<or> p\<^sub>b |\<rhd> \<pi>
"
 apply (erule ap_matches.cases; auto)
done

lemma concat_matches_implies: "
  p\<^sub>a :@: p\<^sub>b |\<rhd> \<pi> \<Longrightarrow> \<exists> \<pi>\<^sub>a \<pi>\<^sub>b . \<pi> = \<pi>\<^sub>a @ \<pi>\<^sub>b \<and> p\<^sub>a |\<rhd> \<pi>\<^sub>a \<and> p\<^sub>b |\<rhd> \<pi>\<^sub>b
"
 apply (erule ap_matches.cases; auto)
done


lemma ap_noncompetitive_implies_noncompetitive': "
  ap |\<rhd> \<pi>\<^sub>1 \<Longrightarrow>
  (\<forall> \<pi>\<^sub>2 .
    ap |\<rhd> \<pi>\<^sub>2 \<longrightarrow>
    ap_noncompetitive ap \<longrightarrow>
    noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
 )
"
 apply (simp add: ap_noncompetitive_def noncompetitive_def)
 apply (erule ap_matches.induct; auto)
  apply (simp add: atom_matches_implies)
  using ap_ordered.simps ap_single.simps apply blast
  using ap_ordered.simps ap_single.simps apply blast

  apply (frule ap_ordered.cases; auto)
  using ap_single.simps apply blast
  apply (drule ap_ordered.Single)
  apply (rotate_tac 4)
  apply (erule ap_matches.cases; auto)
  apply (drule_tac x = \<pi>'' in spec)
  apply (drule_tac x = \<pi>''' in spec)
  apply auto

sorry



lemma ap_noncompetitive_implies_noncompetitive: "
  \<lbrakk>
    ap |\<rhd> \<pi>\<^sub>1;
    ap |\<rhd> \<pi>\<^sub>2;
    ap_noncompetitive ap
  \<rbrakk> \<Longrightarrow>
  noncompetitive \<pi>\<^sub>1 \<pi>\<^sub>2
"
by (simp add: ap_noncompetitive_implies_noncompetitive')


lemma cons_eq_append: "
  [x] @ xs = x # xs
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

lemma concat_star_implies_star': "
  ps |\<rhd> \<pi>\<^sub>a \<Longrightarrow> \<forall> p . ps = {p}* \<longrightarrow> p |\<rhd> \<pi>\<^sub>b \<longrightarrow> {p}* |\<rhd> \<pi>\<^sub>a @ \<pi>\<^sub>b
"
 apply (erule ap_matches.induct; auto)
  using Star_Empty ap_matches.Star apply fastforce
  apply (thin_tac "\<forall>pa. p = {pa}* \<longrightarrow> pa |\<rhd> \<pi>\<^sub>b \<longrightarrow> {pa}* |\<rhd> \<pi> @ \<pi>\<^sub>b")
  apply (drule ap_matches.Star; auto)
done

lemma concat_star_implies_star: "
 {p}* :@: p |\<rhd> \<pi> \<Longrightarrow> {p}* |\<rhd> \<pi>
"
 apply (erule ap_matches.cases; auto)
by (simp add: concat_star_implies_star')


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
   [[] \<mapsto> \<langle>infinite_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<Longrightarrow>
   all_ordered (is_send_path \<E>' (Ch [] g100))
"
sorry


theorem infinite_prog_single_receiver: "
  [[] \<mapsto> \<langle>infinite_prog;Map.empty;[]\<rangle>] \<rightarrow>* \<E>' \<longrightarrow>
   all_ordered (is_recv_path \<E>' (Ch [] g100))
"
sorry

theorem "
  [[] \<mapsto> \<langle>infinite_prog; Map.empty;[]\<rangle>] \<rightarrow>* \<E>' 
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

lemma infinite_prog_\<V>_restricted: "
  (\<forall> x \<omega> . |\<omega>| \<in> infinite_prog_\<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e infinite_prog))
"
sorry

method elim_traceable_result uses dest = (
  (
    (frule traceable_implies_subexp, rule infinite_prog_\<V>_restricted),
    (simp add: infinite_prog_def; (erule subexp.cases; auto)+, fold infinite_prog_def),
    (rotate_tac -2),
    (frule traceable_implies_subexp, rule infinite_prog_\<V>_restricted),
    (simp add: infinite_prog_def; (erule subexp.cases; auto)+, fold infinite_prog_def),
    (
      (rotate_tac 3),
      (drule dest; simp?; auto),
      ((erule subexp.cases; auto)+)
    )+
  )+
)

method elim_traceable_app = (
  (thin_tac "^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y"),
  (thin_tac "infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>, LET x = APP f x\<^sub>a in e\<^sub>n') "),
  (simp add: infinite_prog_\<V>_def; (match premises in I: "_ \<in> (if P then _ else _) " for P \<Rightarrow> \<open>cases P\<close>, auto)+)
)

method elim_traceable = (
  (drule traceable_implies_subexp, rule infinite_prog_\<V>_restricted),
  (simp add: infinite_prog_def; (erule subexp.cases; auto)+)
)

lemma infinite_prog_has_earlier_sync: "
  \<lbrakk>
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>\<^sub>y, LET x\<^sub>y = SYNC x\<^sub>e in e\<^sub>n);
    ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x\<^sub>y;
    \<pi>\<^sub>y ;; `x\<^sub>y \<noteq> [`g100, .g101, `g102, `g108, \<upharpoonleft>g109, `g105, `g106]
  \<rbrakk> \<Longrightarrow>
  (\<exists>\<pi> x. 
    \<pi>\<^sub>y ;; `x\<^sub>y = (\<pi> ;; `x) @ [\<upharpoonleft>g107, `g105, `g106] \<and>
    infinite_prog_\<V> \<turnstile> infinite_prog \<down> (\<pi>, LET x = SYNC x\<^sub>e in e\<^sub>n) \<and> 
    ^\<lparr>\<rparr> \<in> infinite_prog_\<V> x
  )
"
(*

these proof procedures take way too long.
There is quite a bit of eliminating false premises, by looking at cases of cases of cases ... at multiple depths.

Perhaps, the correct behavior of a computable function would be much faster to prove.
Since it's deterministic, there would be no need to waste time eliminating false premises.
*)
(*

 apply (erule traceable.cases; clarsimp)
  apply (simp add: infinite_prog_def)
  apply (elim_traceable_result dest: traceable_result_implies_traceable_case_left)
  apply (elim_traceable_result dest: traceable_result_implies_traceable_case_right)
  apply (elim_traceable_result dest: traceable_result_implies_traceable_app)
  apply (elim_traceable_app)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)
  apply (elim_traceable)

  apply (erule traceable.cases; clarsimp)
    apply (simp add: infinite_prog_def; auto)
*)
sorry


lemma infinite_prog_matches': "
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
    "(&x) :@: _  |\<rhd> x # _" for x \<Rightarrow> \<open>(rule cons_eq_append[THEN subst], rule ap_matches.Concat, rule ap_matches.Atom)\<close>
  )+
  apply (rule ap_matches.Star_Empty)
 (* Inductive case *)
 apply ((drule infinite_prog_has_earlier_sync; simp), (erule exE)+)
  apply (drule_tac x = "(length (\<pi> ;; `x))" in spec, clarsimp)
  apply (drule_tac x = "\<pi>" in spec, clarsimp)
  apply (drule_tac x = "x" in spec)
  apply (drule_tac x = "x\<^sub>e" in spec, erule impE, rule_tac x = "e\<^sub>n" in exI, assumption)
  apply (drule_tac x = "x\<^sub>s\<^sub>c" in spec, erule impE, assumption)
  apply (drule_tac x = "x\<^sub>m" in spec, (erule impE, assumption)+)
  apply (subgoal_tac "&\<upharpoonleft>g107 :@: &`g105 :@: &`g106 |\<rhd> [\<upharpoonleft>g107, `g105, `g106]")
  apply (drule ap_matches.Concat; simp)
  apply (thin_tac "&\<upharpoonleft>g107 :@: &`g105 :@: &`g106 |\<rhd> [\<upharpoonleft>g107, `g105, `g106]")
  apply ((erule ap_matches.cases; auto), erule ap_matches.Concat)+
  apply (erule concat_star_implies_star)
  apply (match conclusion in 
    "(&x) :@: _  |\<rhd> x # _" for x \<Rightarrow> \<open>(rule cons_eq_append[THEN subst], rule ap_matches.Concat, rule ap_matches.Atom)\<close>
  )+
  apply (rule ap_matches.Atom)
done

lemma infinite_prog_matches: "
  is_static_send_path (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100 \<pi> \<Longrightarrow> 
  infinite_prog_send_g100_abstract_path |\<rhd> \<pi>
"
 apply (simp add: is_static_send_path_def; clarsimp)
 apply (insert infinite_prog_matches', blast)
done

theorem infinite_prog_has_single_sender_communication_analysis: "
  all (is_static_send_path (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100) noncompetitive 
"

sorry


theorem infinite_prog_has_single_receiver_communication_analysis: "
  all (is_static_recv_path (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100) noncompetitive
"
sorry

theorem infinite_prog_has_one_to_one_communication_analysis: "
  static_one_to_one (infinite_prog_\<V>, infinite_prog_\<C>, infinite_prog) g100
"
sorry

(*

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
