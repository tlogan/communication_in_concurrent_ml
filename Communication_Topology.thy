theory Communication_Topology
  imports Main
begin
  
datatype var = Var string
  
value " Var ''x''"
  
datatype chan = Ch "var list"
  
datatype exp = 
  E_Let var bind exp ("LET _ = _ in _" [0,0, 61] 61)
| E_Result var ("RESULT _" [61] 61)

and prim = 
  PT_Abs var var exp
| PT_Pair var var
| PT_Left var
| PT_Right var

and bind = 
  B_Unit ("\<lparr>\<rparr>")
| B_Chan ("CHAN \<lparr>\<rparr>")
| B_Spawn exp ("SPAWN _" [61] 61)
| B_Send var var ("SEND _ _" [61, 61] 61)
| B_Recv var ("RECV _" [61] 61)
| B_Fst var ("FST _" [61] 61)
| B_Snd var ("SND _" [61] 61)
| B_Case var var exp var exp ("CASE _ LEFT _ |> _ RIGHT _ |> _" [0,0,0,0, 61] 61)
| B_Prim prim
| B_App var var ("APP _ _" [61, 61] 61)
  
abbreviation bind_abs :: "var => var => exp => bind" ("FN _ _ . _" [0, 0, 61] 61) where
  "FN f x . e \<equiv> B_Prim (PT_Abs f x e)"
  
abbreviation bind_pair :: "var => var => bind" ("\<lparr>_, _\<rparr>" [0, 0] 61) where
  "\<lparr>x, y\<rparr> \<equiv> B_Prim (PT_Pair x y)"
  
abbreviation bind_inl :: "var => bind" ("LEFT _" [61] 61) where
  "LEFT x \<equiv> B_Prim (PT_Left x)"
  
abbreviation bind_inr :: "var => bind" ("RIGHT _" [61] 61) where
  "RIGHT x \<equiv> B_Prim (PT_Right x)"
  
value "Map.empty (Var ''x'' \<mapsto> 4)"

  
datatype val = 
  V_Chan chan ("\<lbrace>_\<rbrace>")
| V_Closure prim "var \<rightharpoonup> val" ("\<lbrace>_, _\<rbrace>")
| V_Unit ("\<lbrace>\<rbrace>")

  
fun closure :: "bind \<Rightarrow> (var \<rightharpoonup> val) \<Rightarrow> val option" ("\<lbrace>_, _\<rbrace>?") where
  "\<lbrace>B_Prim p, \<rho>\<rbrace>? = Some (V_Closure p \<rho>)" |
  "\<lbrace>_, _\<rbrace>? = None"


datatype cont = Cont var exp "var \<rightharpoonup> val" ("\<langle>_,_,_\<rangle>" [0, 0, 0] 70) 

type_synonym state = "exp \<times> (var \<rightharpoonup> val) \<times> cont list"
  
inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  SS_Result: "
    (\<rho> x) = Some \<omega>
    \<Longrightarrow>
    (RESULT x, \<rho>, \<langle>x_ct, e_ct, \<rho>_ct\<rangle> # \<kappa>) \<rightarrow> (e_ct, \<rho>_ct(x_ct \<mapsto> \<omega>), \<kappa>)
  " |
   SS_Let_Unit: "
    \<omega> = \<lbrace>\<rbrace>
    \<Longrightarrow>
    (LET x = \<lparr>\<rparr> in e, \<rho>, \<kappa>) \<rightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  SS_Let_Prim: "
    Some \<omega> = \<lbrace>b, \<rho>\<rbrace>?
    \<Longrightarrow>
    (LET x = b in e, \<rho>, \<kappa>) \<rightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  SS_Let_Case_Left: "
    \<lbrakk>(\<rho> x_sum) = \<lbrace>LEFT x_ll, \<rho>_l\<rbrace>? ; (\<rho>_l x_ll) = Some \<omega>_l \<rbrakk>
    \<Longrightarrow>
    (LET x = CASE x_sum LEFT x_l |> e_l RIGHT _ |> _ in e, \<rho>, \<kappa>) \<rightarrow> (e_l, \<rho>(x_l \<mapsto> \<omega>_l), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  SS_Let_Case_Right: "
    \<lbrakk>(\<rho> x_sum) = \<lbrace>RIGHT x_rr, \<rho>_r\<rbrace>? ; (\<rho>_r x_rr) = Some \<omega>_r \<rbrakk>
    \<Longrightarrow>
    (LET x = CASE x_sum LEFT _ |> _ RIGHT x_r |> e_r in e, \<rho>, \<kappa>) \<rightarrow> (e_r, \<rho>(x_r \<mapsto> \<omega>_r), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  " |
  SS_Fst: "
  \<lbrakk> (\<rho> x_p) = \<lbrace>\<lparr>x1, _\<rparr>, \<rho>_p\<rbrace>? ; (\<rho>_p x1) = Some \<omega> \<rbrakk>
  \<Longrightarrow>
  (LET x = FST x_p in e, \<rho>, \<kappa>) \<rightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  SS_Snd: "
  \<lbrakk> (\<rho> x_p) = \<lbrace>\<lparr>_, x2\<rparr>, \<rho>_p\<rbrace>? ; (\<rho>_p x2) = Some \<omega> \<rbrakk>
  \<Longrightarrow>
  (LET x = FST x_p in e, \<rho>, \<kappa>) \<rightarrow> (e, \<rho>(x \<mapsto> \<omega>), \<kappa>)
  " |
  SS_Let_App: "\<lbrakk>
    (\<rho> x_f) = Some \<omega>_f ; Some \<omega>_f = \<lbrace>FN x_f_abs x_a_abs. e_abs, \<rho>_abs\<rbrace>? ; (\<rho> x_a) = Some \<omega>_a \<rbrakk>
    \<Longrightarrow>
    (LET x = APP x_f x_a in e, \<rho>, \<kappa>) \<rightarrow> (e_abs, \<rho>_abs(x_f_abs \<mapsto> \<omega>_f, x_a_abs \<mapsto> \<omega>_a), \<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "
  
inductive seq_steps :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where
  SSS_Refl: "x \<rightarrow>* x" |
  SSS_Step: "\<lbrakk>x \<rightarrow> y ; y \<rightarrow>* z\<rbrakk> \<Longrightarrow> x \<rightarrow>* z"
  
abbreviation a where "a \<equiv> Var ''a''"
abbreviation b where "b \<equiv> Var ''b''"
abbreviation c where "c \<equiv> Var ''c''"
  
abbreviation d where "d \<equiv> Var ''d''"
abbreviation e where "e \<equiv> Var ''e''"
abbreviation f where "f \<equiv> Var ''f''"
  
abbreviation x where "x \<equiv> Var ''x''"
abbreviation y where "y \<equiv> Var ''y''"
abbreviation z where "z \<equiv> Var ''z''"
  
value "LET y = \<lparr>\<rparr> in VAR y"

value "
LET a = \<lparr>\<rparr> in
LET b = CHAN \<lparr>\<rparr> in
LET c = \<lparr>a, b\<rparr> in
LET x = SEND b a in
LET y = FST c in
LET z = RIGHT y in
LET d = 
  CASE z
  LEFT d |> RESULT d
  RIGHT d |> RESULT d
in
LET e = FN f x .
  LET a = APP f x in
  RESULT a
in
RESULT c
"
  
  
end