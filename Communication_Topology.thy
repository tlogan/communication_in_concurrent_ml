theory Communication_Topology
  imports Main
begin
  
datatype var = Var string
  
value " Var ''x''"
  
datatype chan = Ch "var list"
  
datatype exp = 
  E_Let var bind exp
| E_Var var

and prim = 
  PT_Case var var exp var exp
| PT_Abs var var exp
| PT_Pair var var
| PT_Left var
| PT_Right var

and bind = 
  B_Unit ("\<lparr>\<rparr>")
| B_Chan ("CHAN \<lparr>\<rparr>")
| B_Spawn exp ("SPAWN _" [61] 61)
| B_Send var var
| B_Recv var
| B_Fst var
| B_Snd var
| B_Prim prim
| B_App var var
    
abbreviation exp_let :: "string \<Rightarrow> bind \<Rightarrow> exp \<Rightarrow> exp" ("LET _ = _ |> _" [0,0, 61] 61) where
  "LET x = b |> e \<equiv> E_Let (Var x) b e"
  
abbreviation exp_var :: "string \<Rightarrow> exp" ("VAR _" [61] 61) where
  "VAR x \<equiv> E_Var (Var x)"

abbreviation bind_send :: "string \<Rightarrow> string \<Rightarrow> bind" ("SEND _ _" [61, 61] 61) where
  "SEND x y \<equiv> B_Send (Var x) (Var y)"
  
abbreviation bind_recv :: "string \<Rightarrow> bind" ("RECV _" [61] 61) where
  "RECV x \<equiv> B_Recv (Var x)"
  
abbreviation bind_fst :: "string \<Rightarrow> bind" ("FST _" [61] 61) where
  "FST x \<equiv> B_Fst (Var x)"
  
abbreviation bind_snd :: "string \<Rightarrow> bind" ("SND _" [61] 61) where
  "SND x \<equiv> B_Snd (Var x)"
  
abbreviation bind_app :: "string \<Rightarrow> string \<Rightarrow> bind" ("APP _ _" [61, 61] 61) where
  "APP x y \<equiv> B_App (Var x) (Var y)"

abbreviation bind_case :: "string \<Rightarrow> string \<Rightarrow> exp \<Rightarrow> string \<Rightarrow> exp \<Rightarrow> bind" ("CASE _ LEFT _ |> _ RIGHT _ |> _" [0,0,0,0, 61] 61) where
  "CASE x LEFT xl |> el RIGHT xr |> er \<equiv> B_Prim (PT_Case (Var x) (Var xl) el (Var xr) er)"
  
abbreviation bind_abs :: "string => string => exp => bind" ("FUN _, _ |> _" [0, 0, 61] 61) where
  "FUN f, x |> e \<equiv> B_Prim (PT_Abs (Var f) (Var x) e)"
  
abbreviation bind_pair :: "string => string => bind" ("\<lparr>_, _\<rparr>" [0, 0] 61) where
  "\<lparr>x, y\<rparr> \<equiv> B_Prim (PT_Pair (Var x) (Var y))"
  
abbreviation bind_inl :: "string => bind" ("LEFT _" [61] 61) where
  "LEFT x \<equiv> B_Prim (PT_Left (Var x))"
  
abbreviation bind_inr :: "string => bind" ("RIGHT _" [61] 61) where
  "RIGHT x \<equiv> B_Prim (PT_Right (Var x))"
  
value "Map.empty (Var ''x'' \<mapsto> 4)"
  
  
datatype val = 
  V_Chan chan 
| V_Closure prim "var \<rightharpoonup> val"
| V_Unit
  
  
value "LET ''y'' = \<lparr>\<rparr> |> VAR ''y''"

value "
LET ''y'' = \<lparr>\<rparr> |>
LET ''x'' = CHAN \<lparr>\<rparr> |>
LET ''z'' = \<lparr>''x'', ''y''\<rparr> |>
LET ''a'' = SEND ''x'' ''y'' |>
LET ''b'' = FST ''z'' |>
LET ''c'' = RIGHT ''b'' |>
LET ''d'' = 
  CASE ''c''
  LEFT ''cl'' |> VAR ''cl''
  RIGHT ''cr'' |> VAR ''cr''
|>
VAR ''z''
"

datatype cont = Cont var exp "var \<rightharpoonup> val" ("\<langle>_,_,_\<rangle>" [0, 0, 0] 70) 

type_synonym state = "exp \<times> (var \<rightharpoonup> val) \<times> cont list"
  
inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  SS_Var: "
   (\<rho> x) = Some \<omega>
   \<Longrightarrow>
   (E_Var x, \<rho>, \<langle>x_ct, e_ct, \<rho>_ct\<rangle> # \<kappa>) \<rightarrow> (e_ct, \<rho>_ct(x_ct \<mapsto> \<omega>), \<kappa>)
  "
  
  
end
  