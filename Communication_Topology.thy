theory Communication_Topology
  imports Main
begin
  
datatype var = Var string
  
value " Var ''x''"
  
datatype chan = Ch "var list"
  
datatype exp = E_Let var bind exp | E_Var var

and prim = 
  PT_Case var var exp var exp
| PT_Abs var var exp
| PT_Pair var var
| PT_Inl var
| PT_Inr var

and bind = 
  B_Unit 
| B_Spawn exp 
| B_Send var var
| B_Recv var
| B_Fst var
| B_Snd var
| B_Prim prim
| B_App var var
  
  
value "Map.empty (Var ''x'' \<mapsto> 4)"
  
  
datatype val = 
  V_Chan chan 
| V_Closure prim "var \<rightharpoonup> val"
| V_Unit

type_synonym cont = "var \<times> exp \<times> (var \<rightharpoonup> val)"

type_synonym state = "exp \<times> (var \<rightharpoonup> val) \<times> cont list"
  
inductive seq_step :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where 
  SS_Var: "
   (\<rho> x) = Some \<omega>
   \<Longrightarrow>
   (E_Var x, \<rho>, (x_ct, e_ct, \<rho>_ct) # \<kappa>) \<rightarrow> (e_ct, \<rho>_ct(x_ct \<mapsto> \<omega>), \<kappa>)
  "
  
  
end
  