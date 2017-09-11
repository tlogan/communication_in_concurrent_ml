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
| V_Closure val env
| V_Unit
and env = Env "var \<Rightarrow> val option"



datatype cont = Cont var exp env

datatype state = St exp env "cont list"
inductive seq_step :: ""
  
  
end
  