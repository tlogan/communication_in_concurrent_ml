theory Communication_Topology_Soundness
  imports 
    Main 
    Syntax Semantics 
    Abstract_Value_Flow_Analysis Abstract_Value_Flow_Soundness
    Communication_Topology_Analysis
begin

theorem topology_sound : "
  \<lbrakk>
    \<A> \<bind> e; 
    [[] \<mapsto> <<e, empty, []>>] \<rightarrow>* \<E>'
  \<rbrakk> \<Longrightarrow>
  \<langle>\<langle>\<E>'\<rangle>\<rangle> \<sqsubseteq>\<^sub>t \<A>
"
 sorry


end