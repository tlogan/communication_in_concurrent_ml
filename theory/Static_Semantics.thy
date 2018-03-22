theory Static_Semantics
  imports Main Syntax Runtime_Semantics
    "~~/src/HOL/Library/List"
begin

datatype abstract_value = A_Chan var ("^Chan _" [61] 61) | A_Unit ("^\<lparr>\<rparr>") | A_Prim prim ("^_" [61] 61 )

type_synonym abstract_value_env = "var \<Rightarrow> abstract_value set"

fun result_var :: "exp \<Rightarrow> var" ("\<lfloor>_\<rfloor>" [0]61) where
  "\<lfloor>RESULT x\<rfloor> = x" |
  "\<lfloor>LET _ = _ in e\<rfloor> = \<lfloor>e\<rfloor>"


inductive accept_exp :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> exp \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>e" 55) where
  Result: "
    (\<V>, \<C>) \<Turnstile>\<^sub>e (RESULT x)
  " |
  Let_Unit: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>\<rparr> in e
  " |

  Let_Chan: "
    \<lbrakk>
      {^Chan x} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CHAN \<lparr>\<rparr> in e
  " |

  Let_Send_Evt : "
    \<lbrakk>
      {^Send_Evt x\<^sub>c x\<^sub>m} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt : "
    \<lbrakk>
      {^Recv_Evt x\<^sub>c} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = RECV EVT x\<^sub>c in e
  " |

  Let_Pair : "
    \<lbrakk>
      {^Pair x\<^sub>1 x\<^sub>2} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left : "
    \<lbrakk>
      {^Left x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = LEFT x\<^sub>p in e
  " |
  Let_Right : "
    \<lbrakk>
      {^Right x\<^sub>p} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = RIGHT x\<^sub>p in e
  " |

  Let_Abs : "
    \<lbrakk>
      {^Abs f' x' e'} \<subseteq> \<V> f';
      (\<V>, \<C>) \<Turnstile>\<^sub>e e';
      {^Abs f' x' e'} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FN f' x' . e' in e
  " |

  Let_Spawn: "
    \<lbrakk>
      {^\<lparr>\<rparr>} \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>c;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SPAWN e\<^sub>c in e
  " |

  Let_Sync  : "
    \<lbrakk>
      \<forall> x\<^sub>s\<^sub>c x\<^sub>m x\<^sub>c . 
        ^Send_Evt x\<^sub>s\<^sub>c x\<^sub>m \<in> \<V> x\<^sub>e \<longrightarrow> 
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>s\<^sub>c \<longrightarrow>
        {^\<lparr>\<rparr>} \<subseteq> \<V> x \<and> \<V> x\<^sub>m \<subseteq> \<C> x\<^sub>c
      ;
      \<forall> x\<^sub>r\<^sub>c x\<^sub>c . 
        ^Recv_Evt x\<^sub>r\<^sub>c \<in> \<V> x\<^sub>e \<longrightarrow>
        ^Chan x\<^sub>c \<in> \<V> x\<^sub>r\<^sub>c \<longrightarrow>
        \<C> x\<^sub>c \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow>  
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SYNC x\<^sub>e in e
  " |

  Let_Fst: "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2. ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>1 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile>\<^sub>e e 
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk>
      \<forall> x\<^sub>1 x\<^sub>2 . ^Pair x\<^sub>1 x\<^sub>2 \<in> \<V> x\<^sub>p \<longrightarrow> \<V> x\<^sub>2 \<subseteq> \<V> x; 
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = SND x\<^sub>p in e
  " |
  Let_Case: "
    \<lbrakk>
      \<forall> x\<^sub>l' . ^Left x\<^sub>l' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>l' \<subseteq> \<V> x\<^sub>l \<and> \<V> (\<lfloor>e\<^sub>l\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>l
      ;
      \<forall> x\<^sub>r' . ^Right x\<^sub>r' \<in> \<V> x\<^sub>s \<longrightarrow>
        \<V> x\<^sub>r' \<subseteq> \<V> x\<^sub>r \<and> \<V> (\<lfloor>e\<^sub>r\<rfloor>) \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>e e\<^sub>r
      ;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  " |
  Let_App: "
    \<lbrakk>
      \<forall> f' x' e' . ^Abs f' x' e' \<in> \<V> f \<longrightarrow>
        \<V> x\<^sub>a \<subseteq> \<V> x' \<and>
        \<V> (\<lfloor>e'\<rfloor>) \<subseteq> \<V> x
      ;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>e LET x = APP f x\<^sub>a in e
  "


fun value_to_abstract_value :: "val \<Rightarrow> abstract_value" ("|_|" [0]61) where
  "|\<lbrace>\<rbrace>| = ^\<lparr>\<rparr>" |
  "|\<lbrace>Ch \<pi> x\<rbrace>| = ^Chan x" |
  "|\<lbrace>p, \<rho>\<rbrace>| = ^p"


definition env_to_abstract_value_env :: "(var \<rightharpoonup> val) \<Rightarrow> abstract_value_env" ("\<parallel>_\<parallel>" [0]61) where
  "\<parallel>\<rho>\<parallel> = (\<lambda> x . (case (\<rho> x) of 
    Some \<omega> \<Rightarrow> {|\<omega>|} |
    None \<Rightarrow> {}
  ))"

inductive accept_value :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<omega>" 55)
and  accept_val_env :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> val_env \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<rho>" 55) 
where
  Unit: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>\<rbrace>
  " |

  Chan: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>c\<rbrace>
  " |

  Send_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Send_Evt _ _, \<rho>\<rbrace>
  " |

  Recv_Evt: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Recv_Evt _, \<rho>\<rbrace>
  " |

  Left: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Left _, \<rho>\<rbrace>
  " |

  Right: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Right _, \<rho>\<rbrace>
  " |

  Abs: "
    \<lbrakk>
      {^Abs f x e} \<subseteq> \<V> f;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Abs f x e, \<rho>\<rbrace>
  " |

  Pair: "
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
    \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<lbrace>Pair _ _, \<rho>\<rbrace>
  " |

  Any : "
    \<lbrakk>
      (\<forall> x \<omega> . \<rho> x = Some \<omega> \<longrightarrow>
        {|\<omega>|} \<subseteq> \<V> x \<and> (\<V>, \<C>) \<Turnstile>\<^sub>\<omega> \<omega>
      )
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>
  "


inductive accept_stack :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> abstract_value set \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>\<kappa> _ \<Rrightarrow> _" [56,0,56]55) where
  Empty: "(\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> []" |
  Nonempty: "
    \<lbrakk> 
      \<W> \<subseteq> \<V> x;
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<W> \<Rrightarrow> (\<langle>x, e, \<rho>\<rangle> # \<kappa>)
  "


inductive accept_state :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<sigma>" 55)  where
  Any: "
    \<lbrakk>
      (\<V>, \<C>) \<Turnstile>\<^sub>e e;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<rho> \<rho>;
      (\<V>, \<C>) \<Turnstile>\<^sub>\<kappa> \<V> (\<lfloor>e\<rfloor>) \<Rrightarrow> \<kappa>
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<langle>e; \<rho>; \<kappa>\<rangle>
  "

inductive accept_state_pool :: "abstract_value_env \<times> abstract_value_env \<Rightarrow> state_pool \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<E>" 55) where
  Any: "
    (\<forall> \<pi> \<sigma> . \<E> \<pi> = Some \<sigma> \<longrightarrow> (\<V>, \<C>) \<Turnstile>\<^sub>\<sigma> \<sigma>)
    \<Longrightarrow> 
    (\<V>, \<C>) \<Turnstile>\<^sub>\<E> \<E>
  "
   
definition abstract_value_env_precision :: "abstract_value_env \<Rightarrow> abstract_value_env \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "\<V> \<sqsubseteq> \<V>' \<equiv> (\<forall> x . \<V> x \<subseteq> \<V>' x)"


inductive traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> control_path \<Rightarrow> exp \<Rightarrow> bool" ("_ \<turnstile> _ \<down> _ \<mapsto> _" [56,0,0,56]55)  where
  Start: "
    \<V> \<turnstile> e\<^sub>0 \<down> [] \<mapsto> e\<^sub>0
  " |
  Result: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ \<upharpoonleft>x # \<pi>' \<mapsto> RESULT x\<^sub>r; 
      \<downharpoonright>\<pi>'\<upharpoonleft>;
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = b in e\<^sub>n 
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> @ \<upharpoonleft>x # (\<pi>';;\<downharpoonleft>x) \<mapsto> e\<^sub>n
  " |
  Let_Unit: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = \<lparr>\<rparr> in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Chan: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CHAN \<lparr>\<rparr> in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Prim: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = Prim p in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Spawn_Child: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SPAWN e\<^sub>c in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;.x \<mapsto> e\<^sub>c
  " |
  Let_Spawn: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SPAWN e\<^sub>c in e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Sync: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SYNC x\<^sub>v in e\<^sub>n;
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Fst: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = FST p in e\<^sub>n;
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Snd: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = SND p in e\<^sub>n;
      (* constraint below not necessary for our purposes*)
      |\<omega>| \<in> \<V> x
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;`x \<mapsto> e\<^sub>n
  " |
  Let_Case_Left: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n;
      (* constraint below not necessary for our purposes*)
      ^Left x\<^sub>l' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;\<upharpoonleft>x \<mapsto> e\<^sub>l
  " |
  Let_Case_Right: "
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n;
      ^Right x\<^sub>r' \<in> \<V> x\<^sub>s
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;\<upharpoonleft>x \<mapsto> e\<^sub>r
  " |
  Let_App: " 
    \<lbrakk>
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> LET x = APP f x\<^sub>a in e\<^sub>n;
      ^Abs f' x' e' \<in> \<V> f
    \<rbrakk> \<Longrightarrow>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi>;;\<upharpoonleft>x \<mapsto> e'
  "

inductive stack_traceable :: "abstract_value_env \<Rightarrow> exp \<Rightarrow> control_path \<Rightarrow> cont list \<Rightarrow> bool" ("_ \<tturnstile> _ \<down> _ \<mapsto> _" [56,0,0,56]55)  where
  Empty: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<upharpoonleft>
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e \<down> \<pi> \<mapsto> []
  " |
  Empty_Local: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ .x # \<pi>\<^sub>2 \<mapsto> []
  " |
  Nonempty: "
    \<lbrakk> 
      \<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>;
      \<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>;
      \<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> \<kappa>
    \<rbrakk> \<Longrightarrow>
    \<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ \<upharpoonleft>x\<^sub>\<kappa> # \<pi>\<^sub>2 \<mapsto> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>
  "


lemma singleton_eq_empty_surround: "
  [l] = ([] @ l # [])
"
by simp

lemma stack_traceable_preserved_over_balanced_extension:
  "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow> \<downharpoonright>\<pi>'\<upharpoonleft> \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" 
proof -
  assume "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa>" "\<downharpoonright>\<pi>'\<upharpoonleft>" then 
  show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>"
  proof (cases rule: stack_traceable.cases)
    case Empty 
    from `\<downharpoonright>\<pi>\<upharpoonleft>` `\<downharpoonright>\<pi>'\<upharpoonleft>`
    have "\<downharpoonright>(\<pi> @ \<pi>')\<upharpoonleft>" by (simp add: Append) then
    have "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> []" by (simp add: stack_traceable.Empty)
    with `\<kappa> = []`
    show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" by blast
  next
    case (Empty_Local \<pi>\<^sub>2 \<pi>\<^sub>1 x)
    from `\<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>` `\<downharpoonright>\<pi>'\<upharpoonleft>` 
    have "\<downharpoonright>(\<pi>\<^sub>2 @ \<pi>')\<upharpoonleft>" by (simp add: Append) then
    have "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ .x # \<pi>\<^sub>2 @ \<pi>' \<mapsto> []" by (simp add: stack_traceable.Empty_Local)
    with `\<pi> = \<pi>\<^sub>1 @ .x # \<pi>\<^sub>2` `\<kappa> = []` 
    show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" by simp
  next
    case (Nonempty \<pi>\<^sub>2 \<pi>\<^sub>1 x\<^sub>\<kappa> b e\<^sub>\<kappa> \<kappa>' \<rho>\<^sub>\<kappa>) 
    from `\<downharpoonright>\<pi>\<^sub>2\<upharpoonleft>` `\<downharpoonright>\<pi>'\<upharpoonleft>`
    have "\<downharpoonright>(\<pi>\<^sub>2 @ \<pi>')\<upharpoonleft>" by (simp add: Append)
    with `\<V> \<turnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> LET x\<^sub>\<kappa> = b in e\<^sub>\<kappa>` `\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 \<mapsto> \<kappa>'`
    have "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi>\<^sub>1 @ \<upharpoonleft>x\<^sub>\<kappa> # \<pi>\<^sub>2 @ \<pi>' \<mapsto> \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>'" by (auto simp: stack_traceable.Nonempty)
    with `\<pi> = \<pi>\<^sub>1 @ \<upharpoonleft>x\<^sub>\<kappa> # \<pi>\<^sub>2` `\<kappa> = \<langle>x\<^sub>\<kappa>,e\<^sub>\<kappa>,\<rho>\<^sub>\<kappa>\<rangle> # \<kappa>'`
    show "\<V> \<tturnstile> e\<^sub>0 \<down> \<pi> @ \<pi>' \<mapsto> \<kappa>" by simp
  qed
qed
(*
apply (erule stack_traceable.cases; auto)
   apply (simp add: stack_traceable.Empty)
  apply (simp add: Empty_Local)
 apply (simp add: stack_traceable.Nonempty)
done
*)

lemma stack_traceable_preserved_over_seq_extension:"
  \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> \<mapsto> \<kappa> \<Longrightarrow> \<V> \<tturnstile> e\<^sub>0 \<down> \<pi> ;; `x \<mapsto> \<kappa>
"
by (simp add: Linear stack_traceable_preserved_over_balanced_extension)

inductive subexp :: "exp \<Rightarrow> exp \<Rightarrow> bool" ("_ \<preceq>\<^sub>e _" [56,56]55) where
  Refl : "
    e \<preceq>\<^sub>e e
  " | 
  Let: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>n
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = b in e\<^sub>n)
  " | 
  Let_Spawn_Child: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>c
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = SPAWN e\<^sub>c in e\<^sub>n)
  " |
  Let_Case_Left: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>l
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " | 
  Let_Case_Right: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>r
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n)
  " |
  Let_Abs_Body: "
    \<lbrakk>
      e \<preceq>\<^sub>e e\<^sub>b 
    \<rbrakk> \<Longrightarrow>
    e \<preceq>\<^sub>e (LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n)
  "

lemma subexp_trans: "
  e\<^sub>x \<preceq>\<^sub>e e\<^sub>y \<Longrightarrow> e\<^sub>y \<preceq>\<^sub>e e\<^sub>z \<Longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>z
"
proof -
  assume "e\<^sub>x \<preceq>\<^sub>e e\<^sub>y"
  assume "e\<^sub>y \<preceq>\<^sub>e e\<^sub>z" then
  have "(\<forall> e\<^sub>x . e\<^sub>x \<preceq>\<^sub>e e\<^sub>y \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>z)"
  proof (induction rule: subexp.induct)
    case (Refl e)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e" by simp
  next
    case (Let e e\<^sub>n x b)
    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>n \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = b in e\<^sub>n" by (simp add: subexp.Let) 
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>n` (* IH *)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = b in e\<^sub>n" by blast
  next
    case (Let_Spawn_Child e e\<^sub>c x e\<^sub>n)
    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>c \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = SPAWN e\<^sub>c in e\<^sub>n" by (simp add: subexp.Let_Spawn_Child)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>c` (* IH *)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = SPAWN e\<^sub>c in e\<^sub>n"by blast
  next
    case (Let_Case_Left e e\<^sub>l x x\<^sub>s x\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n)
    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>l \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by (simp add: subexp.Let_Case_Left)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>l` (* IH *)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by blast
  next
    case (Let_Case_Right e e\<^sub>r x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>n)
    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>r \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by (simp add: subexp.Let_Case_Right)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>r` (* IH *)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e\<^sub>n" by blast
  next
    case (Let_Abs_Body e e\<^sub>b x f x\<^sub>p e\<^sub>n)
    have "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e\<^sub>b \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n" by (simp add: subexp.Let_Abs_Body)
    with `\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e e\<^sub>b` (* IH *)
    show "\<forall>e\<^sub>x. e\<^sub>x \<preceq>\<^sub>e e \<longrightarrow> e\<^sub>x \<preceq>\<^sub>e LET x = FN f x\<^sub>p . e\<^sub>b in e\<^sub>n" by blast
  qed 
  with `e\<^sub>x \<preceq>\<^sub>e e\<^sub>y`
  show "e\<^sub>x \<preceq>\<^sub>e e\<^sub>z" by blast
qed
(*
  apply (erule subexp.induct; auto)
   apply (drule spec; auto, rule subexp.Let, assumption)
   apply (drule spec; auto, rule subexp.Let_Spawn_Child, assumption)
   apply (drule spec; auto, rule subexp.Let_Case_Left, assumption)
   apply (drule spec; auto, rule subexp.Let_Case_Right, assumption)
   apply (drule spec; auto, rule subexp.Let_Abs_Body, assumption)
*)

lemma subexp1: "
  e\<^sub>n \<preceq>\<^sub>e LET x = b in e\<^sub>n
"
by (simp add: Let Refl)

(*
lemma traceable_implies_subexp': "
  \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e \<Longrightarrow>
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0)) \<longrightarrow>
    e \<preceq>\<^sub>e e\<^sub>0
"
 apply (erule traceable.induct; auto)
    apply (rule subexp.Refl)

   apply (rotate_tac -1, rule subexp_trans; auto?; rule subexp1)+

   apply (rule subexp_trans; auto?; rule subexp.Let_Spawn_Child; rule subexp.Refl)
         
   apply (rotate_tac -1, rule subexp_trans; auto?; rule subexp1)+
      
   apply (rule subexp_trans; auto?; rule subexp.Let_Case_Left; rule subexp.Refl)
   
   apply (rule subexp_trans; auto?; rule subexp.Let_Case_Right; rule subexp.Refl)

   apply (drule_tac x = f in spec)
   apply (drule_tac x = "\<lbrace> Abs f' x' e' , _\<rbrace>" in spec)
   apply (erule impE; simp)
   apply (blast intro:  Let_Abs_Body Refl subexp_trans)

done
*)

theorem traceable_implies_subexp: "
  \<lbrakk>
    \<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e;
    (\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0))
  \<rbrakk> \<Longrightarrow>
  e \<preceq>\<^sub>e e\<^sub>0
"
proof -
  assume "\<forall>x \<omega>. |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists>x e\<^sub>n. LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0)"
  assume "\<V> \<turnstile> e\<^sub>0 \<down> \<pi> \<mapsto> e" then
  have "(\<forall> x \<omega> . |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists> x e\<^sub>n . LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0)) \<longrightarrow> e \<preceq>\<^sub>e e\<^sub>0"
  proof (induction rule: traceable.induct)
    case (Start \<V> e\<^sub>0)
    then show ?case
    by (simp add: Refl)
  next
    case (Result \<V> e\<^sub>0 \<pi> x \<pi>' x\<^sub>r b e\<^sub>n)
    then show ?case
    using subexp1 subexp_trans by blast
  next
    case (Let_Unit \<V> e\<^sub>0 \<pi> x e\<^sub>n)
    then show ?case
    using subexp1 subexp_trans by blast
  next
    case (Let_Chan \<V> e\<^sub>0 \<pi> x e\<^sub>n)
    then show ?case
    using subexp1 subexp_trans by blast
  next
    case (Let_Prim \<V> e\<^sub>0 \<pi> x p e\<^sub>n)
    then show ?case
    using subexp1 subexp_trans by blast
    next
    case (Let_Spawn_Child \<V> e\<^sub>0 \<pi> x e\<^sub>c e\<^sub>n)
    then show ?case
    using Refl subexp.Let_Spawn_Child subexp_trans by blast
  next
    case (Let_Spawn \<V> e\<^sub>0 \<pi> x e\<^sub>c e\<^sub>n)
    then show ?case
    using subexp1 subexp_trans by blast
  next
      case (Let_Sync \<V> e\<^sub>0 \<pi> x x\<^sub>v e\<^sub>n \<omega>)
    then show ?case
    using subexp1 subexp_trans by blast
  next
    case (Let_Fst \<V> e\<^sub>0 \<pi> x p e\<^sub>n \<omega>)
    then show ?case
    using subexp1 subexp_trans by blast
  next
    case (Let_Snd \<V> e\<^sub>0 \<pi> x p e\<^sub>n \<omega>)
      then show ?case
        using subexp1 subexp_trans by blast
  next
    case (Let_Case_Left \<V> e\<^sub>0 \<pi> x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n x\<^sub>l')
    then show ?case
      using Refl subexp.Let_Case_Left subexp_trans by blast
  next
    case (Let_Case_Right \<V> e\<^sub>0 \<pi> x x\<^sub>s x\<^sub>l e\<^sub>l x\<^sub>r e\<^sub>r e\<^sub>n x\<^sub>r')
    then show ?case
    using Refl subexp.Let_Case_Right subexp_trans by blast
  next
    case (Let_App \<V> e\<^sub>0 \<pi> x f x\<^sub>a e\<^sub>n f' x' e')
    then show ?case
    by (metis (no_types, hide_lams) Let_Abs_Body Refl subexp_trans val_to_bind.simps(3) value_to_abstract_value.simps(3))
  qed
  with `\<forall>x \<omega>. |\<omega>| \<in> \<V> x \<longrightarrow> (\<exists>x e\<^sub>n. LET x = val_to_bind \<omega> in e\<^sub>n \<preceq>\<^sub>e e\<^sub>0)`
  show "e \<preceq>\<^sub>e e\<^sub>0"
  by blast
qed


type_synonym flow_set = "(exp \<times> control_label \<times> exp) set"
(* this a nice order for the rules; update other definitions to use same order*)
inductive flow :: "(abstract_value_env \<times> flow_set) \<Rightarrow> exp \<Rightarrow> bool" (infix "\<TTurnstile>" 55) where
  Result: "
    (\<V>, \<F>) \<TTurnstile> RESULT x
  " |
  Let_Unit: "
    \<lbrakk>
      {(LET x = \<lparr>\<rparr> in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = \<lparr>\<rparr> in e
  " |
  Let_Chan: "
    \<lbrakk>
      {(LET x = CHAN \<lparr>\<rparr> in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = CHAN \<lparr>\<rparr> in e
  " |
  Let_Send_Evt: "
    \<lbrakk>
      {(LET x = SEND EVT x\<^sub>c x\<^sub>m  in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SEND EVT x\<^sub>c x\<^sub>m in e
  " |
  Let_Recv_Evt: "
    \<lbrakk>
      {(LET x = RECV EVT x\<^sub>c  in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = RECV EVT x\<^sub>c in e
  " |
  Let_Pair: "
    \<lbrakk>
      {(LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = \<lparr>x\<^sub>1, x\<^sub>2\<rparr> in e
  " |
  Let_Left: "
    \<lbrakk>
      {(LET x = LEFT x\<^sub>p in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = LEFT x\<^sub>p in e
  " |
  Let_Right: "
    \<lbrakk>
      {(LET x = RIGHT x\<^sub>p in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = RIGHT x\<^sub>p in e
  " |
  Let_Abs: "
    \<lbrakk>
      {(LET x = FN f x\<^sub>p . e\<^sub>b  in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>b;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = FN f x\<^sub>p . e\<^sub>b  in e
  " |
  Let_Spawn: "
    \<lbrakk>
      {
        (LET x = SPAWN e\<^sub>c  in e, `x, e),
        (LET x = SPAWN e\<^sub>c  in e, .x, e\<^sub>c)
      } \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>c;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SPAWN e\<^sub>c in e
  " |
  Let_Sync: "
    \<lbrakk>
      {(LET x = SYNC x\<^sub>e in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SYNC x\<^sub>e in e
  " |
  Let_Fst: "
    \<lbrakk>
      {(LET x = FST x\<^sub>p in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = FST x\<^sub>p in e
  " |
  Let_Snd: "
    \<lbrakk>
      {(LET x = FST x\<^sub>p in e, `x, e)} \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = SND x\<^sub>p in e
  " |
  Let_Case: "
    \<lbrakk>
      {
        (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e, \<upharpoonleft>x, e\<^sub>l),
        (LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e, \<upharpoonleft>x, e\<^sub>r),
        (RESULT \<lfloor>e\<^sub>l\<rfloor>, \<downharpoonleft>x, e),
        (RESULT \<lfloor>e\<^sub>r\<rfloor>, \<downharpoonleft>x, e)
      } \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>l;
      (\<V>, \<F>) \<TTurnstile> e\<^sub>r;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile>LET x = CASE x\<^sub>s LEFT x\<^sub>l |> e\<^sub>l RIGHT x\<^sub>r |> e\<^sub>r in e
  "|
  Let_App: "
    \<lbrakk>

      \<forall> f' x\<^sub>p e\<^sub>b . ^Abs f' x\<^sub>p e\<^sub>b \<in> \<V> f \<longrightarrow>
      {
        (LET x = APP f x\<^sub>a in e, \<upharpoonleft>x, e\<^sub>b),
        (RESULT \<lfloor>e\<^sub>b\<rfloor>, \<downharpoonleft>x, e)
      } \<subseteq> \<F>;
      (\<V>, \<F>) \<TTurnstile> e
    \<rbrakk> \<Longrightarrow>
    (\<V>, \<F>) \<TTurnstile> LET x = APP f x\<^sub>a in e
  "
  
end