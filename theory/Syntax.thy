theory Syntax
  imports Main
begin
  
datatype var = Var string

(* ANF grammar *)
datatype exp = 
  Let var bind exp ("LET _ = _ in _" [0,0, 61] 61) |
  Result var ("RESULT _" [61] 61)

and prim = 
  Abs var var exp |
  Pair var var |
  Left var |
  Right var |
  Send_Evt var var |
  Recv_Evt var |
  Always_Evt var

and bind = 
  Unit ("\<lparr>\<rparr>") |
  Chan ("CHAN \<lparr>\<rparr>") |
  Spawn exp ("SPAWN _" [61] 61) |
  Sync var ("SYNC _" [61] 61)  |
  Fst var ("FST _" [61] 61) |
  Snd var ("SND _" [61] 61) |
  Case var var exp var exp ("CASE _ LEFT _ |> _ RIGHT _ |> _" [0,0,0,0, 61] 61) |
  Prim prim |
  App var var ("APP _ _" [61, 61] 61)
  
abbreviation bind_send_evt :: "var => var => bind" ("SEND EVT _ _" [0, 61] 61) where
  "SEND EVT x y \<equiv> Prim (Send_Evt x y)"
  
abbreviation bind_recv_evt :: "var => bind" ("RECV EVT _" [61] 61) where
  "RECV EVT x \<equiv> Prim (Recv_Evt x)"

abbreviation bind_always_evt :: "var \<Rightarrow> bind" ("ALWAYS EVT _" [61] 61) where
  "ALWAYS EVT x \<equiv> Prim (Always_Evt x)"
  
abbreviation bind_abs :: "var => var => exp => bind" ("FN _ _ . _" [0, 0, 61] 61) where
  "FN f x . e \<equiv> Prim (Abs f x e)"
  
abbreviation bind_pair :: "var => var => bind" ("\<lparr>_, _\<rparr>" [0, 0] 61) where
  "\<lparr>x, y\<rparr> \<equiv> Prim (Pair x y)"
  
abbreviation bind_inl :: "var => bind" ("LEFT _" [61] 61) where
  "LEFT x \<equiv> Prim (Left x)"
  
abbreviation bind_inr :: "var => bind" ("RIGHT _" [61] 61) where
  "RIGHT x \<equiv> Prim (Right x)"
  
(* unrestricted grammar*)

datatype u_exp =
  U_Let var  u_exp u_exp (".LET _ = _ in _" [0,0, 61] 61) |
  U_Var var ("._" [61] 61)|
  U_Abs var var u_exp (".FN _ _ .  _" [0, 0, 61] 61)|
  U_Pair u_exp u_exp (".\<lparr>_, _\<rparr>" [0, 0] 61)|
  U_Left u_exp (".LEFT _" [61] 61)|
  U_Right u_exp (".RIGHT _" [61] 61)|
  U_Send_Evt u_exp u_exp (".SEND EVT _ _" [61] 61)|
  U_Recv_Evt u_exp (".RECV EVT _" [61] 61)|
  U_Always_Evt u_exp (".ALWAYS EVT _" [61] 61)|
  U_Unit (".\<lparr>\<rparr>") |
  U_Chan (".CHAN \<lparr>\<rparr>") |
  U_Spawn u_exp (".SPAWN _" [61] 61) |
  U_Sync u_exp (".SYNC _" [61] 61) |
  U_Fst u_exp (".FST _" [61] 61) |
  U_Snd u_exp (".SND _" [61] 61) |
  U_Case u_exp var u_exp var u_exp (".CASE _ LEFT _ |> _ RIGHT _ |> _" [0,0,0,0, 61] 61) |
  U_App u_exp u_exp (".APP _ _" [61, 61] 61)
  
  
fun program_size :: "u_exp \<Rightarrow> nat" where
  "program_size (.y) = 1" |
  "program_size (.LET x2 = eb in e) = 1 + (program_size eb) + (program_size e)" |
  "program_size (.FN f x2 . e) = 1 + (program_size e)" | 
  "program_size (.\<lparr>e1, e2\<rparr>) = 1 + (program_size e1) + (program_size e2)" |
  "program_size (.LEFT e) = 1 + (program_size e)" |
  "program_size (.RIGHT e) = 1 + (program_size e)" |
  "program_size (.SEND EVT e1 e2) = 1 + (program_size e1) + (program_size e2)" |
  "program_size (.RECV EVT e) =  1 + (program_size e)" |
  "program_size (.ALWAYS EVT e) = 1 + (program_size e)" |
  "program_size (.\<lparr>\<rparr>) = 1" |
  "program_size (.CHAN \<lparr>\<rparr>) = 1" |
  "program_size (.SPAWN e) = 1 + (program_size e)" |
  "program_size (.SYNC e) = 1 + (program_size e)" |
  "program_size (.FST e) = 1 + (program_size e)" |
  "program_size (.SND e) = 1 + (program_size e)" |
  "program_size (.CASE e1 LEFT x2 |> e2 RIGHT x3 |> e3) = 1 + (program_size e1) + (program_size e2) + (program_size e3)" |
  "program_size (.APP e1 e2) = 1 + (program_size e1) + (program_size e2)"
  
  
fun rename :: "var \<Rightarrow> var \<Rightarrow> u_exp \<Rightarrow> u_exp" where
  "rename x0 x1 (.y) = (if x0 = y then .x1 else .y)" |
  "rename x0 x1 (.LET x2 = eb in e) = (.LET x2 = rename x0 x1 eb in
    (if x0 = x2 then e else (rename x0 x1 e))
  )" |
  "rename x0 x1 (.FN f x2 . e) = (.FN f x2 .
    (if x0 = f \<or> x0 = x2 then e else (rename x0 x1 e))
  )" | 
  "rename x0 x1 (.\<lparr>e1, e2\<rparr>) = .\<lparr>rename x0 x1 e1, rename x0 x1 e2\<rparr>" |
  "rename x0 x1 (.LEFT e) = .LEFT (rename x0 x1 e)" |
  "rename x0 x1 (.RIGHT e) = .RIGHT (rename x0 x1 e)" |
  "rename x0 x1 (.SEND EVT e1 e2) = .SEND EVT (rename x0 x1 e1) (rename x0 x1 e2)" |
  "rename x0 x1 (.RECV EVT e) = .RECV EVT (rename x0 x1 e)" |
  "rename x0 x1 (.ALWAYS EVT e) = .ALWAYS EVT (rename x0 x1 e)" |
  "rename x0 x1 (.\<lparr>\<rparr>) = .\<lparr>\<rparr>" |
  "rename x0 x1 (.CHAN \<lparr>\<rparr>) = .CHAN \<lparr>\<rparr>" |
  "rename x0 x1 (.SPAWN e) = .SPAWN (rename x0 x1 e)" |
  "rename x0 x1 (.SYNC e) = .SYNC (rename x0 x1 e)" |
  "rename x0 x1 (.FST e) = .FST (rename x0 x1 e)" |
  "rename x0 x1 (.SND e) = .SND (rename x0 x1 e)" |
  "rename x0 x1 (.CASE e1 LEFT x2 |> e2 RIGHT x3 |> e3) = 
    (.CASE rename x0 x1 e1 
      LEFT x2 |> (if x0 = x2 then e2 else (rename x0 x1 e2)) 
      RIGHT x3 |> (if x0 = x3 then e3 else (rename x0 x1 e3)) 
    )
  " |
  "rename x0 x1 (.APP e1 e2) = .APP (rename x0 x1 e1) (rename x0 x1 e2)"

  
theorem program_size_rename_equal[simp]: "program_size (rename x0 x1 e) = program_size e"
  by (induction e) auto
 
  
(* code from John Wickerson https://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle *)  
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (
    if n < 10 then 
      [char_of_nat (48 + n)] 
    else 
      string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))]
  )"


  
definition sym :: "nat \<Rightarrow> var" where "sym i = Var (''g'' @ (string_of_nat i))"
  
(*related normalize algorithm explained at http://matt.might.net/articles/a-normalization/ *) 
(*termination proofs explained in http://isabelle.in.tum.de/doc/functions.pdf*)
function (sequential) normalize_cont :: "nat \<Rightarrow> u_exp \<Rightarrow> (nat \<Rightarrow> var \<Rightarrow> (exp \<times> nat)) \<Rightarrow> (exp \<times> nat)" where
  "normalize_cont i (.x) k = k i x" |
  "normalize_cont i (.LET x = .xb in e) k = 
    normalize_cont i (rename x xb e) k
  " |
  "normalize_cont i (.LET x = eb in e) k = 
    normalize_cont i eb (\<lambda> i' xb . 
      normalize_cont i' (rename x xb e) k
    )
  " |
  "normalize_cont i (.FN f x . e) k =
    (let g = sym i in
    (let f' = sym (i+1) in
    (let x' = sym (i+2) in
    (let (e', i') = normalize_cont (i+3) (rename f f' (rename x x' e)) (\<lambda> ik x . (RESULT x, ik)) in
    (let (ek, i'') = (k i' g) in
      (LET g = (FN f' x' . e') in ek, i'')
    )))))
  " |
  "normalize_cont i (.\<lparr>e1, e2\<rparr>) k =
    normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (ek, i''') = (k (i''+1) (sym i'')) in
          (LET (sym i'') = \<lparr>x1, x2\<rparr> in ek, i''')
        )
      )
    )
  " |
  "normalize_cont i (.LEFT e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = LEFT xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.RIGHT e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = RIGHT xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.SEND EVT e1 e2) k =
   normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (ek, i''') = (k (i''+1) (sym i'')) in
          (LET (sym i'') = SEND EVT x1 x2 in ek, i''')
        )
      )
    )
  " |
  "normalize_cont i (.RECV EVT e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = RECV EVT xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.ALWAYS EVT e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = ALWAYS EVT xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.\<lparr>\<rparr>) k =
    (let (ek, i') = k (i+1) (sym i) in
      (LET (sym i) = \<lparr>\<rparr> in ek, i')
    )
  "|
  "normalize_cont i (.CHAN \<lparr>\<rparr>) k =
    (let (ek, i') = k (i+1) (sym i) in
      (LET (sym i) = CHAN \<lparr>\<rparr> in ek, i')
    )
  "|
  "normalize_cont i (.SPAWN e) k = 
    (let (e', i') = normalize_cont (i+1) e (\<lambda> ik x . (RESULT x, ik)) in
    (let (ek, i'') = k i' (sym i) in
      (LET (sym i) = SPAWN e' in ek, i'')
    ))
  " |
  "normalize_cont i (.SYNC e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = SYNC xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.FST e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = FST xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.SND e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (LET (sym i') = SND xb in ek, i'')
      )
    )
  " |
  "normalize_cont i (.CASE e LEFT xl |> el RIGHT xr |> er) k =
    normalize_cont i e (\<lambda> i' x .
      (let xl' = sym (i'+1) in
      (let (el', i'') = normalize_cont (i'+2) (rename xl xl' el) (\<lambda> il x . (RESULT x, il)) in
      (let xr' = sym i'' in  
      (let (er', i''') = normalize_cont (i''+1) (rename xr xr' er) (\<lambda> ir x . (RESULT x, ir))  in
      (let (ek, i'''') = k i''' (sym i') in
        (  
          LET (sym i') = 
            CASE x 
            LEFT xl' |> el'
            RIGHT xr' |> er' 
          in ek, 
          i''''
        )
      )))))
    )
  " |
  "normalize_cont i (.APP e1 e2) k =
    normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (e''', i''') = (k (i''+1) (sym i'')) in
          (LET (sym i'') = APP x1 x2 in e''', i''')
        )
      )
    )
  "
by pat_completeness auto
termination by (relation "measure (\<lambda>(i, e, k). program_size e)") auto

    
definition normalize :: "u_exp \<Rightarrow> exp" where
  "normalize e = fst (normalize_cont 100 e (\<lambda> i x . (RESULT x, i)))"

end

