theory Syntax
  imports Main
begin
  
datatype name = Var string

datatype tm = 
  Bind name complex tm 
| Rslt name

and complex = 
  Unt 
| MkChn 
| Atom atom 
| Spwn tm 
| Sync name 
| Fst name 
| Snd name 
| Case name name tm name tm 
| App name name 

and atom = 
  SendEvt name name 
| RecvEvt name 
| Pair name name 
| Lft name 
| Rht name 
| Fun name name tm

fun freeVarsAtom :: "atom \<Rightarrow> name set"
and freeVarsComplex :: "complex \<Rightarrow> name set"
and freeVarsTerm :: "tm \<Rightarrow> name set" where
  "freeVarsAtom (SendEvt x_ch x_m) = {x_ch, x_m}"
| "freeVarsAtom (RecvEvt x_ch) = {x_ch}"
| "freeVarsAtom (Pair x1 x2) = {x1, x2}"
| "freeVarsAtom (Lft x) = {x}"
| "freeVarsAtom (Rht x) = {x}"
| "freeVarsAtom (Fun x_f x_p e_b) = freeVarsTerm e_b - {x_f, x_p}"

| "freeVarsComplex Unt = {}"
| "freeVarsComplex MkChn = {}"
| "freeVarsComplex (Atom atom) = freeVarsAtom atom"
| "freeVarsComplex (Spwn e) = freeVarsTerm e"
| "freeVarsComplex (Sync x) = {x}"
| "freeVarsComplex (Fst x) = {x}"
| "freeVarsComplex (Snd x) = {x}"
| "freeVarsComplex (Case x_sum x_l e_l x_r e_r) = 
    {x_sum} \<union> freeVarsTerm e_l \<union> freeVarsTerm e_r - {x_l, x_r}"
| "freeVarsComplex (App x_f x_a) = {x_f, x_a}"

| "freeVarsTerm (Bind x b e) = freeVarsComplex b \<union> freeVarsTerm e - {x}" 
| "freeVarsTerm (Rslt x) = {x}"

datatype qtm =
  QBind name qtm qtm 
| QVar name 
| QUnt 
| QMkChn 
| QSendEvt qtm qtm 
| QRecvEvt qtm 
| QPair qtm qtm 
| QLft qtm 
| QRht qtm 
| QFun name name qtm 
| QSpwn qtm | QSync qtm 
| QFst qtm 
| QSnd qtm 
| QCase qtm name qtm name qtm 
| QApp qtm qtm
  
  
fun program_size :: "qtm \<Rightarrow> nat" where
  "program_size (QVar y) = 1" 
| "program_size (QBind x2 eb e) = 1 + (program_size eb) + (program_size e)" 
| "program_size (QUnt) = 1" 
| "program_size (QMkChn) = 1" 
| "program_size (QSendEvt e1 e2) = 1 + (program_size e1) + (program_size e2)" 
| "program_size (QRecvEvt e) =  1 + (program_size e)" 
| "program_size (QPair e1 e2) = 1 + (program_size e1) + (program_size e2)" 
| "program_size (QLft e) = 1 + (program_size e)" 
| "program_size (QRht e) = 1 + (program_size e)" 
| "program_size (QFun f x2 e) = 1 + (program_size e)"
| "program_size (QSpwn e) = 1 + (program_size e)" 
| "program_size (QSync e) = 1 + (program_size e)" 
| "program_size (QFst e) = 1 + (program_size e)" 
| "program_size (QSnd e) = 1 + (program_size e)" 
| "program_size (QCase e1 x2 e2 x3 e3) = 1 + (program_size e1) + (program_size e2) + (program_size e3)" 
| "program_size (QApp e1 e2) = 1 + (program_size e1) + (program_size e2)"
  
  
fun rename :: "name \<Rightarrow> name \<Rightarrow> qtm \<Rightarrow> qtm" where
  "rename x0 x1 (QVar y) = (if x0 = y then (QVar x1) else (QVar y))" 
| "rename x0 x1 (QBind x2 eb e) = (QBind x2 (rename x0 x1 eb)
    (if x0 = x2 then e else (rename x0 x1 e)))" 
| "rename x0 x1 (QUnt) = QUnt" 
| "rename x0 x1 (QMkChn) = QMkChn" 
| "rename x0 x1 (QSendEvt e1 e2) = QSendEvt (rename x0 x1 e1) (rename x0 x1 e2)" 
| "rename x0 x1 (QRecvEvt e) = QRecvEvt (rename x0 x1 e)" 
| "rename x0 x1 (QPair e1 e2) = QPair (rename x0 x1 e1) (rename x0 x1 e2)" 
| "rename x0 x1 (QLft e) = QLft (rename x0 x1 e)" 
| "rename x0 x1 (QRht e) = QRht (rename x0 x1 e)" 
| "rename x0 x1 (QFun f x2 e) = QFun f x2 
    (if x0 = f \<or> x0 = x2 then e else (rename x0 x1 e))"
| "rename x0 x1 (QSpwn e) = QSpwn (rename x0 x1 e)" 
| "rename x0 x1 (QSync e) = QSync (rename x0 x1 e)" 
| "rename x0 x1 (QFst e) = QFst (rename x0 x1 e)" 
| "rename x0 x1 (QSnd e) = QSnd (rename x0 x1 e)" 
| "rename x0 x1 (QCase e1 x2 e2 x3 e3) = 
    (QCase (rename x0 x1 e1) 
      x2 (if x0 = x2 then e2 else (rename x0 x1 e2)) 
      x3 (if x0 = x3 then e3 else (rename x0 x1 e3)))" 
| "rename x0 x1 (QApp e1 e2) = QApp (rename x0 x1 e1) (rename x0 x1 e2)"

  
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
  
definition sym :: "nat \<Rightarrow> name" where "sym i = Var (''g'' @ (string_of_nat i))"
  
(*related normalize algorithm tmlained at http://matt.might.net/articles/a-normalization/ *) 
(*tmination proofs tmlained in http://isabelle.in.tum.de/doc/functions.pdf*)
function (sequential) normalize_cont :: "nat \<Rightarrow> qtm \<Rightarrow> (nat \<Rightarrow> name \<Rightarrow> (tm \<times> nat)) \<Rightarrow> (tm \<times> nat)" where
  "normalize_cont i (QVar x) k = k i x" 
| "normalize_cont i (QBind x (QVar xb) e) k = 
    normalize_cont i (rename x xb e) k" 
| "normalize_cont i (QBind x eb e) k = 
    normalize_cont i eb (\<lambda> i' xb . normalize_cont i' (rename x xb e) k)" 
| "normalize_cont i (QUnt) k =
    (let (ek, i') = k (i+1) (sym i) in
      (Bind (sym i) Unt ek, i'))"
| "normalize_cont i QMkChn k =
    (let (ek, i') = k (i+1) (sym i) in
      (Bind (sym i) MkChn ek, i'))" 
|  "normalize_cont i (QSendEvt e1 e2) k =
   normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (ek, i''') = (k (i''+1) (sym i'')) in
          (Bind (sym i'') (Atom (SendEvt x1 x2)) ek, i'''))))" 
|  "normalize_cont i (QRecvEvt e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Bind (sym i') (Atom (RecvEvt xb)) ek, i'')))" 
|
  "normalize_cont i (QPair e1 e2) k =
    normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (ek, i''') = (k (i''+1) (sym i'')) in
          (Bind (sym i'') (Atom (Pair x1 x2)) ek, i'''))))" 
|  "normalize_cont i (QLft e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Bind (sym i') (Atom (Lft xb)) ek, i'')))" 
|  "normalize_cont i (QRht e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Bind (sym i') (Atom (Rht xb)) ek, i'')))" 
|  "normalize_cont i (QFun f x e) k =
    (let g = sym i in
    (let f' = sym (i+1) in
    (let x' = sym (i+2) in
    (let (e', i') = normalize_cont (i+3) (rename f f' (rename x x' e)) (\<lambda> ik x . (Rslt x, ik)) in
    (let (ek, i'') = (k i' g) in
      (Bind g (Atom (Fun f' x' e')) ek, i''))))))" 
|  "normalize_cont i (QSpwn e) k = 
    (let (e', i') = normalize_cont (i+1) e (\<lambda> ik x . (Rslt x, ik)) in
    (let (ek, i'') = k i' (sym i) in
      (Bind (sym i) (Spwn e') ek, i'')))" 
|  "normalize_cont i (QSync e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Bind (sym i') (Sync xb) ek, i'')))" 
| "normalize_cont i (QFst e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Bind (sym i') (Fst xb) ek, i'')))" 
| "normalize_cont i (QSnd e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Bind (sym i') (Snd xb) ek, i'')))" 
| "normalize_cont i (QCase e xl el xr er) k =
    normalize_cont i e (\<lambda> i' x .
      (let xl' = sym (i'+1) in
      (let (el', i'') = normalize_cont (i'+2) (rename xl xl' el) (\<lambda> il x . (Rslt x, il)) in
      (let xr' = sym i'' in  
      (let (er', i''') = normalize_cont (i''+1) (rename xr xr' er) (\<lambda> ir x . (Rslt x, ir))  in
      (let (ek, i'''') = k i''' (sym i') in
        (Bind (sym i')
          (Case x xl' el' xr' er') ek, i'''')))))))" 
| "normalize_cont i (QApp e1 e2) k =
    normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (e''', i''') = (k (i''+1) (sym i'')) in
          (Bind (sym i'') (App x1 x2) e''', i'''))))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(i, e, k). program_size e)") auto

    
definition normalize :: "qtm \<Rightarrow> tm" where
  "normalize e = fst (normalize_cont 100 e (\<lambda> i x . (Rslt x, i)))"

end
