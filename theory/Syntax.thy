theory Syntax
  imports Main
begin
  
datatype var = Var string

datatype 
  exp = 
    Let var bound_exp exp |
    Rslt var and 

  bound_exp = 
    Unt | MkChn | Prim prim | Spwn exp |
    Sync var | Fst var | Snd var |
    Case var var exp var exp | App var var and 

  prim = 
    SendEvt var var | RecvEvt var | Pair var var |
    Lft var | Rght var | Abs var var exp

datatype 
  qexp =
    QLet var qexp qexp | QVar var | QUnt |
    QMkChn | QSendEvt qexp qexp | QRecvEvt qexp |
    QPair qexp qexp | QLft qexp | QRght qexp |
    QAbs var var qexp | QSpwn qexp | QSync qexp |
    QFst qexp | QSnd qexp |
    QCase qexp var qexp var qexp | QApp qexp qexp
  
  
fun program_size :: "qexp \<Rightarrow> nat" where
  "program_size (QVar y) = 1" |
  "program_size (QLet x2 eb e) = 1 + (program_size eb) + (program_size e)" |
  "program_size (QUnt) = 1" |
  "program_size (QMkChn) = 1" |
  "program_size (QSendEvt e1 e2) = 1 + (program_size e1) + (program_size e2)" |
  "program_size (QRecvEvt e) =  1 + (program_size e)" |
  "program_size (QPair e1 e2) = 1 + (program_size e1) + (program_size e2)" |
  "program_size (QLft e) = 1 + (program_size e)" |
  "program_size (QRght e) = 1 + (program_size e)" |
  "program_size (QAbs f x2 e) = 1 + (program_size e)" | 
  "program_size (QSpwn e) = 1 + (program_size e)" |
  "program_size (QSync e) = 1 + (program_size e)" |
  "program_size (QFst e) = 1 + (program_size e)" |
  "program_size (QSnd e) = 1 + (program_size e)" |
  "program_size (QCase e1 x2 e2 x3 e3) = 1 + (program_size e1) + (program_size e2) + (program_size e3)" |
  "program_size (QApp e1 e2) = 1 + (program_size e1) + (program_size e2)"
  
  
fun rename :: "var \<Rightarrow> var \<Rightarrow> qexp \<Rightarrow> qexp" where
  "rename x0 x1 (QVar y) = (if x0 = y then (QVar x1) else (QVar y))" |
  "rename x0 x1 (QLet x2 eb e) = (QLet x2 (rename x0 x1 eb)
    (if x0 = x2 then e else (rename x0 x1 e)))" |
  "rename x0 x1 (QUnt) = QUnt" |
  "rename x0 x1 (QMkChn) = QMkChn" |
  "rename x0 x1 (QSendEvt e1 e2) = QSendEvt (rename x0 x1 e1) (rename x0 x1 e2)" |
  "rename x0 x1 (QRecvEvt e) = QRecvEvt (rename x0 x1 e)" |
  "rename x0 x1 (QPair e1 e2) = QPair (rename x0 x1 e1) (rename x0 x1 e2)" |
  "rename x0 x1 (QLft e) = QLft (rename x0 x1 e)" |
  "rename x0 x1 (QRght e) = QRght (rename x0 x1 e)" |
  "rename x0 x1 (QAbs f x2 e) = QAbs f x2 
    (if x0 = f \<or> x0 = x2 then e else (rename x0 x1 e))" | 
  "rename x0 x1 (QSpwn e) = QSpwn (rename x0 x1 e)" |
  "rename x0 x1 (QSync e) = QSync (rename x0 x1 e)" |
  "rename x0 x1 (QFst e) = QFst (rename x0 x1 e)" |
  "rename x0 x1 (QSnd e) = QSnd (rename x0 x1 e)" |
  "rename x0 x1 (QCase e1 x2 e2 x3 e3) = 
    (QCase (rename x0 x1 e1) 
      x2 (if x0 = x2 then e2 else (rename x0 x1 e2)) 
      x3 (if x0 = x3 then e3 else (rename x0 x1 e3)))" |
  "rename x0 x1 (QApp e1 e2) = QApp (rename x0 x1 e1) (rename x0 x1 e2)"

  
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
function (sequential) normalize_cont :: "nat \<Rightarrow> qexp \<Rightarrow> (nat \<Rightarrow> var \<Rightarrow> (exp \<times> nat)) \<Rightarrow> (exp \<times> nat)" where
  "normalize_cont i (QVar x) k = k i x" |
  "normalize_cont i (QLet x (QVar xb) e) k = 
    normalize_cont i (rename x xb e) k" |
  "normalize_cont i (QLet x eb e) k = 
    normalize_cont i eb (\<lambda> i' xb . normalize_cont i' (rename x xb e) k)" |
  "normalize_cont i (QUnt) k =
    (let (ek, i') = k (i+1) (sym i) in
      (Let (sym i) Unt ek, i'))"|
  "normalize_cont i QMkChn k =
    (let (ek, i') = k (i+1) (sym i) in
      (Let (sym i) MkChn ek, i'))" |

  "normalize_cont i (QSendEvt e1 e2) k =
   normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (ek, i''') = (k (i''+1) (sym i'')) in
          (Let (sym i'') (Prim (SendEvt x1 x2)) ek, i'''))))" |

  "normalize_cont i (QRecvEvt e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Let (sym i') (Prim (RecvEvt xb)) ek, i'')))" |


  "normalize_cont i (QPair e1 e2) k =
    normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (ek, i''') = (k (i''+1) (sym i'')) in
          (Let (sym i'') (Prim (Pair x1 x2)) ek, i'''))))" |

  "normalize_cont i (QLft e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Let (sym i') (Prim (Lft xb)) ek, i'')))" |

  "normalize_cont i (QRght e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Let (sym i') (Prim (Rght xb)) ek, i'')))" |

  "normalize_cont i (QAbs f x e) k =
    (let g = sym i in
    (let f' = sym (i+1) in
    (let x' = sym (i+2) in
    (let (e', i') = normalize_cont (i+3) (rename f f' (rename x x' e)) (\<lambda> ik x . (Rslt x, ik)) in
    (let (ek, i'') = (k i' g) in
      (Let g (Prim (Abs f' x' e')) ek, i''))))))" |

  "normalize_cont i (QSpwn e) k = 
    (let (e', i') = normalize_cont (i+1) e (\<lambda> ik x . (Rslt x, ik)) in
    (let (ek, i'') = k i' (sym i) in
      (Let (sym i) (Spwn e') ek, i'')))" |

  "normalize_cont i (QSync e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Let (sym i') (Sync xb) ek, i'')))" |
  "normalize_cont i (QFst e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Let (sym i') (Fst xb) ek, i'')))" |
  "normalize_cont i (QSnd e) k =
    normalize_cont i e (\<lambda> i' xb .
      (let (ek, i'') = (k (i'+1) (sym i')) in
        (Let (sym i') (Snd xb) ek, i'')))" |
  "normalize_cont i (QCase e xl el xr er) k =
    normalize_cont i e (\<lambda> i' x .
      (let xl' = sym (i'+1) in
      (let (el', i'') = normalize_cont (i'+2) (rename xl xl' el) (\<lambda> il x . (Rslt x, il)) in
      (let xr' = sym i'' in  
      (let (er', i''') = normalize_cont (i''+1) (rename xr xr' er) (\<lambda> ir x . (Rslt x, ir))  in
      (let (ek, i'''') = k i''' (sym i') in
        (Let (sym i')
          (Case x xl' el' xr' er') ek, i'''')))))))" |
  "normalize_cont i (QApp e1 e2) k =
    normalize_cont i e1 (\<lambda> i' x1 .
      normalize_cont i' e2 (\<lambda> i'' x2 .
        (let (e''', i''') = (k (i''+1) (sym i'')) in
          (Let (sym i'') (App x1 x2) e''', i'''))))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(i, e, k). program_size e)") auto

    
definition normalize :: "qexp \<Rightarrow> exp" where
  "normalize e = fst (normalize_cont 100 e (\<lambda> i x . (Rslt x, i)))"

end