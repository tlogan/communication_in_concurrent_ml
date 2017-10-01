theory Isar_Induction_Demo
imports Main
begin

section{*Case distinction and induction*}

subsection{*Case distinction*}

text{* Explicit: *}

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []" thus ?thesis by simp
next
  fix y ys assume "xs = y#ys"
  thus ?thesis by simp
qed

text{* Implicit: *}

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
print_cases
  case Nil
thm Nil
  thus ?thesis by simp
next
  case (Cons y ys)
thm Cons
  thus ?thesis by simp
qed


subsection{*Structural induction for nat*}

text{* Explicit: *}

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text{* Implicit: *}

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
print_cases
  case 0
  show ?case by simp
next
  case (Suc n)
thm Suc
  thus ?case by simp
qed

text{* After the induction or cases step,
 the PG menu item Isabelle/Show me/cases displays
 the different cases. *}

text{* Induction with @{text "\<Longrightarrow>"} *}

lemma split_list: "x : set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induction xs)
  case Nil thus ?case by simp
next
print_cases
  case (Cons a xs)
thm Cons.IH --"Induction hypothesis"
thm Cons.prems --"Premises of the step case"
thm Cons
  from Cons.prems have "x = a \<or> x : set xs" by simp
  thus ?case
  proof
    assume "x = a"
    hence "a#xs = [] @ x # xs" by simp
    thus ?thesis by blast
  next
    assume "x : set xs"
    then obtain ys zs where "xs = ys @ x # zs" using Cons.IH by auto
    hence "a#xs = (a#ys) @ x # zs" by simp
    thus ?thesis by blast
  qed
qed


subsection{*Rule induction*}


inductive ev :: "nat => bool" where
ev0:  "ev 0" |
evSS:  "ev n \<Longrightarrow> ev(Suc(Suc n))"

declare ev.intros [simp]


lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
proof (induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case evSS thus ?case by arith
qed


lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
proof (induction rule: ev.induct)
  case ev0 show ?case by simp
next
  case (evSS m)
thm evSS
thm evSS.IH
thm evSS.hyps
  then obtain k where "m = 2*k" by blast
  hence "Suc(Suc m) = 2*(k+1)" by simp
  thus "\<exists>k. Suc(Suc m) = 2*k" by blast
qed


subsection{*Inductive definition of the reflexive transitive closure *}

consts step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<rightarrow>" 55)

inductive steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<rightarrow>*" 55) where
refl: "x \<rightarrow>* x" |
step: "\<lbrakk> x \<rightarrow> y; y \<rightarrow>* z \<rbrakk> \<Longrightarrow> x \<rightarrow>* z"

declare refl[simp, intro]

text{* Explicit and by hand: *}

lemma "x \<rightarrow>* y  \<Longrightarrow>  y \<rightarrow>* z \<Longrightarrow> x \<rightarrow>* z"
proof(induction rule: steps.induct)
  fix x assume "x \<rightarrow>* z"
  thus "x \<rightarrow>* z" . --"by assumption"
next
  fix x' x y :: 'a
  assume "x' \<rightarrow> x" and "x \<rightarrow>* y"
  assume IH: "y \<rightarrow>* z \<Longrightarrow> x \<rightarrow>* z"
  assume "y \<rightarrow>* z"
  show "x' \<rightarrow>* z" by(rule step[OF `x' \<rightarrow> x` IH[OF `y\<rightarrow>*z`]])
qed

text{* Implicit and automatic: *}

lemma "x \<rightarrow>* y  \<Longrightarrow>  y \<rightarrow>* z \<Longrightarrow> x \<rightarrow>* z"
proof(induction rule: steps.induct)
  case refl thus ?case .
next
  case (step x' x y)
  --"x' x y not used in proof text, just for demo"
thm step
thm step.IH
thm step.hyps
thm step.prems
  show ?case
    by (metis step.hyps(1) step.IH step.prems steps.step)
qed


subsection{*Rule inversion*}


lemma assumes "ev n" shows "ev(n - 2)"
proof-
  from `ev n` show "ev(n - 2)"
  proof cases
    case ev0
thm ev0
    then show ?thesis by simp
  next
    case (evSS k)
thm evSS
    then show ?thesis by simp
  qed
qed


text{* Impossible cases are proved automatically: *}

lemma "\<not> ev(Suc 0)"
proof
  assume "ev(Suc 0)"
  then show False
  proof cases
  qed
qed


end
