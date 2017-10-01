theory Inductive_Demo
imports Main
begin

subsection{*Inductive definition of the even numbers*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS
thm ev.intros

text{* Using the introduction rules: *}
lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

thm evSS[OF evSS[OF ev0]]

text{* A recursive definition of evenness: *}
fun even :: "nat \<Rightarrow> bool" where
"even 0 = True" |
"even (Suc 0) = False" |
"even (Suc(Suc n)) = even n"

text{*A simple example of rule induction: *}
lemma "ev n \<Longrightarrow> even n"
apply(induction rule: ev.induct)
 apply(simp)
apply(simp)
done

text{* An induction on the computation of even: *}
lemma "even n \<Longrightarrow> ev n"
apply(induction n rule: even.induct)
  apply (simp add: ev0)
 apply simp
apply(simp add: evSS)
done

text{* No problem with termination because the premises are always smaller
than the conclusion: *}
declare ev.intros[simp,intro]

text{* A shorter proof: *}
lemma "even n \<Longrightarrow> ev n"
apply(induction n rule: even.induct)
apply(simp_all)
done

text{* The power of arith: *}
lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
apply(induction rule: ev.induct)
 apply(simp)
apply arith
done


subsection{*Inductive definition of the reflexive transitive closure *}

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
apply(rename_tac u x y)
apply(metis step)
done

end
