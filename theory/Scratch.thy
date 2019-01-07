theory Scratch
  imports Main
begin

theorem A: "P1 \<longrightarrow> Q" sorry
theorem B: "P2 \<longrightarrow> Q" sorry

lemma "P1 \<or> P2 \<longrightarrow> Q"
apply (rule impI)
apply (erule disjE)
apply (insert A[of P1 Q])[1]
apply (rotate_tac)
apply (erule mp)
apply assumption

apply (insert B[of P2 Q])[1]
apply (erule mp)
apply assumption
done


datatype nat = Z | S nat
inductive lte :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  eq: "lte n n"
| lt: "lte n1 n2 \<Longrightarrow> lte n1 (S n2)"


datatype 'a list = Nil | Cons 'a "'a list"

inductive sorted :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  nil: "sorted r Nil"
| uni: "sorted r (Cons x Nil)"
| cons: "r x y \<Longrightarrow> sorted r (Cons y ys) \<Longrightarrow> sorted r (Cons x (Cons y ys))"

theorem "sorted lte (Cons Z (Cons (S Z) (Cons (S Z) (Cons (S (S (S Z))) Nil))))"
apply (rule cons)
apply (rule lt)
apply (rule eq)
apply (rule cons)
apply (rule eq)
apply (rule cons)
apply (rule lt)
apply (rule lt)
apply (rule eq)
apply (rule uni)