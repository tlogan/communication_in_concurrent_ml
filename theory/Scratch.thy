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