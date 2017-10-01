theory Auto_Proof_Demo
imports Main
begin

section{* Logic and sets *}

lemma "ALL x. EX y. x=y"
by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

text{* Note the bounded quantification notation: *}

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us:A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce


text{*
 Most simple proofs in FOL and set theory are automatic.
 Example: if T is total, A is antisymmetric
 and T is a subset of A, then A is a subset of T.
*}

lemma AT:
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast


section{* Sledgehammer *}

lemma "R^* \<subseteq> (R \<union> S)^*"
oops

(* Find a suitable P and try sledgehammer: *)

lemma "a # xs = ys @ [a] \<Longrightarrow> P"
oops


section{* Arithmetic *}

lemma "\<forall> (k::nat) > 7. \<exists> i j. k = 3*i + 5*j"
by arith

end
