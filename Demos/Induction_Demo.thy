theory Induction_Demo
imports Main
begin

(* HINT FOR ONLINE DEMO
   Start your first proof attempt with
   itrev xs [] = rev xs
   then generalize by introducing ys, and finally quantify over ys.
   Each generalization should be motivated by the previous failed
   proof attempt.
*)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
apply(induction xs arbitrary: ys)
apply(auto)
done


subsection{* Computation Induction *}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"
apply(induction a xs rule: sep.induct)
apply auto
done

end
