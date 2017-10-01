theory Tree_Demo
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

lemma "Tip ~= Node l x r"
apply auto
done

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

value "mirror(Node (Node Tip a Tip) b t)"

lemma mirror_mirros[simp]: "mirror(mirror t) = t"
apply(induction t)
apply auto
done

text{* An example of fun: beyond one equation per constructor *}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

value "sep a [x,y,z]"

end
