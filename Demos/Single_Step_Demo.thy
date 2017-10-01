theory Single_Step_Demo
imports Main
begin

text{* "thm" is a command that displays one or more named theorems: *}
thm conjI impI iffI notI

text{* Instantiation of theorems: "of" *}

text{* Positional: *}
thm conjI[of "A" "B"]
thm conjI[of "A"]
thm conjI[of _ "B"]

text{* By name: *}
thm conjI[where ?Q = "B"]

text{* Composition of theorems: OF *}

thm refl[of "a"]
thm conjI[OF refl[of "a"] refl[of "b"]]
thm conjI[OF refl[of "a"]]
thm conjI[OF _ refl[of "b"]]


text{* A simple backward proof: *}
lemma "\<lbrakk> A; B \<rbrakk> \<Longrightarrow> A \<and> B"
apply(rule conjI)
apply assumption
apply assumption
done

text{* Teaching blast new intro rules: *}

thm le_trans

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d \<rbrakk> \<Longrightarrow> a \<le> d"
by(blast intro: le_trans)

end
