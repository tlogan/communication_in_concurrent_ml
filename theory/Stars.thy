theory Stars
  imports "~~/src/HOL/IMP/Star"
begin

inductive star_left :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for R where
 refl: "star_left R z z" |
 step: "star_left R x y \<Longrightarrow> R y z \<Longrightarrow> star_left R x z"

lemma star_left_trans: "
  star_left r y z \<Longrightarrow> star_left r x y \<Longrightarrow> star_left r x z
"
proof(induction rule: star_left.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star_left.step)
qed

lemma star_left_step1[simp, intro]: "r x y \<Longrightarrow> star_left r x y"
by(metis star_left.refl star_left.step)

theorem star_implies_star_left: "star R x z \<Longrightarrow> star_left R x z"
 apply (erule star.induct, rule star_left.refl)
 apply (meson star_left_step1 star_left_trans)
done

theorem star_left_implies_star: "star_left R x z \<Longrightarrow> star R x z"
 apply (erule star_left.induct, rule star.refl)
 apply (meson star_step1 star_trans)
done

end
