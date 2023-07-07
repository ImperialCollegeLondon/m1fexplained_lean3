import data.real.basic
import analysis.normed.field.unit_ball

open_locale topology big_operators nnreal ennreal uniformity pointwise

/-
Which of the following sets S have an upper bound and which have a
lower bound? In the cases where these exist, state what the least upper
bounds and greatest lower bounds are.
(i) S = {−1, 3, 7, −2}.
(ii) S = {x | x ∈ ℝ and |x − 3| < |x + 7|}.
(iii) S = {x | x ∈ ℝ and x³ − 3x < 0}.
(iv) S = {x | x ∈ ℝ and x² = a² + b² for some a, b ∈ ℕ}.
-/

def Si : set ℝ := {-1, 3, 7, -2}

-- Si is bounded above.
lemma part_a_ub : ∃ z : ℝ, z ∈ upper_bounds Si :=
begin
  use 7,
  rw upper_bounds,
  intro t,
  intro h,
  cases h,
  rw h,
  norm_num,
  cases h,
  rw h,
  norm_num,
  cases h,
  rw h,
  simp at h,
  rw h,
  norm_num,
end

-- if you proved there was an upper bound, then change 37 to the 
-- right answer and prove it's a least upper bound!
-- If you proved there was no upper bound, just comment out
-- this part.
lemma part_a_lub : is_lub Si 37 :=
begin
  sorry
end

-- Now the same for lower bounds.
lemma part_a_lb : ∃ z : ℝ, z ∈ lower_bounds Si :=
begin
  sorry
end

-- if you proved there *was* a lower bound,
-- and prove it's a least upper bound!
-- If not, then delete this part.
lemma part_a_glb : is_glb Si 37 :=
begin
  sorry
end

def Sii : set ℝ := {x | ‖x - 3‖ < ‖x + 7‖}.

-- If you think Sii is bounded above, prove this. If you
-- think it's not, then *disprove* it by putting `¬` in front of it.
lemma part_b_ub : ∃ z : ℝ, z ∈ upper_bounds Sii :=
begin
  sorry
end

-- if you proved there was an upper bound, then change 37 to the 
-- right answer and prove it's a least upper bound!
-- etc etc
lemma part_b_lub : is_lub Sii 37 :=
begin
  sorry
end

lemma part_b_lb : ∃ z : ℝ, z ∈ lower_bounds Sii :=
begin
  sorry
end

lemma part_b_glb : is_glb Sii 37 :=
begin
  sorry
end

def Siii : set ℝ := {x | x^3 - 3*x < 0}

lemma part_c_ub : ∃ z : ℝ, z ∈ upper_bounds Siii :=
begin
  sorry
end

lemma part_c_lub : is_lub Siii 37 :=
begin
  sorry
end

lemma part_c_lb : ∃ z : ℝ, z ∈ lower_bounds Siii :=
begin
  sorry
end

lemma part_c_glb : is_glb Siii 37 :=
begin
  sorry
end

def Siv : set ℝ := {x | ∃ a b : pnat, x = a^2 + b^2}.

lemma part_d_ub : ∃ z : ℝ, z ∈ upper_bounds Siv :=
begin
  sorry
end

lemma part_d_lub : is_lub Siv 37 :=
begin
  sorry
end

lemma part_d_lb : ∃ z : ℝ, z ∈ lower_bounds Siv :=
begin
  sorry
end

lemma part_d_glb : is_glb Siv 37 :=
begin
  sorry
end