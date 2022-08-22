import data.real.basic
import analysis.normed.field.unit_ball
import data.real.sqrt

open_locale topological_space big_operators nnreal ennreal uniformity pointwise

/-
Which of the following sets S have an upper bound and which have a
lower bound? In the cases where these exist, state what the least upper
bounds and greatest lower bounds are.
(i) S = {−1, 3, 7, −2}.
(ii) S = {x | x ∈ ℝ and |x − 3| < |x + 7|}.
(iii) S = {x | x ∈ ℝ and  x³ −3x < 0}.
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

-- 7 is the least upper bound.
lemma part_a_lub : is_lub Si 7 :=
begin
  rw is_lub,
  rw is_least,
  split,
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
  rw lower_bounds,
  intro n,
  intro h,
  rw upper_bounds at h,
  simp at h,
  apply h,
  unfold Si,
  simp,
end

-- Si is bounded below.
lemma part_a_lb : ∃ z : ℝ, z ∈ lower_bounds Si :=
begin
  use -2,
  rw lower_bounds,
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
  norm_num,
  simp at h,
  rw h,
end

-- -2 is the greatest lower bound.
lemma part_a_glb : is_glb Si (-2) :=
begin
  rw is_glb,
  rw is_greatest,
  split,
  rw lower_bounds,
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
  norm_num,
  simp at h,
  rw h,
  rw upper_bounds,
  intro n,
  intro h,
  rw lower_bounds at h,
  simp at h,
  apply h,
  unfold Si,
  simp,
end

def Sii : set ℝ := {x | ∥x - 3∥ < ∥x + 7∥}.

-- Sii is not bounded above.
lemma part_b_ub : ¬ ∃ z : ℝ, z ∈ upper_bounds Sii :=
begin
  rw not_exists,
  intro n,
  rw upper_bounds,
  simp,
  by_cases h: n ≤ 3,
  use 4,
  split,
  unfold Sii,
  simp,
  norm_num,
  rw abs_of_pos,
  norm_num,
  norm_num,
  linarith,
  use n+1,
  split,
  unfold Sii,
  simp,
  rw abs_of_pos,
  rw abs_of_pos,
  linarith,
  linarith,
  linarith,
  linarith,
end

-- if you proved there was an upper bound, then change 37 to the 
-- right answer and prove it's a least upper bound!
-- etc etc

-- Si is bounded below.
lemma part_b_lb : ∃ z : ℝ, z ∈ lower_bounds Sii :=
begin
  use -2,
  rw lower_bounds,
  simp,
  intro t,
  intro h,
  unfold Sii at h,
  simp at h,
  by_cases h1: t < -7,
  rw abs_of_neg at h,
  rw abs_of_neg at h,
  linarith,
  linarith,
  linarith,
  by_cases h2: t ≥ 3,
  linarith,
  rw abs_of_neg at h,
  rw abs_of_nonneg at h,
  linarith,
  push_neg at h1,
  linarith,
  linarith,
end

-- -2 is the greatest lower bound.
lemma part_b_glb : is_glb Sii (-2) :=
begin
  rw is_glb,
  rw is_greatest,
  split,
  rw lower_bounds,
  simp,
  intro t,
  intro h,
  unfold Sii at h,
  simp at h,
  by_cases h1: t < -7,
  rw abs_of_neg at h,
  rw abs_of_neg at h,
  linarith,
  linarith,
  linarith,
  by_cases h2: t ≥ 3,
  linarith,
  rw abs_of_neg at h,
  rw abs_of_nonneg at h,
  linarith,
  push_neg at h1,
  linarith,
  linarith,
  rw upper_bounds,
  simp,
  intro n,
  intro h,
  rw lower_bounds at h,
  simp at h,
  unfold Sii at h,
  by_contra h1,
  push_neg at h1,
  by_cases p: n≤ (-1),
  let t:= n+2,
  have ht: -2+t = n,
    simp [t],
  let k:= -2 + (t/2),
  have l1: n ≤ k,
  apply h,
  simp [k],
  rw abs_of_neg,
  rw abs_of_pos,
  linarith,
  linarith,
  linarith,
  simp [k] at l1,
  linarith,
  push_neg at p,
  have l: n≤ (-1),
  apply h,
  simp,
  rw abs_of_neg,
  rw abs_of_pos,
  linarith,
  linarith,
  linarith,
  linarith,
end

def Siii : set ℝ := {x | x^3 - 3*x < 0}

-- Siii is bounded above.
lemma part_c_ub : ∃ z : ℝ, z ∈ upper_bounds Siii :=
begin
  use (real.sqrt 3),
  rw upper_bounds,
  simp,
  intro n,
  intro h,
  unfold Siii at h,
  simp at h,
  by_cases p: 0 < n,
  have l:= div_lt_div_of_lt p h,
  rw mul_div_assoc at l,
  rw div_self at l,
  simp at l,
  have k: 1+2 = 3,
  norm_num,
  rw ← k at l,
  rw pow_add at l,
  simp at l,
  rw mul_comm at l,
  rw mul_div_assoc at l,
  rw div_self at l,
  simp at l,
  have l1: 3 = (real.sqrt 3) ^ 2,
  norm_num,
  rw l1 at l,
  rw sq_lt_sq at l,
  have p1: 0 ≤ n,
  linarith,
  rw ← abs_eq_self at p1,
  rw p1 at l,
  have p2: 0≤ real.sqrt 3,
  exact real.sqrt_nonneg 3,
  rw ← abs_eq_self at p2,
  rw p2 at l,
  linarith,
  linarith,
  linarith,
  push_neg at p,
  have p2: 0≤ real.sqrt 3,
  exact real.sqrt_nonneg 3,
  linarith,
end

-- a lemma
lemma part_c_lemma1 : (real.sqrt 3) ∈ upper_bounds Siii :=
begin
  rw upper_bounds,
  simp,
  intro n,
  intro h,
  unfold Siii at h,
  simp at h,
  by_cases p: 0 < n,
  have l:= div_lt_div_of_lt p h,
  rw mul_div_assoc at l,
  rw div_self at l,
  simp at l,
  have k: 1+2 = 3,
  norm_num,
  rw ← k at l,
  rw pow_add at l,
  simp at l,
  rw mul_comm at l,
  rw mul_div_assoc at l,
  rw div_self at l,
  simp at l,
  have l1: 3 = (real.sqrt 3) ^ 2,
  norm_num,
  rw l1 at l,
  rw sq_lt_sq at l,
  have p1: 0 ≤ n,
  linarith,
  rw ← abs_eq_self at p1,
  rw p1 at l,
  have p2: 0≤ real.sqrt 3,
  exact real.sqrt_nonneg 3,
  rw ← abs_eq_self at p2,
  rw p2 at l,
  linarith,
  linarith,
  linarith,
  push_neg at p,
  have p2: 0≤ real.sqrt 3,
  exact real.sqrt_nonneg 3,
  linarith,
end

-- Square root 3 is the least upper bound.
lemma part_c_lub : is_lub Siii (real.sqrt 3) :=
begin
  rw is_lub,
  rw is_least,
  split,
  exact part_c_lemma1,
  rw lower_bounds,
  simp,
  intro n,
  intro h1,
  rw upper_bounds at h1,
  unfold Siii at h1,
  simp at h1,
  by_contra,
  push_neg at h,
  by_cases p: (3/2 : ℝ) ≤ n,
  let t:= real.sqrt 3 - n,
  have ht: real.sqrt 3 - t = n,
    simp [t],
  let k:= real.sqrt 3 - (t/2),
  have l: k ^3 < 3 * k,
  have l2: 0 < k,
  simp [k],
  simp [t],
  linarith,
  have l3: k ^2 < 3,
  simp [k],
  rw sub_sq,
  rw real.sq_sqrt,
  have l4: real.sqrt 3 ≤ real.sqrt 4,
  have l5: (3 :ℝ) ≤ (4 :ℝ) ,
  norm_num,
  exact real.sqrt_le_sqrt l5,
  have l6: (4 :ℝ) = (2 :ℝ) * (2 :ℝ),
  norm_num,
  rw l6 at l4,
  have l7: 0 ≤ (2 :ℝ),
  norm_num,
  rw real.sqrt_mul_self l7 at l4,
  have l8: (t/2) < 1,
  simp [t],
  linarith,
  rw sq,
  have l9: 0 < real.sqrt 3,
  linarith,
  have l10: 1 < real.sqrt 3,
  linarith,
  have l11: 0 < (t/2),
  linarith,
  have l12: -(2 * (real.sqrt 3)) * (t/2) + (t/2) * (t/2) < 0,
  rw ← right_distrib,
  have l13: -(2 * (real.sqrt 3)) + (t/2) < 0,
  linarith,
  exact mul_neg_of_neg_of_pos l13 l11,
  linarith,
  linarith,
  have l4: k ^ 2 * k < 3 * k,
  exact mul_lt_mul_of_pos_right l3 l2,
  have l5: 1+2 = 3,
  norm_num,
  rw ← l5,
  rw pow_add,
  simp,
  rw mul_comm,
  exact l4,
  have h2 := h1 l,
  have h3 : n < k,
  have h4: 0 < t,
  linarith,
  simp [k],
  rw ← ht,
  linarith,
  linarith,
  push_neg at p,
  have ll: (3/2 : ℝ) ^ 3 < 3 * (3/2 : ℝ),
  norm_num,
  have h2 := h1 ll,
  linarith,
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