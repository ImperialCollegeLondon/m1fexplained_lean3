/-
6. (a) Find an onto function from ℕ to ℤ.
(b) Find a 1-1 function from ℤ to ℕ.
-/

import tactic

open function

def f (n : ℕ) : ℤ := if 2 ∣ n then n / 2 else - (n+1) / 2 -- replace 37 with a surjective function

lemma dvd_mul_add_iff (n t b : ℤ) : n ∣ n * t + b ↔ n ∣ b :=
begin
  split,
  { rw dvd_iff_exists_eq_mul_left,
    rintro ⟨d, hd⟩,
    rw dvd_iff_exists_eq_mul_left,
    use d - t,
    linear_combination hd, },
  { rw dvd_iff_exists_eq_mul_left,
    rintro ⟨d, hd⟩,
    rw dvd_iff_exists_eq_mul_left,
    use d + t,
    linear_combination hd, },

  -- rw dvd_add_right,
  -- apply dvd_mul_right 
end

lemma f_surj : surjective f :=
begin
  intro z,
  rcases lt_trichotomy z 0 with h1 | rfl | h3,
  {
    use (-2*z-1).nat_abs,
    unfold f,
    split_ifs,
  {
    exfalso,
    rw int.coe_nat_dvd_left.symm at h,
    simp at h,
    rw (show  -(2 * z) - 1 = 2 * (- z - 1) + 1, by ring) at h,
    rw dvd_add_right at h,
    norm_num at h,
    apply dvd_mul_right,
  },
  {
    apply int.div_eq_of_eq_mul_left,
    norm_num,
    rw int.nat_abs_of_nonneg,
    ring,
    linarith,
  },
  },
  {use 0,
  unfold f,
  split_ifs,
  simp,
  exfalso,
  norm_num at h,
  },
  {use (2 * z).nat_abs,
  unfold f,
  split_ifs,
  apply int.div_eq_of_eq_mul_left,
  norm_num,
  rw int.nat_abs_of_nonneg,
  ring,
  linarith,
  exfalso,
  apply h,
  rw ← int.coe_nat_dvd_left,
  norm_num,
  },
end

def g (z : ℤ) : ℕ := if 0 < z then 2 * z.nat_abs else 2 * z.nat_abs + 1 -- replace 37 with an injective function

lemma g_inj : injective g :=
begin
  sorry
end
