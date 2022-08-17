/-
8. The manufacturers of the high-fibre cereal “Improve Your Functions”
are offering a prize of £1000 to anyone who can find three different
integers a, b, c and a polynomial P(x) with integer coefficients, such that
P(a) = b, P(b) = c and P(c) = a.
Critics Ivor Smallbrain and Greta Picture spend several long evenings
trying to solve this, without success.
Prove that nobody will win the prize.
(Hint: Observe that P(x) − P(y) = (x − y)Q(x, y), where Q(x, y) is a
polynomial in x, y with integer coefficients. Substitute x = a, y = b, etc.,
into this equation and see what happens.)
-/

import tactic
import data.polynomial.eval
import data.polynomial
import data.mv_polynomial.comm_ring

open_locale polynomial -- notation for polynomials

open polynomial

-- prove for the hint
variables {R : Type*} [comm_ring R] (p : R[X])  {A : Type*} [comm_ring A]
  (f : R →+* A) (s t : A)

open mv_polynomial

open_locale big_operators

lemma dvd_pow_sub_pow (a b : R) (n : ℕ) : (a - b) ∣ a^n - b^n :=
begin
  cases n, { simp, },
  use ∑ i in finset.range n.succ, a ^ i * b ^ (n - i),
  simp_rw [finset.mul_sum, sub_mul, finset.sum_sub_distrib],
  rw finset.sum_range_succ,
  rw finset.sum_range_succ',
  suffices : ∑ (x : ℕ) in finset.range n, a * (a ^ x * b ^ (n - x)) = ∑ (k : ℕ) in finset.range n, b * (a ^ (k + 1) * b ^ (n - (k + 1))),
  { rw [this, nat.succ_eq_add_one, nat.sub_self], ring_exp, },
  refine finset.sum_congr rfl (λ i hi, _),
  rw finset.mem_range at hi,
  rw [pow_add],
  ring_nf,
  congr',
  rw ← pow_succ',
  congr',
  rw [nat.sub_eq_iff_eq_add hi.le, add_right_comm, add_assoc],
  rw nat.lt_iff_add_one_le at hi,
  exact (nat.sub_eq_iff_eq_add hi).mp rfl,
end

lemma dvd_poly_sub_poly : (s - t) ∣ p.eval₂ f s - p.eval₂ f t :=
begin
  apply p.induction_on,
  -- check it for zero, monomials and sums
  { simp, }, -- that's zero
  { intros p q hp hq, -- this is addition
    convert dvd_add hp hq,
    simp only [polynomial.eval₂_add],
    ring,
  },
  -- this is the tricky case
  { rintro m a h',
    simp,
    rw ← mul_sub,
    apply dvd_mul_of_dvd_right,
    apply dvd_pow_sub_pow,
  },
end

-- useful lemma for the proof
lemma iff_one_mul (a b : ℤ) (ha : a ≠ (0:ℤ)): a = b * a ↔ b = 1 := 
begin
  split,
  {
    intro h,
    have h1 : a / a = (b * a) / a,
    {exact congr (congr_arg has_div.div h) rfl},
    have h2 : b * a / a = b,
    {sorry},
    sorry 
  },
  {
    intro h,
    rw h,
    ring,
  },
end

-- the sorry above needs this
example (a : ℤ) (a ≠ 0): a / a = 1 :=
begin
  have ha : a = a * 1,
  {ring},
  -- apply int.div_eq_of_eq_mul_right (why this doesn't work;-;),
  sorry
end

example : ¬ ∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ P : ℤ[X], eval a P = b ∧ eval b P = c ∧ eval c P = a :=
begin
  intro h,
  rcases h with ⟨a, b, c, hab, hbc, hca, P, hP1, hP2, hP3⟩,
  have h : ∀ x y : ℤ, (x - y) ∣ eval x P - eval y P,
  {apply dvd_poly_sub_poly},
  have h1 : ∃ k1 : ℤ, (b - c) = k1 * (a - b),
  {
    specialize h a b, rwa [hP1, hP2] at h, exact exists_eq_mul_left_of_dvd h
  },
  have h2 : ∃ k2 : ℤ, (c - a) = k2 * (b - c),
  {
    specialize h b c, rwa [hP2, hP3] at h, exact exists_eq_mul_left_of_dvd h
  },
  have h3 : ∃ k3 : ℤ, (a - b) = k3 * (c - a),
  {
    specialize h c a, rwa [hP3, hP1] at h, exact exists_eq_mul_left_of_dvd h
  },
  cases h1 with k1 h1,
  cases h2 with k2 h2,
  cases h3 with k3 h3,
  have hk : k1 * k2 * k3 = 1,
  { 
    ring_nf,
    suffices : (a - b) = (k3 * k2 * k1) * (a - b),
    sorry,
    linear_combination (-k2 - 1) * h1 + (-(k3 * k1) - 1) * h2 + (-(k2 * k1) - k1) * h3,
  },
  -- then we can use something like 'int.eq_one_or_neg_one_of_mul_eq_one'' to consider different cases for k1, k2, k3
  sorry,
end


-- thinking if this alternative way may be more leanable
lemma dvd_mod_le (a b : ℤ) (hb : b ≠ 0) : a ∣ b → |a| ≤ |b| :=
begin
  sorry,
end

example (a b c : ℤ) (h1 : |a| ≤ |b|) (h2 : |b| ≤ |c|) (h3 : |c| ≤ |a|) : |a| = |b| ∧ |a| = |c| :=
begin
  split,
  -- maybe we can use something like ge_antisymm here
  sorry,
  sorry,
end

