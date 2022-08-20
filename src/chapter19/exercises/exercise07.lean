/-
7. (a) Let S = {1, 2, 3} and T = {1, 2, 3, 4, 5}. How many functions are
there from S to T ? How many of these are 1-1?
(b) Let |S| = m, |T | = n with m ≤ n. Show that the number of 1-1 func-
tions from S to T is equal to n(n − 1)(n − 2) · · ·(n − m + 1).
-/
import tactic
import data.fintype.card_embedding

open_locale classical

-- replace 37 with the right number
lemma parta (S T : Type) [fintype S] [fintype T] (hS : fintype.card S = 3) (hT : fintype.card T = 5) :
  fintype.card (S → T) = 125 :=
begin
  simp [fintype.card_fun, hS, hT],
  norm_num,
end

-- replace 37 with the right number
lemma parta' (S T : Type) [fintype S] [fintype T] (hS : fintype.card S = 3) (hT : fintype.card T = 5) :
  fintype.card {f : S → T // function.injective f} = 60 :=
begin
  have h : fintype.card {f : S → T // function.injective f} = fintype.card (S ↪ T),
  {
    apply fintype.card_congr,
    exact equiv.subtype_injective_equiv_embedding S T,
  },
  rw h,
  simpa [fintype.card_embedding_eq, hS, hT],
end

open_locale big_operators -- for Π 

lemma partb (S T : Type) [fintype S] [fintype T] (m n : ℕ) (hmn : m ≤ n) (hS : fintype.card S = m) (hT : fintype.card T = n): 
  fintype.card {f : S → T // function.injective f} = ∏ i in finset.Icc (n - m + 1) n, i :=
begin
  have h : fintype.card {f : S → T // function.injective f} = fintype.card (S ↪ T),
  {
    apply fintype.card_congr,
    exact equiv.subtype_injective_equiv_embedding S T,
  },
  rw h,
  simp [fintype.card_embedding_eq, hS, hT],
  clear hS hT h _inst_1 _inst_2,
  rw [nat.desc_factorial_eq_div, nat.div_eq_of_eq_mul_right ((n - m).factorial_pos)],
  swap,
  exact hmn,
  sorry,
end 

-- attempt to solve the sorry above
example (a b : ℕ) (hab : b ≤ a): a.desc_factorial b = ∏ i in finset.Icc (a - b + 1) a, i :=
begin
  rw [nat.desc_factorial_eq_div, nat.div_eq_of_eq_mul_right ((a - b).factorial_pos)],
  swap,
  exact hab,
  induction a,
  simp,
  rcases lt_trichotomy b a_n with h1 | h2 | h3,
  {
    have := le_of_lt h1,
    specialize a_ih this,
    sorry
  },
  {
    have := (eq.symm h2).ge,
    specialize a_ih this,
    sorry
  },
  {
    have hb : b = a_n.succ, 
    {
      rw [nat.lt_iff_add_one_le] at h3, 
      exact ge_antisymm h3 hab,
    },
    simp [hb],
    sorry,
  },
end


