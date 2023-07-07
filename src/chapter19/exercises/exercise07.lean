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
  { apply fintype.card_congr,
    exact equiv.subtype_injective_equiv_embedding S T, },
  rw h,
  simpa [fintype.card_embedding_eq, hS, hT],
end

open_locale big_operators -- for Π 

lemma partb (S T : Type) [fintype S] [fintype T] (m n : ℕ) (hmn : m ≤ n) (hS : fintype.card S = m) (hT : fintype.card T = n): 
  fintype.card {f : S → T // function.injective f} = ∏ i in finset.Icc (n - m + 1) n, i :=
begin
  have h : fintype.card {f : S → T // function.injective f} = fintype.card (S ↪ T),
  { apply fintype.card_congr,
    exact equiv.subtype_injective_equiv_embedding S T, },
  rw h,
  simp [fintype.card_embedding_eq, hS, hT],
  clear hS hT h _inst_1 _inst_2,
  induction m,
  simp,
  have hm : m_n ≤ n := nat.le_of_succ_le hmn, 
  specialize m_ih hm,
  simp [nat.desc_factorial_succ, m_ih, nat.succ_eq_add_one],
  have p : insert (n - m_n) (finset.Icc (n - m_n + 1) n) = finset.Icc (n - (m_n + 1) + 1) n,
  { ext c,
    split,
    { intro hc,
      simp at *,
      cases hc with hc1 hc2,
      { subst hc1,
        simp,
        linarith, },
      { simp [hc2],
        linarith [hc2.1], }, },
    { intro hc,
      simp at *,
      simp [hc],
      cases hc with hc1 hc2,
      by_cases n - m_n + 1 ≤ c,
      { right,
        exact h, },
      { push_neg at h,
        left,
        linarith, }, }, },
  rw ← p,
  simp,
end 
