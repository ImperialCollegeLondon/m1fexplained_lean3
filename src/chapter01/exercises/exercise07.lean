import tactic

/-
7. Disprove the following statements:
(a) If n and k are positive integers, then n^k − n is always divisible by k.
(b) Every positive integer is the sum of three squares (the squares be-ing 0, 1, 4, 9, 16, etc.).
-/

lemma part_a : ¬ (∀ n k : ℕ, n > 0 → k > 0 → k ∣ n ^ k - n) :=
begin
  intro h,
  specialize h 2 4,
  norm_num at h,
end

lemma part_b : ¬ (∀ n : ℕ, n > 0 → ∃ a b c : ℕ, a>0 ∧ b>0 ∧ c>0 ∧ n = a^2 + b^2 + c^2) :=
begin
  intro h,
  specialize h 1,
  norm_num at h,
  rcases h with ⟨a, ha, b, hb, c, hc, h⟩, 
  have hm : a^2 + b^2 + c^2 >= 3,
  swap,
  rw ← h at hm,
  norm_num at hm,
  clear h,
  have ha2 : a^2 > 0,
  apply pow_pos, assumption, 
  have hb2 : b^2 > 0,
  apply pow_pos, assumption,
  have hc2 : c^2 > 0,
  apply pow_pos, assumption,
  linarith,
end

