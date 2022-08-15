import tactic

/-
7. Disprove the following statements:
(a) If n and k are positive integers, then n^k − n is always divisible by k.
(b) Every positive integer is the sum of three squares (the squares be-ing 0, 1, 4, 9, 16, etc.).
-/

lemma part_a : ¬ (∀ n k : ℕ, n > 0 → k > 0 → k ∣ n ^ k - n) :=
begin
  -- True for k prime
  intro h,
  specialize h 2 4,
  norm_num at h,
end

/-
  https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/arithmetic.20timeout.20with.20a.5E2.2Bb.5E2.2Bc.5E2.3D7
  Thanks to Patrick Johnson
  Also a way via zmod by Alex J. Best
-/

lemma part_b : ¬ (∀ n : ℕ, n > 0 → ∃ a b c : ℕ, n = a^2 + b^2 + c^2) :=
begin
  -- True for n <= 6
  intro h,
  specialize h 7,
  have lt_three : ∀ {a b c : ℕ}, 7 = a ^ 2 + b ^ 2 + c ^ 2 → a < 3,
  { intros a b c h, nlinarith, },
  simp at h,
  rcases h with ⟨a, b, c, h⟩,
  have ha := lt_three h,
  have hb := lt_three (by linarith : 7 = b^2 + a^2 + c^2),
  have hc := lt_three (by linarith : 7 = c^2 + a^2 + b^2),
  interval_cases a; interval_cases b; interval_cases c; -- Generate 3 x 3 x 3 = 27 goals
  cases h,
end

