import tactic

lemma part_a : ¬ (∀ n k : ℕ, n > 0 → k > 0 → k ∣ n ^ k - n) :=
begin
  intro h,
  specialize h 2 4,
  norm_num at h,
end

lemma part_b : ¬ (∀ n : ℕ, n > 0 → ∃ a b c : ℕ, n = a^2 + b^2 + c^2) :=
begin

end

