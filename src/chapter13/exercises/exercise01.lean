import data.nat.modeq

/-
(a) Find r with 0 ≤ r ≤ 10 such that 7^137 ≡ r mod 11.
(b) Find r with 0 ≤ r < 645 such that 2^81 ≡ r mod 645.
(c) Find the last two digits of 3^124 (when expressed in decimal notation).
(d) Show that there is a multiple of 21 which has 241 as its last three digits.
-/

lemma part_a : ∃r : ℕ, 0 ≤ r ∧ r ≤ 10 ∧ 7^137 ≡ r [MOD 11] :=
begin
  sorry
end

lemma part_b : ∃r : ℕ, 0 ≤ r ∧ r < 645 ∧ 2^81 ≡ r [MOD 645] :=
begin
  sorry
end

-- Once you compute the last two digits, change 37 below to them.
lemma part_c : 3^124 ≡ 37 [MOD 100] :=
begin
  sorry
end

lemma part_d : ∃k : ℕ, 21 ∣ k ∧ k ≡ 241 [MOD 1000] :=
begin
  sorry
end