import data.nat.prime
import data.int.modeq

/-
Let p be a prime number, and let a be an integer that is not divisible by p.
Prove that the congruence equation ax ≡ 1 mod p has a solution x ∈ ℤ.
-/

lemma mod_inv_exists (p : ℕ) (hp : prime p) (a : ℤ) (ha : ¬(↑p ∣ a)) : ∃x : ℤ, (a * x) ≡ 1 [ZMOD p] :=
begin
  sorry
end
