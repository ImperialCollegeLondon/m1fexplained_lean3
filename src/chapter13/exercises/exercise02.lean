import data.int.modeq
import data.nat.prime

namespace chapter13.exercise02

/-
Let p be a prime number and k a positive integer.
(a) Show that if x is an integer such that x^2 ≡ x mod p, then x ≡ 0 or 1 mod p.
(b) Show that if x is an integer such that x^2 ≡ x mod p^k, then x ≡ 0 or 1 mod p^k.
-/

open nat

lemma part_a (p : ℤ) (hp : prime p) (x : ℤ) : x^2 ≡ x [ZMOD p] → x ≡ 0 [ZMOD p] ∨ x ≡ 1 [ZMOD p] :=
begin
  sorry
end

lemma part_b (p : ℤ) (hp : prime p) (k : ℕ) (hk : k > 0) (x : ℤ) : x^2 ≡ x [ZMOD p^k] → x ≡ 0 [ZMOD p^k] ∨ x ≡ 1 [ZMOD p^k] := 
begin
  sorry
end

end chapter13.exercise02
