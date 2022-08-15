/-
5. Use the Pigeonhole Principle to prove the following statements involv-
ing a positive integer n:
(a) In any set of 6 integers, there must be two whose difference is divisible by 5.
(b) In any set of n + 1 integers, there must be two whose difference is
divisible by n.
(c) Given any n integers a₁, a₂,..., aₙ, there is a non-empty subset of
these whose sum is divisible by n. (Hint: Consider the integers 0,a₁ ,
a₁ + a₂ ,..., a₁ +...+aₙ and use (b).)
(d) Given any set S consisting of ten distinct integers between 1 and 50,
there are two different 5-element subsets of S with the same sum.
(e) Given any set T consisting of nine distinct integers between 1 and
50, there are two disjoint subsets of T with the same sum.
(f) In any set of 101 integers chosen from the set {1, 2, . . . , 200}, there
must be two integers such that one divides the other.
-/
import tactic

lemma parta (S : finset ℤ) (hS : S.card = 6) : ∃ a b ∈ S, a ≠ b ∧ (5 : ℤ) ∣ a - b :=
begin
  sorry
end

lemma partb (n : ℕ) (hn : 0 < n) (S : finset ℤ) (hS : S.card = n + 1) : ∃ a b ∈ S, a ≠ b ∧ (n : ℤ) ∣ a - b :=
begin
  sorry
end

-- I think that this version of part (b) is more appropriate for doing part (c)
lemma partb' (n : ℕ) (hn : 0 < n) (S : fin (n + 1) → ℤ) : ∃ a b : fin (n + 1), a ≠ b ∧ (n : ℤ) ∣ a - b :=
begin
  sorry
end

open_locale big_operators

lemma partc (n : ℕ) (a : fin n → ℤ) : ∃ S : finset (fin n), S ≠ ∅ ∧ (n : ℤ) ∣ ∑ i in S, a i :=
begin
  sorry
end

lemma partd (S : finset ℤ) (hS : ∀ s ∈ S, (1 : ℤ) ≤ s ∧ s ≤ 50) (hScard : S.card = 10) : ∃ A B : finset ℤ,
  A.card = 5 ∧ B.card = 5 ∧ A ≠ B ∧ A ≤ S ∧ B ≤ S ∧ ∑ i in A, i = ∑ j in B, j :=
begin
  sorry
end

lemma parte (T : finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 50) (hTcard : T.card = 9) : ∃ A B : finset ℤ,
  A ≤ T ∧ B ≤ T ∧ A ∩ B = ∅ ∧ ∑ i in A, i = ∑ j in B, j :=
begin
  sorry
end

lemma partf (T : finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 200) (hTcard : T.card = 101) : ∃ a b : ℤ,
  a ∈ T ∧ b ∈ T ∧ a ≠ b ∧ a ∣ b :=
begin
  sorry
end