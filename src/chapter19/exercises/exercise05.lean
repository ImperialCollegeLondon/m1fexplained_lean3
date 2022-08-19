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
import combinatorics.pigeonhole

open function 

lemma parta (S : finset ℤ) (hS : S.card = 6) : ∃ a b ∈ S, a ≠ b ∧ (5 : ℤ) ∣ a - b :=
begin
  let f : ℤ → ℤ := λ z, z % 5, 
  let T : finset ℤ := finset.Ico 0 5,
  have hfT : ∀ z : ℤ, z ∈ S → (f z) ∈ T,
  {
    intros z hz,
    simp [f, T],
    split,
    apply int.mod_nonneg,
    norm_num,
    apply int.mod_lt,
    norm_num,
  },
  have hST : T.card * 1 < S.card,
  { 
    simp [T, hS],
    norm_num,
  },
  have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hfT hST,
  dsimp at this,
  rcases this with ⟨y, Hy, H⟩,
  rw finset.one_lt_card at H,
  rcases H with ⟨a, ha, b, hb, H⟩,
  simp at ha hb,
  use [a, ha.1, b, hb.1, H],
  have h : f a = f b,
  {rw [ha.2, hb.2]},
  simp [f] at h,
  exact (int.modeq.symm h).dvd,
end

lemma partb (n : ℕ) (hn : 0 < n) (S : finset ℤ) (hS : S.card = n + 1) : ∃ a b ∈ S, a ≠ b ∧ (n : ℤ) ∣ a - b :=
begin
  let f : ℤ → ℤ := λ z, z % n, 
  let T : finset ℤ := finset.Ico 0 n,
  have hfT : ∀ z : ℤ, z ∈ S → (f z) ∈ T,
  {
    intros z hz,
    simp [f, T],
    split,
    apply int.mod_nonneg,
    linarith,
    convert int.mod_lt _ _,
    simp,
    linarith,
  },
  have hST : T.card * 1 < S.card,
  { 
    simp [T, hS],
  },
  have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hfT hST,
  dsimp at this,
  rcases this with ⟨y, Hy, H⟩,
  rw finset.one_lt_card at H,
  rcases H with ⟨a, ha, b, hb, H⟩,
  simp at ha hb,
  use [a, ha.1, b, hb.1, H],
  have h : f a = f b,
  {rw [ha.2, hb.2]},
  simp [f] at h,
  exact (int.modeq.symm h).dvd,
end

-- I think that this version of part (b) is more appropriate for doing part (c)
lemma partb' (n : ℕ) (hn : 0 < n) (S : fin (n + 1) → ℤ) : ∃ a b : fin (n + 1), a ≠ b ∧ (n : ℤ) ∣ S a - S b :=
begin
  -- this stronger version can be split into two cases
  have hs : injective S ∨ ¬ injective S,
  {finish},
  cases hs with h1 h2,
  {
    sorry,
  },
  {
    unfold injective at h2,
    push_neg at h2,
    rcases h2 with ⟨a, b, h⟩,
    use a,
    use b,
    cases h with hp hq,
    split,
    exact hq,
    simp [hp],
  },
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