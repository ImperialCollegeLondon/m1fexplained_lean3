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
import algebra.big_operators.fin

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
    --apply partb,
    have hS : (finset.image S _).card = n + 1,
    {
      suffices :  (finset.image S _).card = fintype.card (fin (n + 1)),
      rw this,
      exact fintype.card_fin (n + 1),
      apply finset.card_image_of_injective,
      exact h1,
    },
    have p := partb n hn _ hS,
    rcases p with ⟨a, ha, b, hb, p⟩,
    simp at *,
    cases ha with a1 ha1,
    cases hb with b1 hb1,
    refine ⟨a1, b1, _⟩,
    cases p with p1 p2,
    simp [ha1, hb1, p2],
    finish,
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

lemma partc (n : ℕ) (hn : 0 < n) (f : fin n → ℤ) : ∃ S : finset (fin n), S ≠ ∅ ∧ (n : ℤ) ∣ ∑ i in S, f i :=
begin
  rcases (partb' n hn (fin.partial_sum f)) with ⟨a, b, hab⟩,
  rw ne_iff_lt_or_gt at hab,
  obtain ⟨c, hc⟩ : ∃ (c : ℕ), c.succ = n := by refine ⟨(n - 1), by omega⟩,
  haveI : has_zero (fin n),
  { subst hc,
    exact fin.has_zero, },
  let g := λ (i : fin n), if a ≤ i ∧ ↑i < b then i else 0,
  refine ⟨finset.image g (finset.univ : finset (fin n)), _⟩,
  simp only [ne.def, finset.image_eq_empty],
  refine ⟨top_ne_bot, _⟩,
  have hT : fin.partial_sum f a - fin.partial_sum f b = ∑ i : fin n, f (g i),
  { dsimp [fin.partial_sum],
    repeat {rw list.sum_take_of_fn},
    simp only [fin.val_eq_coe, finset.sum_filter],
    dsimp [g],
    
    sorry},
  rw hT at hab,
  have goal : (finset.image g finset.univ).sum f = ∑ (i : fin n), f (g i),
  { 
    sorry},
  rw goal,
  exact hab.2,
end

lemma partd (S : finset ℤ) (hS : ∀ s ∈ S, (1 : ℤ) ≤ s ∧ s ≤ 50) (hScard : S.card = 10) : ∃ A B : finset ℤ,
  A.card = 5 ∧ B.card = 5 ∧ A ≠ B ∧ A ≤ S ∧ B ≤ S ∧ ∑ i in A, i = ∑ j in B, j :=
begin
  -- consider possibilities for subset of S with card 5
  let P := finset.powerset_len 5 S,
  -- consider possibilities for sum
  let F := finset.Icc (15 : ℤ) 240,
  have hFP : F.card * 1 < P.card,
  {
    simp [nat.card_Icc, finset.card_powerset_len 5 S, hScard],
    have h : (10 : ℕ).choose 5 = 252,
    {refl},
    simp [h],
    norm_num,
  },
  let g : finset ℤ → ℤ := λ x, ∑ i in x, i,
  have hg : ∀ p : finset ℤ, p ∈ P → (g p) ∈ F,
  { 
    intros p hp,
    simp [g],
    -- apply finset.mem_powerset,
    sorry
  },
  have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hFP,
  dsimp at this,
  rcases this with ⟨y, hy1, hy2⟩,
  rw finset.one_lt_card at hy2,
  rcases hy2 with ⟨A, hA, B, hB, hAB⟩,
  rw finset.mem_filter at hA hB,
  cases hB with hB1 hB2,
  cases hA with hA1 hA2,
  use A,
  use B,
  simp [hAB],
  have hAcard : A.card = 5,
  {
    -- apply finset.mem_powerset_len,
    sorry
  },
  have hBcard : B.card = 5,
  {
    sorry
  },
  have h : ∑ (i : ℤ) in A, i = ∑ (j : ℤ) in B, j,
  {
    suffices : g A = g B,
    simpa [g] using this,
    simp [hB2, hA2],
  },
  simp [hAcard, hBcard, h],
  split,
  {
    -- finset.mem_powerset,
    sorry
  },
  {
    sorry
  },
end

lemma parte (T : finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 50) (hTcard : T.card = 9) : ∃ A B : finset ℤ,
  A ≤ T ∧ B ≤ T ∧ A ∩ B = ∅ ∧ ∑ i in A, i = ∑ j in B, j :=
begin
  -- as long as we can find two non-empty sets A, B of the same sum, we can find two disjoint set by A/B and B/A
  suffices h : ∃ C D : finset ℤ, C ≤ T ∧ D ≤ T ∧ C ≠ D ∧ ∑ i in C, i = ∑ j in D, j,
  {
    -- let A = C - (C ∩ D), B = D - (C ∩ D),
    rcases h with ⟨C, D, hC, hD, hCD, h⟩,
    let A := C \ D,
    let B := D \ C,
    -- rw finset.mem_sdiff, -- example of a theorem about sdiff
    -- `mem` is `∈`
    -- `sdiff` is `\` 

    sorry,
  },
  {
    -- consider powerset of T
    let P := finset.powerset T,
    let F := finset.Icc 0 414,
    have hPF : F.card * 1 < P.card,
    {
      simp [nat.card_Icc, finset.card_powerset, hTcard],
      linarith,
    },
    -- find a map from P to F by summing elements in P
    -- let g : P → F :=  λ x, ∑ i in (x : finset ℤ), i,
    -- have hg : ∀ p : finset ℤ, p ∈ P → (g p) ∈ F,
    -- have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hFP,
    sorry
  },
end

lemma partf (T : finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 200) (hTcard : T.card = 101) : ∃ a b : ℤ,
  a ∈ T ∧ b ∈ T ∧ a ≠ b ∧ a ∣ b :=
begin
  -- claim : every t can be written as 2^k * q for which q is odd
  have h : ∀ t : ℤ, t ∈ T → ∃ k q : ℕ, (q ≤ 199) ∧ ( ¬ 2 ∣ q) ∧ (t = 2^k * q),
  {
    intros t ht,
    specialize hT t ht,
    cases hT with h1 h2,
    -- find the odd divisor of t
    sorry,
  },
  -- there are 100 posibilities for q as every even number can be 'reduced'
  -- let Q : finset ℤ :=  
  -- have hTO : T.card * 1 < Q.card
  -- find a map from Q to T, by considering corresponding 'q'
  -- let f : Q → T := 
  -- have hg : ∀ q ∈ Q, (f q) ∈ T,
  -- have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hTO,
  sorry
end

