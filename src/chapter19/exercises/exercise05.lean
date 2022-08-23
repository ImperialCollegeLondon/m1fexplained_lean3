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

-- A stronger of part b which should be easier to use
-- (the point is that f might not be injective on s)
lemma partb' {ι : Type*} {s : finset ι} (f : ι → ℤ) (hs : s.nonempty) {n : ℕ} (hn : 0 < n)
  (hs' : n < s.card): ∃ a b ∈ s, a ≠ b ∧ (n : ℤ) ∣ f a - f b :=
begin
  let f' : ι → ℤ := λ z, (f z) % n, 
  let T : finset ℤ := finset.Ico 0 n,
  have hfT : ∀ z : ι, z ∈ s → (f' z) ∈ T,
  {
    intros z hz,
    simp only [f', finset.mem_Ico],
    have hn' : (n : ℤ) ≠ 0, 
    { norm_cast, exact hn.ne', },
    split,
    { exact int.mod_nonneg _ hn', },
    { convert int.mod_lt _ hn',
      simp only [nat.abs_cast], },
  },
  have hST : T.card * 1 < s.card,
  { simp [hs'], },
  obtain ⟨y, hyT, hcard⟩ := 
    finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hfT hST,
  rw finset.one_lt_card_iff at hcard,
  rcases hcard with ⟨a, b, ha, hb, hab⟩,
  rw finset.mem_filter at ha hb,
  refine ⟨a, ha.1, b, hb.1, hab, _⟩,
  dsimp at ha hb,
  apply int.modeq.dvd,
  change f' b = f' a,
  rw [hb.2, ha.2],
end

open_locale big_operators

lemma finset.sum_Ico {M : Type*} [add_comm_group M]
  {a b : ℕ} (h : a ≤ b) (f : ℕ → M) : 
  ∑ i in finset.Ico a b, f i = ∑ j in finset.range b, f j - ∑ j in finset.range a, f j :=
begin
  rw eq_sub_iff_add_eq,
  rw ← finset.sum_union,
  { apply finset.sum_congr _ (λ x _, rfl),
    rw finset.range_eq_Ico,
    rw finset.union_comm,
    rw finset.Ico_union_Ico_eq_Ico (nat.zero_le a) h,
  },
  { rintros x (hx : x ∈ _ ∩ _),
    rw [finset.mem_inter, finset.mem_Ico, finset.mem_range] at hx,
    rcases hx with ⟨⟨h1, _⟩, h2⟩,
    exact false.elim (h1.not_lt h2), },
end

lemma partc (n : ℕ) (hn : 0 < n) (f : ℕ → ℤ) : ∃ S : finset ℕ, 
  S ⊆ finset.range n ∧ S.nonempty ∧ (n : ℤ) ∣ ∑ i in S, f i :=
begin
  --  {ι : Type*} {s : finset ι} (f : ι → ℤ) (hs : s.nonempty) {n : ℕ} (hn : 0 < n)
  -- (hs' : n < s.card): ∃ a b ∈ s, a ≠ b ∧ (n : ℤ) ∣ f a - f b := sorry
  rcases partb' (λ t, ∑ i in finset.range t, f i) 
    (@finset.nonempty_range_succ n) hn (by simp) with ⟨a, ha, b, hb, hab, hn⟩,
  rw finset.mem_range_succ_iff at ha hb,
  rw ne_iff_lt_or_gt at hab,
  rcases hab with hab | (hab : b < a),
  { use finset.Ico a b,
    refine ⟨_, _, _⟩,
    { rw finset.range_eq_Ico,
      rw finset.Ico_subset_Ico_iff hab,
      exact ⟨zero_le a, hb⟩, },
    { rwa finset.nonempty_Ico, },
    { rw finset.sum_Ico hab.le,
      rw [← dvd_neg, neg_sub],
      exact hn, },
  },
  { -- b < a case
    use finset.Ico b a,
    refine ⟨_, _, _⟩,
    { rw finset.range_eq_Ico,
      rw finset.Ico_subset_Ico_iff hab,
      exact ⟨zero_le b, ha⟩, },
    { rwa finset.nonempty_Ico, },
    { rw finset.sum_Ico hab.le,
      exact hn, },
  },
end

lemma partd (S : finset ℤ) (hS : ∀ s ∈ S, (1 : ℤ) ≤ s ∧ s ≤ 50) (hScard : S.card = 10) : ∃ A B : finset ℤ,
  A.card = 5 ∧ B.card = 5 ∧ A ≠ B ∧ A ≤ S ∧ B ≤ S ∧ ∑ i in A, i = ∑ j in B, j :=
begin
  -- consider possibilities for subset of S with card 5
  let P := finset.powerset_len 5 S,
  -- consider possibilities for sum
  let F := finset.Icc (15 : ℤ) 240,
  have hFP : F.card * 1 < P.card,
  { simp [nat.card_Icc, finset.card_powerset_len 5 S, hScard],
    have h : (10 : ℕ).choose 5 = 252,
    {refl},
    simp [h],
    norm_num, },
  let g : finset ℤ → ℤ := λ x, ∑ i in x, i,
  have hg : ∀ p : finset ℤ, p ∈ P → (g p) ∈ F,
  { intros p hp,
    simp [g],
    rw finset.mem_powerset_len at hp,
    split,
    {
      sorry
    },
    {
      sorry
    },
  },
  have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hFP,
  dsimp at this,
  rcases this with ⟨y, hy1, hy2⟩,
  rw finset.one_lt_card at hy2,
  rcases hy2 with ⟨A, hA, B, hB, hAB⟩,
  rw finset.mem_filter at hA hB,
  use A,
  use B,
  rw [finset.mem_powerset_len] at hA hB,
  simp [hAB, hA.1, hB.1],
  simp [g] at hA hB,
  rw [hA.2, hB.2],
end

lemma parte (T : finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 50) (hTcard : T.card = 9) : ∃ A B : finset ℤ,
  A ≤ T ∧ B ≤ T ∧ A ∩ B = ∅ ∧ ∑ i in A, i = ∑ j in B, j :=
begin
  -- as long as we can find two non-empty sets A, B of the same sum, we can find two disjoint set by A\B and B\A
  suffices h : ∃ C D : finset ℤ, C ≤ T ∧ D ≤ T ∧ C ≠ D ∧ ∑ i in C, i = ∑ j in D, j,
  {
    -- let A = C - (C ∩ D), B = D - (C ∩ D),
    rcases h with ⟨C, D, hC, hD, hCD, h⟩,
    let A : finset ℤ := C \ D,
    let B : finset ℤ := D \ C,
    use A,
    use B,
    have hAC : A ≤ C, apply finset.sdiff_subset,
    have hBD : B ≤ D, apply finset.sdiff_subset,
    have hA : A ≤ T := le_trans hAC hC,
    have hB : B ≤ T := le_trans hBD hD,
    split, exact hA,
    split, exact hB,
    have hAB : A ∩ B = ∅,
    {
      sorry
    },
    simp [hAB],
    let X := C ∩ D,
    suffices : ∑ (i : ℤ) in A, i + ∑ (x : ℤ) in X, x = ∑ (j : ℤ) in B, j + ∑ (x : ℤ) in X, x,
    exact (add_left_inj (∑ (x : ℤ) in X, x)).mp this,
    convert h,
    {
      suffices : C = A ∪ X,
      rw this,
      rw ←  finset.sum_union,
      exact finset.disjoint_sdiff_inter C D,
      ext a,
      rw [finset.mem_union],
      split,
      {
        intro ha,
        sorry
      },
      { intro ha,
        cases ha with ha1 ha2,
        exact hAC ha1,
        exact finset.mem_of_mem_inter_left ha2, },
    },
    {
      sorry
    },
  },
  {
    -- consider powerset of T
    let P := finset.powerset T,
    let F := finset.Icc (0:ℤ) 414,
    have hPF : F.card * 1 < P.card,
    {
      simp [nat.card_Icc, finset.card_powerset, hTcard],
      norm_num,
    },
    -- find a map from P to F by summing elements in P
    let g : finset ℤ → ℤ := λ x, ∑ i in x, i,
    have hg : ∀ p : finset ℤ, p ∈ P → (g p) ∈ F,
    {
      intros p hp,
      simp [g],
      rw finset.mem_powerset at hp,
      split,
      {
        sorry
      },
      {
        sorry
      },
    },
    have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hPF,
    dsimp at this,
    rcases this with ⟨y, hy1, hy2⟩,
    rw finset.one_lt_card at hy2,
    rcases hy2 with ⟨C, hC, D, hD, hCD⟩,
    rw finset.mem_filter at hC hD,
    use C,
    use D,
    rw [finset.mem_powerset] at hC hD,
    simp [hCD, hC.1, hD.1],
    simp [g] at hC hD,
    rw [hC.2, hD.2],
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

example (C D : finset ℤ) : C = (C \ D) ∪ (C ∩ D) :=
begin
  sorry
end

example (T Q: finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 200) (hQ : ∀ q ∈ Q, (q ≤ (199:ℤ) ∧ ( ¬ 2 ∣ q))): 
  ∀ t : ℤ, t ∈ T → ∃ k : ℕ, ∃ q ∈ Q, (t = 2^k * q) :=
begin
  intros t ht,
  specialize hT t ht,
  cases hT with h1 h2,
  -- find the odd divisor of t
  sorry,
end