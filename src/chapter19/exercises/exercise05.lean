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
import data.int.succ_pred

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

-- should be in mathlib maybe? (thanks Eric Rodriguez)
def sum_le_max (S : finset ℤ) (x : ℤ) (hS' : ∀ s ∈ S, s ≤ x) :
  ∑ i in S, i ≤ ∑ i in finset.Ioc (x - finset.card S) x, i :=
begin
  induction h : finset.card S with k ih generalizing S x,
  { obtain rfl := finset.card_eq_zero.mp h, simp},
  have hSn : 0 < S.card := h.symm ▸ k.succ_pos,
  replace hSn : S.nonempty := finset.card_pos.mp hSn,
  specialize ih (S.erase (S.max' hSn)) (x - 1) (λ s hs, _) _,
  { rw [←int.pred, ←int.pred_eq_pred, order.le_pred_iff],
    obtain ⟨hs₁, hs₂⟩ := finset.mem_erase.1 hs,
    exact (S.lt_max'_of_mem_erase_max' hSn hs).trans_le (hS' _ $ S.max'_mem hSn) },
  { simpa [h] using finset.card_erase_of_mem (S.max'_mem hSn) },
  have : x - 1 - k = x - k.succ,
  { rw [sub_sub, sub_right_inj],
    simp [add_comm] },
  rw this at ih,
  have hSm : S.max' hSn ≤ x := hS' _ (S.max'_mem hSn),
  replace ih := add_le_add ih hSm,
  suffices : finset.Ioc (x - k.succ) (x - 1) = (finset.Ioc (x - k.succ) x).erase x,
  { rwa [finset.sum_erase_add _ _ $ S.max'_mem hSn, this, finset.sum_erase_add] at ih,
    simp only [finset.right_mem_Ioc, sub_lt_self_iff],
    exact nat.cast_pos.mpr (k.succ_pos) },
  ext,
  simp only [nat.cast_succ, finset.mem_Ioc, finset.Ioc_erase_right, finset.mem_Ioo,
             and.congr_right_iff],
  rintro -,
  rw [←int.pred, ←int.pred_eq_pred, order.le_pred_iff]
end

-- should also be in mathlib maybe?
def min_le_sum (S : finset ℤ) (x : ℤ) (hS' : ∀ s ∈ S, x ≤ s) :
 ∑ i in finset.Ico x (x + finset.card S), i ≤ ∑ i in S, i :=
begin
  have := sum_le_max (finset.image (λ i, -i) S) (-x) _, swap,
  { intros s hs,
    rw finset.mem_image at hs,
    rcases hs with ⟨t, ht, rfl⟩,
    exact neg_le_neg (hS' t ht), },
  rw ← neg_le_neg_iff,
  have Scard : (finset.image has_neg.neg S).card = S.card,
  { rw finset.card_image_iff,
    intros x hx y hy,
    exact neg_inj.1,
  },
  convert this,
  { rw finset.sum_image,
    symmetry,
    apply finset.sum_neg_distrib,
    intros x hx y hy h,
    rwa neg_inj at h, },
  { rw ← finset.sum_neg_distrib,
    apply finset.sum_bij (λ (a : ℤ) ha, -a),
    { intros a ha,
      simp only [finset.mem_Ioc, neg_le_neg_iff],
      rw finset.mem_Ico at ha,
      rw Scard,
      cases ha,
      split;linarith, },
    { simp, },
    { simp, },
    { rw Scard,
      intros b hb,
      refine ⟨-b, _, _⟩,
      { simp at hb ⊢, cases hb, split; linarith, },
      { simp, }, }, },
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
    { convert min_le_sum p 1 (λ s hs, (hS s (hp.1 hs)).1),
      rw hp.2,
      refl,
    },
    { convert sum_le_max p 50 (λ s hs, (hS s (hp.1 hs)).2),
      rw hp.2,
      refl, }, },
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
  A ≤ T ∧ B ≤ T ∧ disjoint A B ∧ ∑ i in A, i = ∑ j in B, j :=
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
    have hAB : disjoint A B := disjoint_sdiff_sdiff,
    simp [hAB],
    let X := C ∩ D,
    suffices : ∑ (i : ℤ) in A, i + ∑ (x : ℤ) in X, x = ∑ (j : ℤ) in B, j + ∑ (x : ℤ) in X, x,
    exact (add_left_inj (∑ (x : ℤ) in X, x)).mp this,
    convert h,
    { 
      suffices : C = A ∪ X, 
      { rw this,
        rw ←  finset.sum_union,
        exact finset.disjoint_sdiff_inter C D, },
      ext x,
      simp only [finset.mem_union, finset.mem_sdiff, finset.mem_inter, ← and_or_distrib_left],
      tauto, },
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

example (T Q: finset ℤ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 200) (hQ : ∀ q ∈ Q, (q ≤ (199:ℤ) ∧ ( ¬ 2 ∣ q))): 
  ∀ t : ℤ, t ∈ T → ∃ k : ℕ, ∃ q ∈ Q, (t = 2^k * q) :=
begin
  intros t ht,
  specialize hT t ht,
  cases hT with h1 h2,
  -- find the odd divisor of t
  sorry,
end