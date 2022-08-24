import tactic
import combinatorics.pigeonhole
import data.int.parity
import data.nat.factorization.basic

lemma partf (T : finset ℕ) (hT : ∀ t ∈ T, (1 : ℤ) ≤ t ∧ t ≤ 200) (hTcard : T.card = 101) : ∃ a b : ℕ,
  a ∈ T ∧ b ∈ T ∧ a ≠ b ∧ a ∣ b :=
begin
  -- claim : every t can be written as 2^k * q for which q is odd, using ord_compl[2] t
  let Q : finset ℕ := (finset.Icc 1 200).filter odd,
  have hQcard : Q.card = 100,
  {
    -- Show that it equals (finset.Iio 100).map \<\la n, 2 * n + 1, proof_of_injectivity_here\> 
    have hQ : Q = (finset.Iio 100).map ⟨λ n, 2 * n + 1 , 
                                        begin intros a b hab, 
                                        simpa [add_left_inj, mul_eq_mul_left_iff, bit0_eq_zero, nat.one_ne_zero, or_false] using hab, 
                                        end ⟩,
    { dsimp [Q],
      rw le_antisymm_iff,
      split,
      { intros x hx,
        simp only [finset.mem_map, finset.mem_Iio, function.embedding.coe_fn_mk, exists_prop, nat.one_le_cast, finset.mem_filter,
          finset.mem_Icc, nat.odd_iff_not_even] at hx ⊢,
        refine ⟨((x-1)/2), _, _⟩,
        { rcases hx with ⟨⟨h1, h2⟩, h3⟩,
          zify at h2 ⊢,
          rw int.div_lt_iff_lt_mul,
          linarith,
          norm_num, },
        { rcases hx with ⟨⟨h1, h2⟩, h3⟩,
          have := nat.even_or_odd x,
          cases this with hp hq,
          finish,
          unfold odd at hq,
          cases hq with k hq,
          rw hq,
          simp only [nat.add_succ_sub_one, add_zero, nat.mul_div_right, nat.succ_pos'], },
      },
      {
        intros x hx,
        simp only [finset.mem_map, finset.mem_Iio, function.embedding.coe_fn_mk, exists_prop, nat.one_le_cast, finset.mem_filter,
          finset.mem_Icc, nat.odd_iff_not_even] at hx ⊢,
        rcases hx with ⟨a, ⟨h1, h2⟩⟩,
        refine ⟨⟨_, _⟩, _⟩,
        { rw ← h2,
          linarith, },
        { rw ← h2,
          linarith, },
        { intro h,
          rw nat.even_iff at h,
          rw ← h2 at h,
          rw nat.mul_comm at h,
          rw nat.mul_add_mod a 2 1 at h,
          simp only [nat.one_mod, nat.one_ne_zero] at h,
          exact h, }, 
      },
    },
    rw hQ,
    simp only [nat.card_Iio, finset.card_map],
  },
  have hTO : Q.card * 1 < T.card,
  { rw [hQcard, hTcard], norm_num, },
  -- find a map from T to Q, by considering corresponding 'q'
  let f : ℕ → ℕ := λ z, ord_compl[2] z,
  have hf : ∀ t ∈ T, (f t) ∈ Q,
  { intros t ht,
    simp only [f, finset.mem_filter, finset.mem_Icc, nat.odd_iff_not_even],
    refine ⟨⟨_,_⟩,_⟩,
    {
      rw nat.one_le_div_iff,
      { apply nat.ord_proj_le 2,
        specialize hT t ht,
        cases hT with hT1 hT2,
        linarith, },
      {exact nat.ord_proj_pos t 2, },
    },
    { apply nat.div_le_of_le_mul,
      have h1 := nat.ord_proj_pos t 2,
      rw ← nat.succ_le_iff at h1,
      exact le_mul_of_one_le_of_le h1 (hT t ht).2, },
    {
      rw nat.not_even_iff,
      by_contra,
      sorry
    },
  },
  have := finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hTO,
  dsimp at this,
  rcases this with ⟨y, hy1, hy2⟩,
  rw finset.one_lt_card at hy2,
  rcases hy2 with ⟨a, ha, b, hb, hab⟩,
  by_cases a < b,
  { refine ⟨a, b, _⟩,
    simp only [hab, ne.def, not_false_iff, true_and],
    rw finset.mem_filter at ha hb,
    simp only [ha.1, hb.1, true_and],
    suffices : f a = f b,
    {
      sorry
    },
    { rw [ha.2, hb.2], }, },
  {
    sorry
  },
end

lemma ord_compl_eq_dvd (a b : ℕ) (h : ord_compl[2] a = ord_compl[2] b) (hab : a < b) :
  a ∣ b :=
begin
  sorry
end


