import tactic.interval_cases
import data.real.basic

-- Let B,C,D,E be the following sets
def B : set ℝ := {x | x^2 < 4}
def C : set ℝ := {x | 0 ≤ x ∧ x < 2}
def D : set ℝ := {x | ∃ n : ℤ, x = n ∧ x^2 < 1}
def E : set ℝ := {1}

lemma hD : D = ({0} : set ℝ) :=
begin
  simp_rw D,
  ext,
  split,
  { rintro ⟨n, rfl, hn⟩,
    simp_rw sq_lt_one_iff_abs_lt_one at hn,
    rw set.mem_singleton_iff,
    rw abs_lt at hn,
    cases hn with hl hr,
    norm_cast at *,
    interval_cases n, },
  intro hx,
  rw set.mem_singleton_iff at hx,
  simp_rw [hx, sq_lt_one_iff_abs_lt_one, exists_and_distrib_right, set.mem_set_of_eq, abs_zero, zero_lt_one, and_true],
  use (0:ℤ),
  norm_num,
end

-- Which pair of these sets has the property that neither is contained in the other?
lemma parta : ∃ S T ∈ ({B, C, D, E} : set (set ℝ)), ¬ (S ⊆ T) ∧ ¬ (T ⊆ S) :=
begin
  use D,
  split,
  { simp, },
  { use E,
    split,
    { simp, },
    { split, 
      { rw set.subset_def,
        push_neg,
        use 0,
        split,
        { rw D,
          use 0,
          norm_num, },
        { simp[E], }, },
      { rw set.subset_def,
        push_neg,
        use 1,
        split,
        { simp[E], },
        { simp[D], }, }, }, },
end

-- If X is either B,C,D,E and E ⊆ X ⊆ B, what else can we deduce about X? 
-- Note that figuring out what to prove is part of the question
lemma partb (X : set ℝ) (hX : X ∈ ({B,C,D,E} : set (set ℝ))) (h1 : E ⊆ X)
(h2 : X ⊆ B) : X ≠ D :=
begin
  intro hX',
  rw hX' at *,
  have hD2 : ¬ (E ⊆ D),
  { exfalso,
    simp_rw [E, hD] at h1,
    simp at h1,
    exact h1, },
  contradiction,
end