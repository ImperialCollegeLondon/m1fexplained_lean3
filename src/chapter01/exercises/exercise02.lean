import tactic.interval_cases
import data.real.basic

-- Let B,C,D,E be the following sets
def B : set ℝ := {x | x^2 < 4}
def C : set ℝ := {x | 0 ≤ x ∧ x < 2}
def D : set ℝ := {x | ∃ n : ℤ, x = n ∧ x^2 < 1}
def E : set ℝ := {1}

-- Which pair of these sets has the property that neither is contained in the other?
lemma parta : ∃ S T ∈ ({B, C, D, E} : set (set ℝ)), ¬ (S ⊆ T) ∧ ¬ (T ⊆ S) :=
begin
  have h0 : D = ({0} : set ℝ),
  { simp_rw D,
    ext,
    split,
    { intro hx,
      simp at hx,
      simp,
      cases hx with hl hr,
      cases hl with a ha,
      rw ha at hr,
      rw ha,
      rw abs_lt at hr,
      cases hr with hrl hrr,
      by_contra hna,
      norm_cast at *,
      interval_cases a,
      contradiction, },
    intro hx,
    simp at hx,
    simp_rw hx,
    simp,
    use (0:ℤ),
    simp, },
  use D,
  split,
  simp,
  use E,
  split,
  simp,
  rw [h0, E],
  simp,
end

-- If X is either B,C,D,E and E ⊆ X ⊆ B, what else can we deduce about X? 
-- Note that figuring out what to prove is part of the question
lemma partb (X : set ℝ) (hX : X ∈ ({B,C,D,E} : set (set ℝ))) (h1 : E ⊆ X)
(h2 : X ⊆ B) : X ≠ D :=
begin
  intro hX',
  rw hX' at *,
  have hD : ¬ (E ⊆ D),
  { have h0 : D = ({0} : set ℝ),
    -- Any way I can get this hypothesis from the previous proof?
    { simp_rw D,
      ext,
      split,
      { intro hx,
        simp at hx,
        simp,
        cases hx with hl hr,
        cases hl with a ha,
        rw ha at hr,
        rw ha,
        rw abs_lt at hr,
        cases hr with hrl hrr,
        by_contra hna,
        norm_cast at *,
        interval_cases a,
        contradiction, },
      intro hx,
      simp at hx,
      simp_rw hx,
      simp,
      use (0:ℤ),
      simp, },
    exfalso,
    simp_rw [E, h0] at h1,
    simp at h1,
    exact h1, },
  contradiction,
end