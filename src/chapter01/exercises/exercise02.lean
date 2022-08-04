import data.real.basic

-- Let B,C,D,E be the following sets
def B : set ℝ := {x | x^2 < 4}
def C : set ℝ := {x | 0 ≤ x ∧ x < 2}
def D : set ℝ := {x | ∃ n : ℤ, x = n ∧ x^2 < 1}
def E : set ℝ := {1}

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
(h2 : X ⊆ B) : X = B ∨ X = C ∨ X = E:=
begin
  simp at hX,
  cases hX with hb hc,
  { left,
    apply hb, },
  { cases hc with h3 h4,
    right,
    left,
    apply h3,
    { cases h4 with h5 h6,
      { left,
        subst h5,
        rw D at h1,
        rw E at h1,
        finish, },
      { right, 
        subst h6,
        right,
        refl, }, }, },
end
