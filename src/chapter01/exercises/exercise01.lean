import set_theory.zfc.basic
import tactic

lemma Set.well_founded : ¬ ∃ α : Set, α = {α} :=
begin
  sorry
end

variable α : Set.{0}

def zero : Set.{0} := {}
def one : Set.{0} := {zero}
def two : Set.{0} := {zero, one}
def three : Set.{0} := {zero, one, two}

@[reducible] def A : Set := {α, {one,α},{three},{{one,three}},three}

/-

This exercise is rather poorly-specified. Liebeck does not
give the set-theoretic definitions of `1` or `3`, and
does not say which set `α` is. As a result, the set `A`
depends on the input variable `α`, and some parts
of this question depend on the value of `α`.

-/

lemma part_a : α ∈ A (α) :=
begin
  simp,
end

lemma part_b_helper {α β} (h : α ≠ β) : ({α} : Set) ≠ {β} :=
begin
  intro h2,
  apply h,
  have : α ∈ ({β} : Set),
  { simp [← h2], },
  simpa,
end

lemma part_b_helper' : zero ≠ one :=
begin
  intro h,
  have h0 : zero ∈ zero,
  { nth_rewrite 1 h,
    simp [zero, one], },
  simpa [zero] using h0,
end

/-
I'm assuming part(b) is supposed to be false. 
However this depends on what α is supposed to be
and also on the implementation of the set `3`.
-/
lemma part_b (h1 : α ≠ one) -- otherwise {α} = {1,α} ∈ A
  (h3 : α ≠ three) -- otherwise {α} ∈ A
  (h13 : α ≠ {one, three}) -- otherwise {α} ∈ A
  : {α} ∉ A α :=
begin
  simp,
  push_neg,
  refine ⟨_, _, _, _, _⟩,
  { -- {α} ≠ α
    intro h,
    apply Set.well_founded,
    use α,
    rw h, },
  { -- α ≠ {1,α}
    intro h,
    apply h1,
    have : one ∈ ({one, α} : Set) := by simp,
    rw ← h at this,
    symmetry,
    simpa, },  
  { -- {α} ≠ {three}
    exact h3, },
  { -- {α} ≠ {{one,three}}
    exact h13, },
  { -- With our implementation of {3} we can't have
    -- {α} = 3, but if you implement the naturals
    -- numbers as n+1={n} then we would have to avoid
    -- the case α = 2 as well
    intro h,
    apply part_b_helper',
    transitivity α,
    { suffices : zero ∈ ({α} : Set),
      { simpa },
      rw h,
      simp [three], },
    { suffices : one ∈ ({α} : Set),
      { symmetry,
        simpa },
      rw h,
      simp [three], }, }
end

-- This part is true if α = 1
lemma part_c (h1 : α ≠ one) : ¬ {one, α} ⊆ A α :=
begin
  sorry
end

lemma part_d : {three, {three}} ⊆ A α :=
begin
  sorry
end

-- This part is true if α = three or if α = {one, three}
lemma part_e (h1 : α ≠ three) (h13 : α ≠ {one, three}) : ¬ {one, three} ∈ A α := 
begin
  sorry
end

-- this part is true if α = three or if α = {one, three}
-- (because it's the same question as part (e))
lemma part_f (h1 : α ≠ three) (h13 : α ≠ {one, three}) : ¬ {{one, three}} ⊆ A α := 
begin
  sorry
end

lemma part_g : {{one, α}} ⊆ A α :=
begin
  intros x hx,
  simp at hx,
  subst hx,
  simp,
end

lemma part_h : ¬ ({one,α} ∉ A α) :=
begin
  push_neg,
  simp,
end

lemma part_i : ∅ ⊆ A α :=
begin
  intros x hx,
  simp at hx,
  cases hx,
end
