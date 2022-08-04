import tactic
import data.real.sqrt
import data.int.modeq

/-

For each of the following functions `f`, say whether `f` is `1-1` and whether `f`
is `onto`.

-/

def f1 (x : ℝ) : ℝ := x^2 + 2*x

noncomputable def f2 (x : ℝ) : ℝ := 
  if 1 < x then x - 2 
  else if x < -1 then x + 2
  else -x

noncomputable def f3 (x : ℚ) : ℝ := (x + real.sqrt 2)^2

def f4 (mnr : ℕ × ℕ × ℕ) : ℕ := 
let ⟨m, n, r⟩ := mnr in
2 ^ m * 3 ^ n * 5 ^ r

def f5 (mnr : ℕ × ℕ × ℕ) : ℕ := 
let ⟨m, n, r⟩ := mnr in
2 ^ m * 3 ^ n * 6 ^ r

-- For the last question let's first make the equivalence relation
def e (a b : ℤ) : Prop := a ≡ b [ZMOD 7]

lemma he : equivalence e :=
⟨ 
  -- reflexive
  begin
    sorry
  end,
  -- symmetric
  begin
    sorry
  end,
  -- transitive
  begin
    sorry
  end ⟩

-- Let's now say that `e` is the "canonical" equivalence relation on ℤ
instance s : setoid ℤ := ⟨e, he⟩

-- and now we can use the theory of quotients. The set `S` in the question
-- is called `quotient s` here. 

def f6 (x : quotient s) : quotient s :=
quotient.map (λ t : ℤ, t + 1) begin
  -- Lean points out that if we don't show the below, then `f6` isn't well-defined!
  show ∀ a b : ℤ, a ≈ b → a + 1 ≈ b + 1,
  -- So we have to prove it now.
  sorry,
end x

-- `injective` is actually called `function.injective` so let's open `function`
open function

-- now we can just call it `injective`

/-

## The rules

If the functions are injective/surjective, prove the lemmas. If they're not,
then put `¬` in front of them (e.g. `exercise01inj : ¬ (injective f1)` and prove
that instead!

-/
lemma exercise01inj : ¬ (injective f1) :=
begin
  intro h,
  have hp : f1 (-2) = f1 0,
  {unfold f1, norm_num},
  specialize h hp,
  norm_num at h,
end

lemma exercise01surj : ¬ (surjective f1) :=
begin
  intro h,
  specialize h (-2),
  cases h with x hx,
  unfold f1 at hx,
  have hp : ∀ x : ℝ, x ^ 2 + 2 * x = -2 ↔ (x + 1)^2 = -1,
  {intro x, sorry},
  specialize hp x,
  rw hp at hx,
  nlinarith,
end

lemma exercise02inj : ¬ (injective f2) :=
begin
  intro h,
  have hp : f2 (1/2) = f2 (5/2),
  {sorry},
  specialize h hp,
  norm_num at h,
end

lemma exercise02surj : ¬ (surjective f2) :=
begin
  intro h,
  have hy : ∀ y : ℝ, y < 0 ∨ y = 0 ∨ 0 < y,
  {sorry},
  sorry,
end

lemma exercise03inj : injective f3 :=
begin
  sorry
end

lemma exercise03surj : surjective f3 :=
begin
  sorry
end

lemma exercise04inj : injective f4 :=
begin
  sorry
end

lemma exercise04surj : surjective f4 :=
begin
  sorry
end

lemma exercise05inj : injective f5 :=
begin
  sorry
end

lemma exercise05surj : surjective f5 :=
begin
  sorry
end

lemma exercise06inj : injective f6 :=
begin
  sorry
end

lemma exercise06surj : surjective f6 :=
begin
  sorry
end