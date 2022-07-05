import tactic

-- True or false? n = 3 ↔ n^2-2n-3=0. If you think it's false
-- then you'll have to modify the statement by putting it in brackets
-- and adding a ¬ in front of it. 
lemma part_a : ∀ n : ℤ, n = 3 → n ^ 2 - 2 * n - 3 = 0 :=
begin
  norm_num,
end

lemma part_b : ¬ (∀ n : ℤ, n ^ 2 - 2 * n - 3 = 0 → n = 3) := 
begin
  intro h,
  specialize h(-1),
  norm_num at h,
end

lemma part_c : ¬ (∀ n : ℤ, n ^ 2 - 2 * n - 3 = 0 → n = 3) :=
begin
  intro h,
  specialize h(-1),
  norm_num at h,
end

def is_square (n : ℤ) : Prop := ∃ m : ℤ, n = m ^ 2

lemma part_d : ¬ (∀ a b : ℤ, is_square (a * b) → is_square a ∧ is_square b) :=
begin
  intro h,
  specialize h (-1) (-1),
  norm_num at h,
  unfold is_square at h,
  have h_left : ∃ (m : ℤ), 1 = m ^ 2,
  {use 1, norm_num},
  specialize h h_left,
  cases h with m hm,
  nlinarith,
end

lemma part_e : ∀ a b : ℤ, (is_square a ∧ is_square b) → is_square (a * b) :=
begin
  intros a b h,
  unfold is_square at h,
  rcases h with ⟨⟨x, hx⟩,⟨y, hy⟩⟩,
  unfold is_square,
  use x*y,
  rw hx,
  rw hy,
  ring,
end


