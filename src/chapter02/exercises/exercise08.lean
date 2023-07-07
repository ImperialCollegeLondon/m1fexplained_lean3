import tactic

inductive colour : Type
| red : colour
| blue : colour
| green : colour

def horrify : ℕ × ℕ × ℕ → colour → ℕ × ℕ × ℕ
| (r, b + 1, g + 1) red   := (r + 2, b, g)
| (r + 1, b, g + 1) blue  := (r, b + 2, g)
| (r + 1, b + 1, g) green := (r, b, g + 2)
| (r, b, g) _             := (r, b, g)

/-- Critic Ivor Smallbrain is watching the horror movie Salamanders on a
Desert Island. In the film, there are 30 salamanders living on a desert
island: 15 are red, 7 blue and 8 green. When two of a different colour
meet, horrifyingly they both change into the third colour. (For example,
if a red and a green meet, they both become blue.) When two of the same
colour meet, they change into both of the other colours. (For example, if
two reds meet, one becomes green and one becomes blue.) It is all quite
terrifying.

In between being horrified and terrified, Ivor idly wonders whether it
could ever happen that at some instant in the future, all of the salaman-
ders would be red. It turns out that this would never happen. -/

lemma mod_invar (li: ℕ × ℕ × ℕ) (t:colour) : 2*(horrify li t).2.1 + (horrify li t).2.2 ≡  2*li.2.1 + li.2.2 [MOD 3] :=
begin
  have h : 4 = 1 + 3, refl,
  rcases li with ⟨a, b,c⟩,
  dsimp,
  cases t; cases a; cases b; cases c;
  rw horrify;
  simp only [mul_zero, zero_add, add_zero, dvd_zero, ←nat.add_one];
  ring_nf;
  unfold nat.modeq;
  repeat {rw [h, ← add_assoc, nat.add_mod_right]};
  rw [← add_assoc, nat.add_mod_right],
end

lemma list_invar (l : list colour) (li: ℕ × ℕ × ℕ) : 2*(list.foldl horrify li l).2.1 + (list.foldl horrify li l).2.2 ≡  2*li.2.1 + li.2.2 [MOD 3] :=
begin
  induction l using list.reverse_rec_on with x hx hm,
  simp only [list.foldl_nil],
  simp only [list.foldl_append, list.foldl_cons, list.foldl_nil],
  have h := mod_invar (list.foldl horrify li x) hx,
  unfold nat.modeq at *,
  rwa hm at h,
end

lemma salamander : ¬ ∃ (l : list colour), list.foldl horrify (15, 7, 8) l = (30, 0, 0) :=
begin
  rintros ⟨l, hl⟩,
  have t := list_invar l (15, 7, 8),
  rw hl at t,
  simp only [mul_zero, add_zero] at t,
  norm_num at t,
end
