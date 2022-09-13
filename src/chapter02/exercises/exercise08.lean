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

lemma dvd_invar (li: ℕ × ℕ × ℕ) (t:colour) : 3 ∣ (2*li.2.1 + li.2.2 + (horrify li t).2.1 + 2*(horrify li t).2.2) :=
begin
  rcases li with ⟨a, b,c⟩,
  dsimp,
  cases t; cases a; cases b; cases c;
  rw horrify;
  simp only [mul_zero, zero_add, add_zero, dvd_zero, ←nat.add_one];
  ring_nf;
  try {use b+c+1, ring_nf};
  try {use c+1, ring_nf};
  try {use 0*a + b + 2, ring_nf};
  use b + 1;
  ring_nf,
end

lemma mod_invar (li: ℕ × ℕ × ℕ) (t:colour) : 2*(horrify li t).2.1 + (horrify li t).2.2 ≡  2*li.2.1 + li.2.2 [MOD 3] :=
begin
  have h := dvd_invar li t,
  have h2 : (3:ℤ) ∣ 3 * ↑(2 * (horrify li t).snd.fst + (horrify li t).snd.snd),
  {
    use ↑(2 * (horrify li t).snd.fst + (horrify li t).snd.snd),
  },
  have h3: (3:ℤ) ∣ -(2 * li.snd.fst + li.snd.snd + (horrify li t).snd.fst + 2 * (horrify li t).snd.snd),
  {
    rw dvd_neg,
    exact int.coe_nat_dvd.mpr h,
  },
  apply nat.modeq_iff_dvd.mpr,
  simp only [int.coe_nat_bit1, nat.cast_one, nat.cast_add, nat.cast_mul, int.coe_nat_bit0],
  apply (dvd_add_right h2).mp,
  simp only [nat.cast_add, nat.cast_mul, int.coe_nat_bit0, nat.cast_one],
  ring_nf,
  apply (dvd_add_right h3).mp,
  simp only [neg_add_rev],
  ring_nf,
  use ↑((horrify li t).snd.fst),
end


lemma list_invar (l : list colour) (li: ℕ × ℕ × ℕ) : 2*(list.foldl horrify li l).2.1 + (list.foldl horrify li l).2.2 ≡  2*li.2.1 + li.2.2 [MOD 3] :=
begin
  induction l using list.reverse_rec_on with x hx hm,
  simp only [list.foldl_nil],
  simp only [list.foldl_append, list.foldl_cons, list.foldl_nil],
  have h := mod_invar (list.foldl horrify li x) hx,
  unfold nat.modeq at *,
  rw hm at h,
  exact h,
end

lemma salamander : ¬ ∃ (l : list colour), list.foldl horrify (15, 7, 8) l = (30, 0, 0) :=
begin
  rintros ⟨l, hl⟩,
  have t := list_invar l (15, 7, 8),
  rw hl at t,
  simp only [mul_zero, add_zero] at t,
  norm_num at t,
end