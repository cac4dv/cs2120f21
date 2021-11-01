--1
example : 0 ≠ 1 :=
begin
  assume h,
  cases h,
end
--2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h(eq.refl(0)),
  exact false.elim(f),
end
--3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P) := ¬¬P → (¬P → false) → ((P → false) → false),
  contradiction,
end
/-
axiom em : ∀ (p : Prop), p ∨ ¬P
Law of the excluded middle.
A key to proving many intuitive theorem in logic & maths.
It also leads to giving up on having evidence on why somehting is true.

-/

--4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  -- apply law of excluded middle
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end
--5
theorem demorgan_1 : ∀ (P Q : Prop), ¬(Q ∧ P) ↔ ¬P :=
begin
  
end
--6
theorem 