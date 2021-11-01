
-- cac4dv

-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,

end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),

end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,

end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,

end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  split,
  assume h,
  have p_or_np := classical.em P,         cases p_or_np with p np,
  have q_or_nq := classical.em Q,         cases q_or_nq with q nq,
  exact false.elim (h(and.intro p q)),
  apply or.inr,                           exact nq,
  apply or.inl,                           exact np,
  assume np_or_nq,                        assume p_or_q,
  cases np_or_nq with np nq,              cases p_or_q with p q,
    have f := np p,
    exact f,
  cases p_or_q with p q,
    have f := nq q,
    exact f,

end

-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  intros P Q h1,
  have p_or_np := classical.em P,
    apply or.elim p_or_np,
  assume p,
    have p_or_q := or.intro_left Q p,
      apply false.elim,
      exact h1 p_or_q,
  assume np,
    have q_or_nq := classical.em Q,
      apply or.elim q_or_nq,
  assume q,
    have p_or_q := or.intro_right P q,
      apply false.elim,
      exact h1 p_or_q,
    assume nq,
      apply and.intro np nq,

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro  _,

  assume porq,
  have pornop := classical.em P,
  have qornoq := classical.em Q,
  apply or.elim qornoq,
  apply or.elim pornop,
  assume p q,

  apply or.intro_left _,
  exact p,

  assume np q,
  apply or.intro_right,
  exact and.intro np q,

  assume nq,
  apply or.elim porq,
  assume p,
  apply or.intro_left _,
  exact p,
  assume q,
  have qfalse : false := nq q,
  apply false.elim _,
  exact qfalse,

  assume h,
  apply or.elim h,

  assume p,
  apply or.intro_left _ _,
  exact p,

  assume g,
  have q : Q :=and.elim_right g,
  apply or.intro_right _ _,
  exact q,

end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔ P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  assume porqandporr,
  have porq := and.elim_left porqandporr,
  have porr := and.elim_right porqandporr,
  apply or.elim porq,

  assume p,
  apply or.intro_left (Q ∧ R) p,

  assume q,
  apply or.elim porr,

  assume p,
  apply or.intro_left (Q ∧ R) p,

  assume r,
  have qr := and.intro q r,
  apply or.intro_right P qr,

  assume PorQandR,
  apply or.elim PorQandR,

  assume p,
  have porq := or.intro_left Q p,
  have porr := or.intro_left R p,
  have porqanporr := and.intro porq porr,
  exact porqanporr,

  assume qr,
  have q := and.elim_left qr,
  have r := and.elim_right qr,
  have porq := or.intro_right P q,
  have porr := or.intro_right P r,
  apply and.intro _ _,
  exact porq,
  exact porr,

end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _,
  assume h,
  apply or.elim h,

    assume pr,
    have p : P := and.elim_left pr,
  have porq := or.intro_left Q p,
  have r := and.elim_right pr,
  have rors := or.intro_left S r,
  apply and.intro porq rors,
  assume h2,
  apply or.elim h2,

  assume ps,
  have p : P := and.elim_left ps,
  have porq := or.intro_left Q p,
  have s : S := and.elim_right ps,
  have rors := or.intro_right R s,
  apply and.intro porq rors,

  assume h3,
  apply or.elim h3,

  assume qr,
  have q : Q := and.elim_left qr,
  have porq := or.intro_right P q,
  have r : R := and.elim_right qr,
  have rors := or.intro_left S r,
  apply and.intro porq rors,

  assume qs,
  have q : Q := and.elim_left qs,
  have porq : ( P ∨ Q) := or.intro_right P q,
  have s : S := and.elim_right qs,
  have rors := or.intro_right R s,
  apply and.intro porq rors,

  assume h,
  have porq := and.elim_left h,
  have rors := and.elim_right h,
  apply or.elim porq,
  apply or.elim rors,

  assume r p,
  have pr := and.intro p r,
  apply or.intro_left,
  exact pr,

  assume s p,
  have ps := and.intro p s,
  apply or.intro_right,
  apply or.intro_left,
  exact ps,
  apply or.elim rors,
  assume r q,
  have qr := and.intro q r,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  exact qr,

  assume s q,
  have qs := and.intro q s,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  exact qs,

end

/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃(n : ℕ), 1 ≠ 0:=
begin
  apply exists.intro 1,
  assume n,
  contradiction,

end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _,

  have pornp := classical.em P,
  have qornq := classical.em Q,
  assume h,             assume p, 
  apply or.elim h,      apply or.elim qornq,
  assume q np,
  exact q,
  assume nq np,
  apply false.elim,
  have pfalse := np p,
  exact pfalse,
  assume q,             exact q,
  assume h,
  have pornp := classical.em P,
  apply or.elim pornp,
  assume p,
  have q : (Q),
  apply h,
  exact p,
  apply or.intro_right,
  exact q,
  assume np,
  apply or.intro_left _,
  exact np,

end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q h nq,
  apply not.intro,
  have pornp := classical.em P,
  apply or.elim pornp,
  assume p,
  have q: (Q),
  apply h,
  exact p,                        assume p,
  exact nq q,
  assume np p,                    exact np p,

end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q h q,
  have pornp := classical.em P,
  apply or.elim pornp,
  assume p,                       exact p,
  assume np,
  have nq : ¬Q,
  apply h,
  exact np,
  apply false.elim,
  exact nq q,

end

