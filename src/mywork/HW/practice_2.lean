/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

-- trick question? why?
example : false := _
-- would need to prove that false is true which makes everything true
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward direction
    assume p_or_p,
    apply or.elim p_or_p,
    -- left disjunct is true
    assume p,
    exact p,
    -- right disjunct is true
    assume p,
    exact p,
  -- backwards direction
  assume p,
  -- exact or.intro_left P p,
  exact or.intro_right P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply and.intro _ _,
  apply assume p_and_p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


