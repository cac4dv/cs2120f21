import data.set
/-
CS2120 F21 HW5
PART I: EXISTENTIAL QUANTIFICATION.
Goal:
- practice existential quantificaton
- develop your understanding of (in)formal set theory proofs
-//-
In this context complete the following tasks:
1. Write english proof
2. Write a proof in lean
-//-
English language:
If there's a  function that maps/takes every α value that ... 
  has a property of p and returns another value property of q.
This implies that forall values of a...
  there exists a value, a of type α, that has property of p...
  that implies that... 
  there exists a value, b of type β, that has a property of q.
-/    
axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicate
  (q : β → Prop)  -- predicate
-- proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a))
  → 
  (∃ (a : α), p a) → (∃ (b : β), q b)
:= 
-- proof
begin
  -- break big goal into smaller chunks that are already known
  intros f_chunk a_chunk,
  -- extract witnesses 
  cases a_chunk with a pa,
  cases f_chunk with f fx,
  -- find a way to provide a witness to ∃ b, q b
  apply exists.intro _ _,
  -- witness 1
  have b : β := f a,
  exact b,
  -- witness 2
  have fxx := fx a,
  exact fxx pa,  
end