/-
Group Name: apply group.elim_left Chris,
Adam        Borneman  (jqf7yf)
Tho         Vu        (thv7pas)
Christopher Carrillo  (cac4dv)
-//-
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
-- Q1
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
-- Q2
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume p_and_p,
  apply and.elim_right p_and_p,
  assume p,
  apply and.intro p p,
end
-- Q3
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume p_or_q,
  apply or.elim p_or_q,
  assume p,
  apply or.intro_right Q,
  exact p,
  assume q,
  apply or.intro_left P,
  exact q,

  assume q_or_p,
  apply or.elim q_or_p,
  assume Q,
  apply or.intro_right P,
  exact Q,
  assume P,
  apply or.intro_left Q,
  exact P,
end
-- Q4
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume p_and_q,
  apply and.intro (and.elim_right p_and_q) (and.elim_left p_and_q),
  assume q_and_p,
  apply and.intro (and.elim_right q_and_p) (and.elim_left q_and_p),
end
-- Q5
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
  assume  p_and_qorr,
  have  p_of__pand_qorr  := and.elim_left  p_and_qorr,
  have  qr_of__pand_qorr := and.elim_right p_and_qorr,
  cases qr_of__pand_qorr,
  apply or.intro_left,
  exact and.intro p_of__pand_qorr qr_of__pand_qorr,
  apply or.intro_right,
  exact and.intro p_of__pand_qorr qr_of__pand_qorr,
  --backward
  assume pandq_or_pandr,
  apply and.intro,
  cases pandq_or_pandr,
  have  p := and.elim_left pandq_or_pandr,
  exact p,
  have  p := and.elim_left pandq_or_pandr,
  exact p,
  cases pandq_or_pandr,
  apply or.intro_left,
  have  q := and.elim_right pandq_or_pandr,
  exact q,
  apply or.intro_right,
  have  r := and.elim_right pandq_or_pandr,
  exact r,
end
-- Q6
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume    P Q R,
  apply     iff.intro _ _,
  assume    pq_and_pr,
  apply     or.elim pq_and_pr,

  assume    p,
  have      pq      := or.intro_left  Q   p,
  have      qr      := or.intro_left  R   p,
  have      p_or_QR := and.intro pq   qr,
  exact     p_or_QR,

  assume    qqr,
  have      q   := and.elim_left    qqr,
  have      r   := and.elim_right   qqr,
  have      pq  := or.intro_right   P   q,
  have      pr  := or.intro_right   P   r,
  apply     and.intro _,
  exact     pr,
  exact     pq,

  assume    pq_and_pr,
  have      pq  := and.elim_left      pq_and_pr,
  have      pr  := and.elim_right     pq_and_pr,
  apply     or.elim pq,
  assume    p,
  apply     or.intro_left   (Q ∧ R)   p,
  assume    q,
  apply     or.elim pr,
  assume    p,
  apply     or.intro_left   (Q ∧ R)   p,
  assume    r,
  have      qr := and.intro   q   r,
  apply     or.intro_right    P   qr,
end
-- Q7
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume  P Q,
  apply   iff.intro _ _,
  assume  p,
  apply   and.elim_left p,
  assume  h,
  apply   and.intro _ _,
  exact   h,
  apply   or.intro_left,
  exact   h, 
end
-- Q8
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply   iff.intro _ _,
  assume  h,
  apply   or.elim h,

  assume  p,
  exact   p,

  assume  pq,
  apply   and.elim_left pq,

  assume  p,
  apply   or.intro_left _ _,
  exact   p,
end
-- Q9
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume  P,
  apply   iff.intro _ _,
  assume  p_or_true,
  have    pt := true.intro,
  exact   pt,
  assume  true_or_p,
  apply   or.intro_right,
  apply   true.intro,
end
-- Q10
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume  P,
  apply   iff.intro _ _,
  assume  pf,
  apply   or.elim pf,
  assume  h,
  exact   h,
  assume  i,
  apply   false.elim,
  exact   i,

  apply   or.intro_left,
end
-- Q11
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume  P,
  apply   iff.intro _ _,
  assume  p_and_true,
  apply   and.elim_left p_and_true,

  assume  h,
  apply   and.intro,
  exact   h,
  apply   true.intro,
end
-- Q12
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume  P,
  apply   iff.intro _ _,
  assume  p_and_false,
  have    paf := and.elim_right p_and_false,
  exact   paf,
  assume  p_and_f,
  apply   false.elim,
  exact   p_and_f,
end