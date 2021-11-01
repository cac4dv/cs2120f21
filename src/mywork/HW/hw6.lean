import data.set

/- Exercise: Prove that for any set, L, L ∩ L = L. -/
example : ∀ {α : Type} (L : set α), L ∩ L = L := 
begin
  intros α L,
  apply set.ext _,
  assume a_hyp,
  split,

  assume b_hyp, cases b_hyp with b_hyp_l b_hyp_r, exact b_hyp_r,
  assume c_hyp,
  apply and.intro,
  repeat { exact c_hyp }, 
end 
-- forall elements of type α that exist within a set
-- the intersection of the set with itself is itself

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example : ∀ {α : Type} (A B C : set α), A ∪ B ∪ C = A ∪ C ∪ B := 
begin
  intros α A B C,
  apply set.ext _,
  assume x,
  split,
  -- forward and backwards
  repeat {
    assume h,
    cases h with h_l h_r,
    cases h_l with h_ll h_lr,
    apply or.intro_left,
    apply or.intro_left,
    exact h_ll,
    apply or.intro_right,
    exact h_lr,
    apply or.intro_left,
    apply or.intro_right,
    exact h_r,
  },
end 
-- forall elements of type α
-- the union between sets A, B, and C
-- is equal to the union between sets A, C, and B


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
variable  (α      : Type)
variables (W X Y Z: set α)

def set_refl : X ⊆ X := 
begin
  assume x y,
  assumption,
end
-- forall elements of type α, the subset of a set X is itself
def set_trans :  X ⊆ Y → Y ⊆ Z → X ⊆ Z := 
begin
  assume a x y z,
  exact x (a z),
end
-- forall elements of type α...
-- if set X is a subset of Y, then Y is a subset of Z 
-- and if Y is a subset of Z then by extension Z is also a subset of X

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
example : ∀ {α : Type} (A B C : set α), A ∪ (B ∪ C) = (A ∪ B) ∪ C := 
begin
  intros α A B C,
  apply set.ext,
  assume a,
  split,
  -- forwards
  assume a_hyp,
  cases a_hyp with a_hyp_l a_hyp_r,
  apply or.intro_left,
  apply or.intro_left,
  exact a_hyp_l,
  cases a_hyp_r with a_hyp_rl a_hyp_rr,
  apply or.intro_left,
  apply or.intro_right,
  exact a_hyp_rl,
  apply or.intro_right,
  exact a_hyp_rr,
  -- backwards
  assume b_hyp,
  cases b_hyp with b_hyp_l b_hyp_r,
  cases b_hyp_l with b_hyp_ll b_hyp_lr,
  apply or.intro_left,
  exact b_hyp_ll,
  apply or.intro_right,
  apply or.intro_left,
  exact b_hyp_lr,
  repeat { apply or.intro_right },
  exact b_hyp_r,
end
-- forall elements of type α
-- the union A and (the union of B and C) is equal to ..
-- the union of (the union of sets A and B) and C

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-//- Exercise: Formally state and prove that ∩ is left-distributive over ∩. -/
example : ∀ {α : Type} (A B C : set α), A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C) := 
begin
  intros α A B C,
  apply set.ext,
  assume x,
  split,
-- forward
  assume a_hyp,
  cases a_hyp with a_hyp_l a_hyp_r,
  apply and.intro,
  apply and.intro,
  exact a_hyp_l,
  cases a_hyp_r with a_hyp_r_l a_hyp_r_r,
  exact a_hyp_r_l,
  cases a_hyp_r with a_hyp_rl a_hyp_r_r,
  apply and.intro,
  exact a_hyp_l,
  exact a_hyp_r_r,
-- backward
  assume b_hyp,
  cases b_hyp with b_hyp_l b_hyp_r,
  cases b_hyp_l with b_hyp_ll b_hyp_lr,
  apply and.intro,
  exact b_hyp_ll,
  apply and.intro,
  exact b_hyp_lr,
  cases b_hyp_r with b_hyp_rl b_hyp_rr,
  exact b_hyp_rr,
end
-- forall elements of type α
-- the intersection A and (the intersection of B and C) is equal to ..
-- the intersection of (the intersection of sets A and B) and (the intersection of sets A and C)

/- Exercise: Formally state and prove that ∪ is left-distributive over ∩. -/
example : ∀ {α : Type} (A B C : set α), A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := 
begin
  intros α A B C,
  apply set.ext,
  assume x,
  split,
--forward
  assume a_hyp,
  cases a_hyp with a_hyp_l a_hyp_r,
  apply and.intro,
  repeat{ apply or.intro_left, exact a_hyp_l, },
  cases a_hyp_r with a_hyp_rl a_hyp_rr,
  apply and.intro,
  apply or.intro_right,
  exact a_hyp_rl,
  apply or.intro_right,
  exact a_hyp_rr,
--backward
  assume b_hyp,
  cases b_hyp with b_hyp_l b_hyp_r,
  cases b_hyp_l with b_hyp_ll b_hyp_lr,
  cases b_hyp_r with b_hyp_rl b_hyp_rr,
  apply or.intro_left,
  exact b_hyp_ll,
  apply or.intro_left,
  exact b_hyp_ll,
  cases b_hyp_r with b_hyp_rl b_hyp_rr,
  apply or.intro_left,
  exact b_hyp_rl,
  apply or.intro_right,
  apply and.intro,
  exact b_hyp_lr,
  exact b_hyp_rr,
end
-- forall elements of type α
-- the union A and (the intersection of B and C) is equal to ..
-- the union of (the intersection of sets A and B) and (the intersection of sets A and B)