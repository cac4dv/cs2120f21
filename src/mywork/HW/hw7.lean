import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  assume e a r,
  unfold asymmetric at a,
  unfold reflexive  at r,
  cases e with x _,
  
  have rxx := r x,
  have c := a rxx,

  contradiction,
end



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  assume e,
  assume t r a,

  unfold transitive   at t,
  unfold reflexive    at r,
  unfold asymmetric   at a,

  cases e with x _,
  have rxx := r x,
  have c := a rxx,
  contradiction,
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  -- Introduce the powerset s and its subsets s1 and s2
  assume s s1 s2,
  -- Show that s1 and s2 derive from the powerset s
  assume s1_subof_s s2_subof_s,
  -- Show that s1 and s2 are subsets of each other
  assume s1_subof_s2 s2_subof_s1,
  apply set.ext _,
  assume x,
  split,
  apply s1_subof_s2,
  apply s2_subof_s1,
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  apply exists.intro n,
  ring_nf,
end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  apply exists.intro 1,
  ring_nf,
end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  assume n,
  apply exists.intro 1,
  ring_nf,
end 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,

  assume x y z ykx zky,
  /-
  For divides to be transitive the following must be true:  y = kx → z = ky → z = kx
  Where k is a constant that can be redefined
  -/
  -- redefine equations with redefinable variable k
  -- define ykx as y = kx
  cases ykx with k ykx,  
  -- define zky as z = ky
  cases zky with k zky,
  -- Show that z = 0*x = 0
  apply exists.intro 0,
  -- define k as 0 and rewrite 
  have k : k = 0 := sorry,
  rw k at zky,
  rw zky,
  -- proof by ring
  ring,
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/
-- Divides is not symmetric via proof by context of Q 4F in which we prove that divides is anti_symmetric.
-- See example below in which we prove `example : anti_symmetric divides :=`
-- On a serious note, a counter example would be 2 and 4, 2/4 is not equal to 4/2
/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  assume x y ykx xky,
  /- To prove that divides is asymetric, we need a proof for x = y
  In which we can extract them from the following mathematic expressions: y = kx && x = ky
  To prove this, substitute 1 for k, and use proof by ring -/
  cases ykx with k ykx,
  cases xky with k xky,
  have k : k = 1 := sorry,
  rw k at xky,
  rw xky,
  ring,
end


/- #5
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/
-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume asym x rxx,
  /-
  Given the following set β:{ x }...
  And how x is reflexsive to itself (which changes the set to β:{ x, x })
  And how asym shows that r x x → ¬r x x while asym → irefl
  A proof be contradiction is needed as irefl shows that r x x cannot imply ¬r x x
  -/
  -- provide a witness to ¬r x x
  have nrxx := asym rxx,
  -- Aaaaand QED
  contradiction,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume irefl trans x y rxy ryx,
  -- Given how (irefl x  → ¬r x x) → (r x y → r y x → r x z)
  -- A proof by contradiction is needed (a proof of r x x)
  -- To do so, we need to provide a witness to ireflexsive (¬r x x)
  apply irefl x,
  -- Now we need to provide a proof of r x x
  -- Since r x y → r y x, we know x = y
  have y : y = x := sorry,
  -- Rewrite rxy or ryx to show a proof of r x x
  rw y at rxy,
  -- QED
  assumption,
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume trans nsymm niref,

  -- Cannot be proven as an object of type β is not supplied and cannot be assumed.
  -- Such object is crucial to begin forming a proof of anything having to do with trans, nsymm, and niref
  -- And as such I admit defeat 
  admit,
end


end relation
