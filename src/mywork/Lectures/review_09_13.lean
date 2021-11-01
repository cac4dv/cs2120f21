namespace implies
axioms (P Q : Prop) 
/--
If-Then Statement:
"If P then Q"
Requires proof of P being true for Q to be true
If we know that P is true we can assume Q is true
--/
def if_P_is_true_then_so_is_Q: Prop := P → Q

/--
assume P is true
assume we have a proof of P (p)
--/
axiom p : P

-- assume that we have a prrof, pq, of P → Q
-- axiom pq : if_P_is_true_then_so_is_Q
axiom pq: P → Q

/--
Introduction rule for implies: assume premise, show conclusion
Elimination rule for implies:
  apply the proof of P to get the proof of Q
--/
#check pq
#check p
#check (pq p)

/-
Suppose P and Q are propositions and you
know that P → Q and that P are both true.
Show that Q is true.

Proof: Apply the truth of P → Q to the
truth of P to derive the truth of Q.

Proof: By the elimination rule for → with
pq applied to p.

Proof: By "modus ponens". QED.
-/
end implies



namespace all
/-
FORALL
-/
axioms
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x)
--function argument value
  -- Does t have a property P?
  -- Yes, yes it does!!!
  example : P t := a t
  #check a t
end all

/-
AND & →
-/
axioms (P Q : Prop)

/-
Want a proof P ∧ Q.
P needs to be true while Q is also true
-/