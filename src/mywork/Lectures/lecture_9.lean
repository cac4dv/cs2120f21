/-
Negation
-//-
Given a proposition, P, we can form a new
proposition, usually written as ¬P, which we
prounce as "not P," and which we define in
such a way as to assert that P is not true.
-//-
So what does it mean when we say that
"It is true if P is not true"
-//-
First if ¬P is true, there should be a proof of it.
Second, what that proof should show is that
"There can be no proof of P"
-//-
So the way we're going to say ¬P is to say
if P were true then soemthing completely impossible
would happen. Beacause the impossible
cannot happen, therefore there must not be a proof of P.
-//-

-/

#check not

example : ¬ false := 
begin
  assume f,
  exact f,
end

example : ¬ 0 = 1 :=
begin
  assume  z_=_1,
  cases   z_=_1,
end