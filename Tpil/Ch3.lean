namespace chapter_material
-- We can represent propositions as types!
#check And
#check Or
#check Not

example (p: Prop) (hp : p): p :=
    hp


variable (p q r : Prop)

--We can select sides on an ∧
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

--How to make an ∧
example (h1 : p) (h2 : q) : p ∧ q := And.intro h1 h2

--Use Or.elim to prove something for both sides of an or
example (h : p ∨ q) (h1 : p -> r) (h2 : q -> r) : r := Or.elim h
    h1
    h2

example (h : p ∨ q) : q ∨ p := Or.elim h Or.inr Or.inl

--Making your ∨
example (hp : p) : p ∨ q := Or.inl hp
example (hq : q) : p ∨ q := Or.inr hq

--Sometimes we need to specify the type. So we have long form versions
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

--Not is fun. We intro a hypothesis that p is true, use it to prove q is true,
--and then show that that contradicts with hnp
example (hpq: p → q) (hnq: ¬q) : ¬p :=
    fun hp => hnq (hpq hp)

-- `False.elim` lets us take any two contradicting statements and use them to
-- make anything up
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

-- We can also just say `absurd`. For some reason it takes the args in p np
-- order instead of np p order like `False.elim`
example (hp: p) (hnp: ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq: q) (hq_imp_p : q → p) : r := absurd (hq_imp_p hq) hnp

-- ↔ is the symbol for if and only if. It implies that the left can prove the
-- right and the right can prove the left. We split it into two propositions
-- when proving something by writing `Iff.intro a b` and filling in a and b
-- with appropriate proofs for left → right and right → left respectfully

theorem and_swap : p ∧ q ↔ q ∧ p := Iff.intro
    (fun h => And.intro h.right h.left)
    (fun h => And.intro h.right h.left)

-- Iff.mp lets us take an iff statement and go left to right. mpr is the reverse
example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
example (h : q ∧ p) : p ∧ q := (and_swap p q).mpr h

-- We can `have` subgoals! This is actually really awesome if you don't know how
-- to prove a proposition yet but are pretty sure it's true and wanna see if it
-- helps before bothering to actually go back and do the work
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- `suffices` is similar but we prove using the prop that the solution holds
-- before proving that the prop holds. They're just the reverse of each other
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h


open Classical

-- Law of the Excluded Middle, `em` holds that p ∨ ¬p. In other words, p is
-- either true or false
#check em p

-- This means that if we know q is true if p is true or not true, we can prove q
-- always holds using `Or.elim (em p)`
example (hp_imp_q: p → q) (hnp_imp_q: ¬p → q) : q := Or.elim (em p) hp_imp_q hnp_imp_q

-- We can use this to show double elimination works using absurd in the not case. Fun!
theorem dne (h : ¬ ¬ p) : p := Or.elim (em p) (fun h => h) (fun hn => absurd hn h)

-- We can also do `byContradiction` which takes the not of the goal, introduces
-- it as a hypothesis, and then asks you to prove False by finding a contradiction

example (h : ¬¬p) : p := byContradiction (fun hnp => h hnp)

--Let's see how to do stuff with ¬(p ∧ q)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p) (fun hp => Or.inr (show ¬q from fun hq : q => h ⟨hp, hq⟩)) Or.inl

-- These concepts compose (obviously, that's the fucking point)
theorem and_dist_over_or (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
    (fun h =>
        have hp := h.left
        have hq_or_r := h.right
        Or.elim hq_or_r (fun hq => Or.inl (And.intro hp hq)) (fun hr => Or.inr (And.intro hp hr))
    )
    (fun h => Or.elim h
        (fun h =>
            have hp := h.left
            have hq := h.right
            And.intro hp (Or.inl hq))
        (fun h =>
            have hp := h.left
            have hr := h.right
            And.intro hp (Or.inr hr)))

#print and_dist_over_or

example: ¬(p ∧ ¬q) → (p → q) := fun h hp =>
    byContradiction (fun hnq => h ⟨hp, hnq⟩)

end chapter_material

namespace exercises

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro
    (fun hp_and_q => ⟨hp_and_q.right, hp_and_q.left⟩)
    (fun hq_and_p => ⟨hq_and_p.right, hq_and_p.left⟩)
example : p ∨ q ↔ q ∨ p := Iff.intro
    (fun hp_or_q => Or.elim hp_or_q (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun hq_or_p => Or.elim hq_or_p (fun hq => Or.inr hq) (fun hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
    (fun h =>
        have hp := h.left.left
        have hq := h.left.right
        have hr := h.right
        And.intro hp (And.intro hq hr))
    (fun h =>
        have hp := h.left
        have hq := h.right.left
        have hr := h.right.right
        And.intro (And.intro hp hq) hr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro
    (fun h => Or.elim h
        (fun h => Or.elim h
            (fun hp=> Or.inl hp)
            (fun hq=> Or.inr (Or.inl hq)))
        (fun hr => Or.inr (Or.inr hr)))
    (fun h => Or.elim h
        (fun hp => Or.inl (Or.inl hp))
        (fun h => Or.elim h
            (fun hq => Or.inl (Or.inr hq))
            (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
    (fun h =>
        have hp := h.left
        Or.elim h.right
            (fun hq => Or.inl (And.intro hp hq))
            (fun hr => Or.inr (And.intro hp hr)))
    (fun h => Or.elim h
        (fun h => And.intro h.left (Or.inl h.right))
        (fun h => And.intro h.left (Or.inr h.right)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
    (fun h =>
        Or.elim h
            (fun hp => And.intro (Or.inl hp) (Or.inl hp))
            (fun hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right))
        )
    (fun h => Or.elim h.left
        Or.inl
        (fun hq => Or.elim h.right
            Or.inl
            (fun hr => Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
    (fun h1 h2 => h1 h2.left h2.right)
    (fun h hp hq=> h (And.intro hp hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := Iff.intro
    (fun h => And.intro
        (fun hp: p => h (Or.inl hp))
        (fun hq: q => h (Or.inr hq)))
    (fun h hp_or_q=> Or.elim hp_or_q
        (fun hp => h.left hp)
        (fun hq => h.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
    (fun hc => And.intro
        (Classical.byContradiction fun h=>
            have hp := Classical.not_not.mp h
            hc (Or.inl hp))
        (Classical.byContradiction fun h =>
            have hq := Classical.not_not.mp h
            hc (Or.inr hq)))
    (fun hn =>
        Classical.byContradiction
            (fun h: ¬¬(p ∨ q) =>
                have h := Classical.not_not.mp h
                Or.elim h
                    (fun hp => hn.left hp)
                    (fun hq => hn.right hq)))
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    (fun h => Or.elim h
        (fun hnp => Classical.byContradiction (fun hp =>
             hnp (Classical.not_not.mp hp).left))
        (fun hnq => Classical.byContradiction (fun hq =>
             hnq (Classical.not_not.mp hq).right)))
example : ¬(p ∧ ¬p) := Classical.byContradiction
    fun h: ¬¬(p ∧ ¬p) =>
        have h := Classical.not_not.mp h
        h.right h.left

example : p ∧ ¬q → ¬(p → q) := fun h =>
    Classical.byContradiction fun hc =>
        have hc := Classical.not_not.mp hc
        h.right (hc h.left)
example : ¬p → (p → q) := fun hnp hp => absurd hp hnp
example : (¬p ∨ q) → (p → q) := fun hnp_or_q =>
    Or.elim hnp_or_q
        (fun hnp hp => absurd hp hnp)
        (fun hq _ => hq)
example : p ∨ False ↔ p := Iff.intro
    (fun h1 => Or.elim h1 id False.elim)
    (fun h2 => Or.inl h2)
example : p ∧ False ↔ False := Iff.intro
    (fun h1 => False.elim h1.right)
    (fun h2 => False.elim h2)
example : (p → q) → (¬q → ¬p) := fun hp_imp_q hnq =>
    Classical.byContradiction fun hnnp =>
        have hp := Classical.not_not.mp hnnp
        hnq (hp_imp_q hp)

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := fun h =>
--     --Okay so if we have hp, we plug it into h and easily prove the or statement
--     suffices hp : p from Or.elim (h hp)
--         (fun hq => Or.inl (fun _ => hq))
--         (fun hr => Or.inr (fun _ => hr))
--     -- So now to prove p. Whiiich we can't do. I think this is a dead end?
--    h
    Classical.byCases
        (fun hq:q => Or.inl (fun _ => hq))
        (fun hnq => (
            Or.inr (fun hp => (h hp).elim
                (fun hq => absurd hq hnq)
                id)))
--I'm not going to assume too much but it looks like if we can solve with a
--truth table we can solve by using em multiple times and using absurd to show
--the impossible ones false
example : ¬(p ∧ q) → ¬p ∨ ¬q := fun h => (em p).elim
    (fun hp => (em q).elim
        (fun hq => absurd ⟨hp, hq⟩ h)
        Or.inr)
    Or.inl

--I couldn't solve this myself, but the key realization is that ¬p can be
--rewritten as p → False
example : ¬(p → q) → p ∧ ¬q := fun h => byCases
    --for the p case we:
    (fun hp : p =>
        have hnq : ¬q := fun hq =>
            have hpq : p → q := fun _ => hq
            absurd hpq h
        show p ∧ ¬q from And.intro hp hnq)
    (fun hnp : ¬p =>
        have hpq : p → q := fun hp => absurd hp hnp
        absurd hpq h)

example : (p → q) → (¬p ∨ q) := fun h =>
    (em p).elim (fun hp => Or.inr (h hp))
    Or.inl
example : (¬q → ¬p) → (p → q) := fun h hp =>
    byContradiction fun hnq =>
        absurd hp (h hnq)

--THis is literally just the law of the excluded middle. Just fucking use it
example : p ∨ ¬p := em p
example : (((p → q) → p) → p) := fun h => byContradiction
    fun hnp =>
        have hpq : p → q := fun hp => absurd hp hnp
        hnp (h hpq)




end exercises
--something I did for fun. Yeah it's really simple but it's an example off the
--top of my head so fuck it, I'm leaving it here
example (p q r: Prop) (h: p → q → r) : q → p → r := fun hq hp => h hp hq
