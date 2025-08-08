namespace chapter_material
section
--You can start tactics mode from the nat number game with by. Really useful
--when constructing a proof
theorem test1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test1

--Put multiple tactics on a line with `;`
theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

--And use `case` to explicitly pick which thing to work on if there are multiple
theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

--There's also this weird bullet notation. For when you want the structure from
--the cases but don't want to explicitly name them in the proof. It actually
--naturally aligns things so hey, cool
theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h.right
    . intro hq
      left
      exact And.intro h.left  hq
    . intro hr
      right
      exact And.intro h.left hr
  . intro h
    apply Or.elim h
    . intro h
      exact And.intro h.left (Or.inl h.right)
    . intro h
      exact And.intro h.left (Or.inr h.right)

example (α : Type) : α → α := by
  intro a
  exact a

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h1 h2
  exact Eq.trans (Eq.symm h2) h1

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩


variable (x y z w : Nat)

--Assumption will look for a hypothesis that'll solve it
example (h1 : x = y) (h2 : y = z) (h3 : z = w) : x = w := by
  apply Eq.trans h1
  apply Eq.trans h2
  assumption

--and it'll magically unify metavariables
example (h1 : x = y) (h2 : y = z) (h3 : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h1
  apply Eq.trans
  assumption      -- solves y = ?h1.b with h2
  assumption      -- solves z = w with h3

--Let's try it
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

-- Intro has a reverse, revert
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

--There's a generalize tool
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

--careful not to get too cocky with generalize. Provide a name to generalize to
--remember and undo what you did
example : 2 + 3 = 5 := by
  generalize h: 3 = x
  rw [← h]


end
end chapter_material

namespace exercises
section One
section Ch3
section One
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
apply Iff.intro
. intro hpq
  exact ⟨hpq.right, hpq.left⟩
. intro hqp
  exact ⟨hqp.right, hqp.left⟩

example : p ∨ q ↔ q ∨ p := by
apply Iff.intro
. intro hp_or_q
  apply Or.elim hp_or_q
  . intro hp; right; assumption
  . intro hq; left; assumption
. intro hq_or_p
  apply Or.elim hq_or_p
  . intro hq; right; assumption
  . intro hp; left; assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    exact ⟨h.left.left, h.left.right, h.right⟩
  . intro h
    constructor
    constructor
    exact h.left
    exact h.right.left
    exact h.right.right
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro h
      apply Or.elim h
      . intro hp
        left; assumption
      . intro hq
        right; left; assumption
    . intro hr
      right;right; assumption
  . intro h
    apply Or.elim h
    . intro hp
      left; left; assumption
    . intro h
      apply Or.elim h
      . intro hq
        left; right; assumption
      . intro hr
        right; assumption



-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    have hp := h.left
    apply Or.elim h.right
    . intro hq; left; exact ⟨hp, hq⟩
    . intro hr; right; exact ⟨hp, hr⟩
  . intro h
    apply Or.elim h
    . intro hpq
      exact ⟨hpq.left, Or.inl hpq.right⟩
    . intro hpr
      exact ⟨hpr.left, Or.inr hpr.right⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp
      exact ⟨Or.inl hp, Or.inl hp⟩
    . intro hqr
      exact ⟨Or.inr hqr.left, Or.inr hqr.right⟩
  . intro h
    have hpq:= h.left
    have hpr:= h.right
    apply Or.elim hpq
    . intro hp; exact Or.inl hp
    . intro hq
      apply Or.elim hpr
      . intro hp; exact Or.inl hp
      . intro hr; exact Or.inr ⟨hq,hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h
    intro hpq
    exact h hpq.left hpq.right
  . intro h
    intros hp hq
    exact h ⟨hp, hq⟩
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hp
      apply h (Or.inl hp)
    . intro hq
      apply h (Or.inr hq)
  intro h
  have hpr := h.left
  have hqr := h.right
  intro h
  apply Or.elim h
  . exact hpr
  . exact hqr
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply And.intro
    . apply Classical.byContradiction
      intro hnnp
      have hp := Classical.not_not.mp hnnp
      have hp_or_q : p ∨ q := Or.inl hp
      exact h hp_or_q
    . apply Classical.byContradiction
      intro hnnq
      have hq := Classical.not_not.mp hnnq
      exact h (Or.inr hq)
  intro ⟨hnp, hnq⟩
  apply Classical.byContradiction
  intro h
  have h := Classical.not_not.mp h
  apply Or.elim h
  intro;contradiction
  intro;contradiction



example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  apply Classical.byContradiction
  intro ha
  have hpq := Classical.not_not.mp ha
  have hp := hpq.left
  have hq := hpq.right
  apply Or.elim h
  . intro hnp
    contradiction
  . intro hnq
    contradiction


example : ¬(p ∧ ¬p) := by
  apply Classical.byContradiction
  intro h
  have h := Classical.not_not.mp h
  exact h.right h.left

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩
  apply Classical.byContradiction
  intro h
  have h := Classical.not_not.mp h
  exact hnq (h hp)
example : ¬p → (p → q) := by
  intro hnp
  intro hp
  apply False.elim (hnp hp)
example : (¬p ∨ q) → (p → q) := by
  intro h
  apply Or.elim h
  . intro hnp hp
    contradiction
  . intro hq _
    exact hq
example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp; exact hp
    . intro hfalse; exact False.elim hfalse
  . intro hp
    exact Or.inl hp

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro h
    exact h.right
  . intro h
    exact And.intro (False.elim h) h

example : (p → q) → (¬q → ¬p) := by
  intro hpq
  intro hnq
  apply Classical.byContradiction
  intro h
  have hp := Classical.not_not.mp h
  have hq := hpq hp
  exact hnq hq
end One
section Two
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases em p with
  | inl hp => cases h hp with
    |inl hq =>
      left
      intro _
      assumption
    |inr hr =>
      right
      intro _
      assumption
  | inr hnp =>
    left
    intro hp
    contradiction

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp => right; intro hq; exact h ⟨hp, hq⟩
  | inr hnp => left; assumption
example : ¬(p → q) → p ∧ ¬q := by
  intro h
  have hnq: ¬q := by
      intro hq
      apply h
      intro
      exact hq
  cases em p with
  | inl hp => exact  ⟨hp, hnq⟩
  | inr hnp =>
    have hpq : p → q:= by
      intro hp
      contradiction
    contradiction

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases em p with
  | inl hp  =>
    right
    exact h hp
  | inr hnp =>
    left
    exact hnp
example : (¬q → ¬p) → (p → q) := by
  intro h
  cases em q with
  | inl hq =>
    intro _
    assumption
  | inr hnq =>
    have hnp := h hnq
    intro h
    contradiction
example : p ∨ ¬p := by
  cases em p with
  | inl h => left; assumption
  |inr h => right; assumption

example : (((p → q) → p) → p) := by
  intro h
  apply byContradiction
  intro hnp
  have hpq : p → q := by intro h; contradiction
  have hp := h hpq
  contradiction

end Two
end Ch3
section Ch4
section One
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    constructor
    . intro ha
      exact (h ha).left
    . intro ha
      exact (h ha).right
  . intros h ha
    exact ⟨h.left ha , h.right ha⟩
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intros h1 h2 ha
  exact h1 ha (h2 ha)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intros h ha
  apply Or.elim h
  . intro h; left; exact h ha
  . intro h; right; exact h ha
end One
section Two
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    constructor
    . intro ha; exact (h ha).left
    . intro ha; exact (h ha).right
  . intros h ha; exact ⟨h.left ha, h.right ha⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intros h1 h2 ha
  exact h1 ha (h2 ha)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  apply Or.elim h
  . intros h ha
    left; exact h ha
  . intros h ha
    right; exact h ha

end Two

section Three
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h := h barber
  have hmp := h.mp
  have hmpr := h.mpr
  have hnsbb: ¬shaves barber barber := by
    intro h;
    have hn := hmp h
    contradiction
  have hsbb: shaves barber barber := by
    exact hmpr hnsbb
  contradiction

end Three

section Five
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro ⟨_, hr⟩
  assumption
example (a : α) : r → (∃ _ : α, r) := by
  intro h;
  exact ⟨a, h⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨ha, h⟩
    exact ⟨⟨ha, h.left⟩, h.right⟩
  . intro ⟨⟨ha, hpa⟩, hr⟩
    exact ⟨ha, hpa, hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro ⟨ha , hpa_or_qa⟩
    apply Or.elim hpa_or_qa
    . intro hpa
      exact Or.inl ⟨ha, hpa⟩
    . intro hqa
      exact Or.inr ⟨ha, hqa⟩
  . intro h
    apply Or.elim h
    . intro ⟨ha, hpa⟩
      exact ⟨ha, Or.inl hpa⟩
    . intro ⟨ha, hqa⟩
      exact ⟨ha, Or.inr hqa⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply byContradiction
    intro hc
    have ⟨ha, hnp⟩ := not_not.mp hc
    exact hnp (h ha)
  . intros h a
    apply byContradiction
    intro npa
    apply h
    exists a

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro ⟨ha , hpa⟩
    apply byContradiction
    intros hc
    have hanp := not_not.mp hc
    exact (hanp ha) hpa
  . intro hnanpx
    apply byContradiction
    intro hnpx
    apply hnanpx
    intro a hpa
    apply hnpx
    exists a


example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
constructor
case mp =>
  intros h a
  apply byContradiction
  intro hpa
  have hpa:= not_not.mp hpa
  apply h
  exists a
case mpr =>
  intro h
  apply byContradiction
  intro hc
  have ⟨a, hpa⟩ := not_not.mp hc
  have hnpa := h a
  contradiction

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
constructor
. intro h
  apply byContradiction
  intro hc
  apply h
  intro a
  apply byContradiction
  intro hnpa
  have hnc: ∃ x, ¬ p x := ⟨a,hnpa⟩
  contradiction

. intro ⟨a, hnpa⟩
  apply byContradiction
  intro hc
  have hpa := not_not.mp hc a
  contradiction

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
constructor
. intro h ⟨a, hpa⟩
  exact h a hpa
. intro h a pa
  exact h ⟨a,pa⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro ⟨a, ha⟩ h
    exact ha (h a)
  . intro h
    cases em r with
    | inl hr =>
      exists a
      intro
      assumption
    | inr hnr =>
      have hnap : ¬∀ x, p x := by
        intro hap
        apply hnr
        exact h hap
      have hexnp : ∃ x, ¬p x := by
        apply byContradiction
        intro hnexnp
        apply hnap
        intro b
        apply byContradiction
        intro hnpb
        apply hnexnp
        exists b
      have ⟨a, hnpa⟩ := hexnp
      exists a
      intro
      contradiction


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
constructor
. intro ⟨b, hb⟩ hr
  exact ⟨b, hb hr⟩
. intro h
  cases em r with
  | inl hr =>
    have ⟨a, ha⟩ := h hr
    exists a
    intro hr
    assumption
  | inr hnr =>
    exists a
    intro
    contradiction


end Five
end Ch4
end One
section Two
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro| left;assumption| right | assumption)
end Two
end exercises
