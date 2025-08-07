namespace chapter_material

-- So apparently we're extending what we learned in Ch3 to add equalities and
-- quantifiers

--4.1
/-
First time seeing ∀ which roughly means for all

This means that ∀ x: α, p x translates roughly to for any x of type α, p x holds.

This can also be treated as a hypothesis a: α → p a
-/

example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
    fun h z => show p z from (h z).left

--shows that a relationship r is transitive
variable (α : Type) (r: α → α → Prop)
variable (trans_r_sucky : ∀ x y z, r x y → r y z → r x z)


variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r_sucky

#check trans_r_sucky a b c

#check trans_r_sucky a b c hab

#check trans_r_sucky a b c hab hbc

variable (trans_r: ∀ {x y z}, r x y → r y z → r x z)

#check trans_r
-- These two have implicit types for z because we didn't supply a second
-- parameter from which z can be inferred
#check trans_r hab
#check trans_r hbc

#check trans_r hab hbc

-- For any x, r x x holds
variable (refl_r : ∀ x, r x x)
#check refl_r a
-- for any r x y, we have an equivalent r y x
variable (symm_r : ∀ {x y}, r x y → r y x)

example (a b c d : α) (hab : r a b) (hcb: r c b) (hcd: r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

--4.2 Equality

-- a = a
#check Eq.refl
-- a = b ↔ b = a
#check Eq.symm
-- a = c →  b = c → a = b
#check Eq.trans

-- can use @ to exclude implicit args and make the universe explicit

universe u
#check @Eq.refl.{u}
#check Eq.symm.{u}
#check @Eq.trans.{u}

example (a b c d : α) (hab : a = b) (hcb: c = b) (hcd: c = d) : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

-- Can also use the projection notation
example (a b c d : α) (hab : a = b) (hcb: c = b) (hcd: c = d) : a = d :=
  (hab.trans hcb.symm).trans hcd

variable (α β : Type)

-- refl be useful yo
example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

--So we gave it a special name: rfl
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

-- Equality allows substitution cause transitive property
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h_a_eq_b : a = b)
variable (h_f_eq_g : f = g)

-- Fun equality rules using substitution
example : f a = f b := congrArg f h_a_eq_b
example : f a = g a := congrFun h_f_eq_g a
example : f a = g b := congr h_f_eq_g h_a_eq_b

-- Got a bunch of identities I don't wanna type out
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

-- Christ. I'm not writing this out okay. I have a family who loves me. I'm just
-- gonna annotate it
example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
    -- Start with expanding via mul_add
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  --Now stack add_mul
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  --Finally, prove that it's transitive
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

--4.3

--calc is magic! Check it out, we can go point by point, showing how the
--equivalence  changes
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

-- We use this with simp and rw from the Nat Numbers Game and Ch5
example
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

-- can stack rw to happen in a row if we don't care about some intermediate
example
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

-- Hopefully we learn more about simp in Ch 5. It seems kinda magic rn
example
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]

-- Calc isn't limited to equalities! Just anything that implements Trans (UwU)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

--4.4

/- We can use the exist qualifier. In this case we say there is some value of x
that x > 0. We then synthesize the hypothesis 1 > 0 using `Nat.zero_lt_succ 0`
Finally we use `Exists.intro` with 1 and that hypothesis to show that yes, we're
good, 1 is a possible value of x where x > 0. Technically we can plug whatever
we want in place of 0 to get h but it doesn't matter -/
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

-- Plug in 0 for y and this just becomes h
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

#check Exists.intro

--There's an anonymous constructor I don't think I'll use much
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    have h := And.intro hxy hyz
    Exists.intro y h


--Exists.intro has explicit args they wanna show off. It'll *try* to magically
--pick the right one with context. Dunno if this can bite me in the ass
variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

namespace opt_guard
set_option pp.explicit true  -- display implicit arguments

#print gex1
#print gex2
#print gex3
#print gex4

end opt_guard

-- The opposite to Exists.intro is Exists.elim, allowing us to take an exists
-- hypothesis and split it into a value and a more conventional hypothesis.
-- Looks like the implicit constructor is nested and right associative. That
-- actually might be useful then. (Reminder: Right associative for an
-- operator/constructor is x y z := x (y z))
variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h fun w hw =>
    show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩

--The book draws parallels between `elim` on `Exists` and `Or`. It also draws
--parallels between ∃ and Sigma types, although ∃ relationships are props and
--Sigma types are... types. No shit

-- We do have a match statement. Thank fuuuuuuck

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ =>
  ⟨w, hw.right, hw.left⟩

-- Pattern matching let
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

--pattern matching fun
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

--Here's an example proposition. Value a isEven if there exists a value b where
--a = 2 * b.
def IsEven (a : Nat) := ∃ b, a = 2 * b

-- Lets have some fun with it! If isEven a and isEven b and a + b = c, then
-- isEven c

example (h1: IsEven a) (h2: IsEven b) (h3: a + b = c) : IsEven c :=
  let ⟨d1, hd1⟩ := h1
  let ⟨d2, hd2⟩ := h2
  Exists.intro (d1 + d2)
    (calc c
      _ = a + b := by rw [h3]
      _ = 2 * d1 + 2 * d2 := by rw [hd1,hd2]
      _ = 2 * (d1 + d2) := by rw [← Nat.mul_add])

--We can shorten
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  Classical.byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)


variable (r : Prop)
example : (∃ _ : α, r) → r := fun h => Exists.elim h fun _ ha => ha
-- I have to use a here instead of just any arbitrary value. I feel like I
-- should be able to prove it with any arbitrary value? Maybe there's an
-- alternative to `Exists.intro`?
example (a : α) : r → (∃ _ : α, r) := fun h => Exists.intro a h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
  (fun h1 => Exists.elim h1 fun x hp => ⟨⟨x, hp.left⟩, hp.right⟩  )
  (fun h2 => Exists.elim h2.left fun x hpx => ⟨x, hpx, h2.right⟩ )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
  (fun h => Exists.elim h fun x hp_or_q => Or.elim hp_or_q
    (fun hpx => Or.inl ⟨x, hpx⟩ )
    (fun hqx => Or.inr ⟨x, hqx⟩))
  fun h => Or.elim h
    (fun hxpx =>
      Exists.elim hxpx fun x hpx => ⟨x, Or.inl hpx⟩)
    fun hxqx => Exists.elim hxqx fun x hqx => ⟨x, Or.inr hqx⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
  (fun h => Classical.byContradiction fun hnnc =>
    have hc: ∃ x, ¬ p x := Classical.not_not.mp hnnc
    Exists.elim hc fun a hnpa => hnpa (h a))
  (fun h a => Classical.byContradiction fun hnpa => h ⟨a, hnpa⟩)

-- Changing these from examples to theorems because I'm not repeating myself.
-- Fuck that. Nested `byContradiction`s sounds like a nightmare and I might
-- simplify later but don't count on it

theorem not_exist_px_iff_all_npx : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro
  (fun h x=> Classical.byContradiction fun hnnc => hnnc fun hc => h ⟨x, hc⟩)
  (fun h => Classical.byContradiction fun hnnc =>
    hnnc fun hc => Exists.elim hc fun x hpx=> (h x) hpx)
theorem exists_x_px_iff_not_all_npx : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
  (fun h => Exists.elim h fun x hpx =>
    Classical.byContradiction fun hnnc => hnnc
    fun hc: ∀ x, ¬ p x => (hc x) hpx)
  (fun h => Classical.byContradiction fun hc : ¬ ∃ x, p x=>
    suffices haxnpx : ∀ x, ¬ p x from h haxnpx
    Iff.mp (not_exist_px_iff_all_npx α p) hc)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro
  (fun h => Classical.byContradiction (fun hc =>
    have h_all_nnpx:= (not_exist_px_iff_all_npx α (fun x => ¬p x)).mp hc
    have  h_all_px : ∀ x, p x := fun a => Classical.not_not.mp (h_all_nnpx a)
    h h_all_px))
  (fun h => Exists.elim h fun x hnpx => Classical.byContradiction
  fun hnnc => hnnc
    fun hc => hnpx (hc x))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
  (fun h hxpx => Exists.elim hxpx fun x hpx => h x hpx)
  (fun h a hpa => h (Exists.intro a hpa))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
  (fun h hxpx => Exists.elim h fun a hpa => hpa (hxpx a))
  (fun h => Classical.byCases
    (fun hxnp: ∃ x, ¬p x => Exists.elim hxnp (fun a hnpa =>
    ⟨a, fun hpa => absurd hpa hnpa⟩))
    (fun hnxnp=>
      have hpa : ∀ x , p x := fun a => show p a from Classical.byContradiction
        fun hnpa => show False from hnxnp ⟨a, hnpa⟩
      ⟨a , fun _ => h hpa⟩))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
  (fun h => Exists.elim h (fun a hpa hr=> Exists.intro a (hpa hr)))
  (fun h => Classical.byCases
    (fun hr: r =>
      let ⟨w, hpw⟩ := h hr
      ⟨w, fun _ => hpw⟩)
    (fun hnr => ⟨a, fun hr => absurd hr hnr⟩))


end chapter_material

namespace exercises
--1
section
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := Iff.intro
  (fun h => ⟨(fun a => (h a).left), (fun a => (h a).right)⟩)
  (fun h => (fun a => ⟨h.left a, h.right a⟩))
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := (fun h1 h2 a =>
  (h1 a) (h2 a))
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := fun h => Or.elim h
  (fun haxpx a => Or.inl (haxpx a))
  (fun haxqx a=> Or.inr (haxqx a))
end

--2
section
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := (fun a => Iff.intro
  (fun h => h a)
  (fun h _ => h))
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := Iff.intro
  (fun h => Classical.byCases
    (fun hr : r => Or.inr hr)
    (fun hnr => Or.inl (fun a =>
      have hpa_or_r := h a
      Or.elim hpa_or_r
        id
        (fun hr => absurd hr hnr))))
  (fun h => Or.elim h (fun h a => Or.inl (h a)) (fun h _ => Or.inr h))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := Iff.intro
  (fun h hr a=> h a hr)
  (fun h a hr => h hr a)
end

section three
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hnsbb : ¬shaves barber barber := (fun hsbb =>
    have hnsbb := (h barber).mp hsbb
    show False from hnsbb hsbb)
  have hsbb := (h barber).mpr hnsbb
  hnsbb hsbb
end three

section four
def even (n : Nat) : Prop := ∃ b, b * 2 = n

def prime (n : Nat) : Prop := ¬∃ a b, a * b = n

def infinitely_many_primes : Prop := ∀ a, ∃  b, prime b ∧ b > a

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ m : Nat, n = 2 ^ (2 ^ m) + 1

def infinitely_many_Fermat_primes :Prop :=
  ∀n, ∃ m, Fermat_prime m ∧ m > n

def goldbach_conjecture : Prop := ∀ n : Nat, even n → ∃ a b, a + b = n ∧ prime a ∧  prime b

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, ¬even n →
  ∃ a b c, a + b + c = n ∧ prime a ∧ prime b ∧ prime c

def Fermat's_last_theorem : Prop := ∀ n : Nat, n > 2 →
  ¬∃ a b c : Nat, a ^ n + b ^ n = c ^ n

end four
-- I did 5 in the chapter materials. Oops. Well I treated them like exercises
-- anyways. We should get better with using byCases
end exercises
