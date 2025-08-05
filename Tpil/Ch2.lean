--Constants
def m : Nat := 1
def n : Nat := 0
def b1 : Bool := false
def b2 : Bool := true


--Checking types
#check m
#check n
#check n + 0
#check m * (n + 0)
#check n - 1
#check b1
#check b2
#check b1 && b2
#check b1 || b2
#check !b1 && b2
#check 0
#check true

-- Evaluating some exprs

#eval m
#eval n
#eval n + 0
#eval m * (n + 0)
#eval n - 1
#eval b1
#eval b2
#eval b1 && b2
#eval b1 || b2
#eval !b1 && b2
#eval 0
#eval true

#check Nat → Nat
#check Nat × Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat) → Nat
#check Nat.succ
#check (0, (1 : Int))
#check Nat.add
#check (0, (1 : Int)).1
#check (0, (1 : Int)).2

def α : Type := Nat
def β : Type := Bool
def f : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check f α
#check f Nat
#check G α
#check G α β
#check G α Nat

-- Type is weird my dude. There are whole universes of types that are nested infinitely
#check Type
#check Type 1
#check Type 2
#check Type 3

-- Parameterized types!
#check List
#check List Nat

#check Prod
#check Prod Nat
#check Prod Nat Nat


--Our own polymorphic types!??
universe u

def Ty (α : Type u) : Type u := Prod α α
#check Ty
#print Ty


--Don't need an explicit universe
def Ty2.{v} (a : Type v) : Type v := Prod a a

#check fun x : Nat ↦ x * 2

--equivalent forms of the same function
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def double (x : Nat) : Nat := x * 2

#eval double 234519099302101929392102942109482140984398391570957893048930480931

def add (a b : Nat) : Nat := a + b

def t (x : Nat) : Nat :=
    let y := x + x
    y * x

def compose (α β γ : Type) (g : β → γ) (f: α → β) (x : α) : γ :=
    g (f x)

def doTwice (α : Type) (f : α → α) (x : α) : α :=
    f (f x)

def doThrice (α : Type) (f : α → α) (x : α) : α :=
    f (f (f x))
