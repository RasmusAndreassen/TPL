
inductive T where
  | true : T
  | false : T
  | zero : T
  | succ (t₁ : T) : T
  | pred (t₁ : T) : T
  | isZero (t₁ : T) : T
  | cond (t₁ t₂ t₃ : T) : T
  deriving DecidableEq

def T.ofNat (n : Nat) : T :=
  match n with
  | 0 => .zero
  | n' + 1 => .succ (.ofNat n')

@[default_instance]
instance : OfNat T n where
  ofNat := .ofNat n

def T.numeric : T → Prop
  | .zero => True
  | .succ n | .pred n => n.numeric
  | _ => False

@[simp]
def T.succ_numeric {t : T} : t.succ.numeric ↔ t.numeric := by
  constructor <;> intro h
  · assumption
  · assumption

@[simp]
def T.pred_numeric {t : T} : t.succ.numeric ↔ t.numeric := by
  constructor <;> intro h
  · assumption
  · assumption

def T.toNat (t : T) {_ : numeric t} : Nat :=
  match t with
  | 0 => 0
  | succ n' => by
    simp at *
    exact n'.toNat
  | pred n' => by
    have := pred_numeric h
    exact t.toNat.pred



def T.ofBool (b : Bool) : T
  := if b then .true else .false

theorem T.zero_constructor : 0 = .zero := by trivial
  

instance : Coe Bool T where
  coe := T.ofBool

attribute [coe] T.ofBool

example : T := true

macro_rules
  | `(if $t₁ then $t₂ else $t₃) => `(T.cond $t₁ $t₂ $t₃)

example {t₁ t₂ t₃ : T} : T := if t₁ then t₂ else t₃

example : T := if 9 then 0 else 5



def T.repr (t : T) (n : Nat) : Std.Format :=
  match t with
  | true => Bool.true.repr n
  | false => Bool.false.repr n
  | 0 => t.toNat.repr
  | succ _ => t.toNat.repr
  | pred _ => t.toNat.repr
  | if t₁ then t₂ else t₃ => "if " ++ t₁.repr n ++ " then " ++ t₂.repr n ++ " else " ++ t₃.repr n
  | isZero t₁ => "isZero " ++ t₁.repr n

instance : Repr T where
  reprPrec := T.repr

def T.derives_to (t t' : T) : Prop :=
  match t with
  | 0 => False
  | true => False
  | false => False
  | if t₁ then t₂ else t₃ =>
    match t₁ with
    | true => t' = t₂
    | false => t' = t₃
    | t₁ => ∃ t₁', t₁.derives_to t₁' ∧ t' = if t₁' then t₂ else t₃
  | _ => False


infix:200 " → " => T.derives_to

instance : DecidableRel (α := T) (· → ·) := by
  intro t
  induction t using ?_ with


    

#eval 0 → 0

