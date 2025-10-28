
inductive T where
  | true : T
  | false : T
  | zero : T
  | succ (t₁ : T) : T
  | pred (t₁ : T) : T
  | isZero (t₁ : T) : T
  | cond (t₁ t₂ t₃ : T) : T
  deriving DecidableEq

macro_rules
  | `(if $t₁ then $t₂ else $t₃) => `(T.cond $t₁ $t₂ $t₃)

#check T.rec

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
theorem T.zero_numeric : T.numeric 0 := by trivial

@[simp]
theorem T.succ_numeric {t : T} : t.succ.numeric ↔ t.numeric := by
  constructor <;> intro h
  · assumption
  · assumption

@[simp]
theorem T.pred_numeric {t : T} : t.succ.numeric ↔ t.numeric := by
  constructor <;> intro h
  · assumption
  · assumption

@[simp]
theorem T.false_not_numeric : ¬ T.false.numeric := by
  unfold T.numeric
  trivial

@[simp]
theorem T.true_not_numeric : ¬ T.true.numeric := by
  unfold T.numeric
  trivial

@[simp]
theorem T.isZero_not_numeric : ¬ T.numeric (.isZero t) := by
  unfold numeric
  trivial

@[simp]
theorem T.cond_not_numeric : ¬ (if t₁ then t₂ else t₃).numeric := by
  unfold numeric
  trivial

def T.bnumeric : T → Bool
  | 0 => .true
  | .succ tᵢ | .pred tᵢ => tᵢ.bnumeric
  | _ => .false



instance {t : T} : Decidable t.numeric := by
  apply decidable_of_bool t.bnumeric
  
  induction t with unfold T.bnumeric T.numeric
  | zero =>
    simp
  | pred | succ t' ih =>
    assumption
  | true | false => simp
  | cond _ _ _ _ _ _ => simp
  | isZero _ => simp

def T.toNat (t : T) (h : numeric t) : Nat :=
  match t with
  | 0 => 0
  | succ n' => by
    simp at *
    exact (n'.toNat h).succ
  | pred n' => by
    exact (n'.toNat h).pred

def T.ofBool : Bool → T
  | .true => .true
  | .false => .false

theorem T.zero_constructor : 0 = .zero := by trivial

def T.numeral : T → Prop
  | .zero => True
  | .succ t' => t'.numeral
  | _ => False

def T.bnumeral : T → Bool
  | .zero => .true
  | .succ t' => t'.bnumeral
  | _ => .false

instance : DecidablePred T.numeral := by
  intro t
  apply decidable_of_bool t.bnumeral
  induction t with unfold T.numeral T.bnumeral <;> try simp
  | succ t ih =>
    assumption

@[simp]
theorem T.succ_numeral {t : T} : t.succ.numeral ↔ t.numeral := by
  constructor <;> intro h
  · trivial
  · trivial

theorem T.numeric_of_numeral {t : T}: t.numeral → t.numeric := by
  intro h
  induction t with unfold T.numeral at h <;> try contradiction
  | zero => assumption
  | succ tᵢ ih => exact ih h


instance : Coe Bool T where
  coe := T.ofBool

attribute [coe] T.ofBool

example : T := true

example {t₁ t₂ t₃ : T} : T := if t₁ then t₂ else t₃

example : T := if 9 then 0 else 5

def T.repr (t : T) (n : Nat) : Std.Format :=
  match t with
  | true => Bool.true.repr n
  | false => Bool.false.repr n
  | 0 => Nat.zero.repr
  | succ tᵢ => by
    by_cases h : tᵢ.numeral
    · have h := T.numeric_of_numeral h
      exact (tᵢ.toNat h).succ.repr.toFormat
    · exact "succ" ++ tᵢ.repr n
  | pred tᵢ => "pred " ++ (tᵢ.repr n)
  | if t₁ then t₂ else t₃ => "if " ++ t₁.repr n ++ " then " ++ t₂.repr n ++ " else " ++ t₃.repr n
  | isZero t₁ => "isZero " ++ t₁.repr n

instance : Repr T where
  reprPrec := T.repr

#eval if .succ 0 then 0 else 0

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



    

