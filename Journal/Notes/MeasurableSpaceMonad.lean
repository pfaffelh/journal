import Mathlib

open MeasureTheory Measure ProbabilityTheory Function

/- Define the `MeasurableSpaceMonad` -/

universe u v w

class MeasurableSpaceBind (m : (α : Type u) → MeasurableSpace α → Type v) where
  bind {α β : Type u} [σα : MeasurableSpace α] [σβ : MeasurableSpace β] :
    m α σα → (α → m β σβ) → m β σβ

class MeasurableSpacePure (f : (α : Type u) → MeasurableSpace α → Type v) where
  pure {α : Type u} [σα : MeasurableSpace α] : α → f α σα

class MeasurableSpaceFunctor (f : (α : Type u) → MeasurableSpace α → Type v) :
    Type (max (u+1) v) where
  map {α β : Type u} [σα : MeasurableSpace α] [σβ : MeasurableSpace β] :
    (α → β) → f α σα → f β σβ
  mapConst {α β : Type u} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] :
    α → f β mβ → f α mα := Function.comp map (const _)

class MeasurableSpaceSeq (f : (α : Type u) → MeasurableSpace α → Type v) :
    Type (max (u+1) v) where
  seq {α β : Type u} [σα : MeasurableSpace α] [σβ : MeasurableSpace β] :
    f (α → β) (by infer_instance) → (Unit → f α σα) → f β σβ

class MeasurableSpaceSeqLeft (f : (α : Type u) → MeasurableSpace α → Type v) :
    Type (max (u+1) v) where
  seqLeft {α β : Type u} [σα : MeasurableSpace α] [σβ : MeasurableSpace β] :
    f α σα → (Unit → f β σβ) → f α σα

class MeasurableSpaceSeqRight (f : (α : Type u) → MeasurableSpace α → Type v) :
    Type (max (u+1) v) where
  seqRight {α β : Type u} [σα : MeasurableSpace α] [σβ : MeasurableSpace β] :
    f α σα → (Unit → f β σβ) → f β σβ

class MeasurableSpaceApplicative (f : (α : Type u) → MeasurableSpace α → Type v)
    extends MeasurableSpaceFunctor f, MeasurableSpacePure f, MeasurableSpaceSeq f,
      MeasurableSpaceSeqLeft f, MeasurableSpaceSeqRight f where
  map      := fun g μ ↦  seq (pure g) fun _ ↦ μ
  seqLeft  := fun μ ν ↦ seq (map (const _) μ) ν
  seqRight := fun μ ν ↦ seq (map (const _ id) μ) ν

class MeasurableSpaceMonad (m : (α : Type u) → MeasurableSpace α → Type v) :
    Type (max (u+1) v) extends MeasurableSpaceApplicative m, MeasurableSpaceBind m where
  map f μ      := bind μ (comp pure f)
  seq μf ν     := bind μf fun y ↦ map y (ν ())
  seqLeft μ ν  := bind μ fun a ↦ bind (ν ()) (fun _ ↦ pure a)
  seqRight μ ν := bind μ fun _ ↦ ν ()

/- Define Measure Instance -/

noncomputable instance : MeasurableSpaceMonad Measure where
  pure := Measure.dirac
  bind := Measure.bind

/- Define Random Variable Instance -/

open RandomGen

class Seed (Ω : Type w) where
  split : Ω → Ω × Ω

instance : Seed ℕ where
  split n := let ⟨g₁, g₂⟩ := stdSplit (mkStdGen (s := n)); ⟨(stdNext g₁).1, (stdNext g₂).1⟩

def RandomVariable (Ω : Type w) [Seed Ω] [MeasurableSpace Ω] (α : Type u) [MeasurableSpace α] :=
  Ω → α

instance {Ω : Type w} [Seed Ω] [MeasurableSpace Ω] : MeasurableSpaceMonad (RandomVariable Ω) where
  pure a := fun _ ↦ a
  bind X f := fun ω ↦ let ⟨ω₁, ω₂⟩ := Seed.split ω; f (X ω₁) ω₂

/- `do_random` notation -/

open Lean Macro Elab

declare_syntax_cat do_random
declare_syntax_cat do_random_seq

syntax "return " term : do_random
syntax "let " ident " := " term ";" do_random : do_random
syntax "let " ident " ∼ " term ";" do_random : do_random
syntax term : do_random

syntax "do_random " do_random : term

partial def do_random_macro (s : Syntax) : MacroM Syntax :=
  match s with
    | `(do_random| $t:term) => `($t)
    | `(do_random| return $t:term) => `(MeasurableSpacePure.pure $t)
    | `(do_random| let $x:ident := $t:term; $d:do_random) => `(let $x := $t; do_random $d)
    | `(do_random| let $x:ident ∼ $t:term; $d:do_random) =>
        `(MeasurableSpaceBind.bind $t (fun $x ↦ do_random $d))
    | stx => Macro.throwErrorAt stx "syntax error"

macro_rules
  | `(term| do_random $d:do_random) => do_random_macro d

/- `Random Generators` -/

open unitInterval ENNReal

class HasBit (m : (α : Type) → MeasurableSpace α → Type v) where
  bit : m Bool (by infer_instance)

noncomputable instance : HasBit Measure where
  bit := (2 : ℝ≥0∞)⁻¹ • dirac 1 + (2 : ℝ≥0∞)⁻¹ • dirac 0

instance : HasBit (RandomVariable ℕ) where
  bit n := randBool (mkStdGen (s := n)) |>.1

class HasUniform (m : (α : Type u) → MeasurableSpace α → Type v) where
  interval : Type u
  σinterval : MeasurableSpace interval := by infer_instance
  uniform : m interval σinterval

instance {m : (α : Type u) → MeasurableSpace α → Type v} [HasUniform m] :
    MeasurableSpace (HasUniform.interval m) := HasUniform.σinterval

noncomputable instance : HasUniform Measure where
  interval := I
  uniform := ℙ

instance : HasUniform (RandomVariable ℕ) where
  interval := Float
  σinterval := ⊤
  uniform n := Float.ofNat ((mkStdGen (s := n)).1 - 1) / 2147483562.0

/- Examples -/

/- Non-Polymorphic Code -/

noncomputable def bernoulli_measure (p : I) : Measure ℕ := do_random
  let U ∼ ℙ;
  if U ≤ p then do_random return 1 else do_random return 0

noncomputable def binomial_measure (p : I) : ℕ → Measure ℕ
  | .zero => do_random return 0
  | .succ n => do_random
    let Xₙ ∼ binomial_measure p n;
    let X₁ ∼ bernoulli_measure p;
    return Xₙ + X₁

/- Polymorphic Code -/

variable {m : (α : Type) → [MeasurableSpace α] → Type v} [MeasurableSpaceMonad m]

variable [HasUniform m] [LE (HasUniform.interval m)]
  [h : ∀ x y : HasUniform.interval m, Decidable (x ≤ y)]

instance : LE (HasUniform.interval Measure) := by
  simpa [HasUniform.interval] using by infer_instance

instance : LE (HasUniform.interval (RandomVariable ℕ)) := by
  simpa [HasUniform.interval] using by infer_instance

instance : ∀ x y : HasUniform.interval (RandomVariable ℕ), Decidable (x ≤ y) := by
  simpa [HasUniform.interval] using by infer_instance

def bernoulli_measure' (p : HasUniform.interval m) : m ℕ := do_random
  let U ∼ HasUniform.uniform;
  if U ≤ p then do_random return 1 else do_random return 0

def binomial_measure' (p : HasUniform.interval m) : ℕ → m ℕ
  | .zero => do_random return 0
  | .succ n => do_random
    let Xₙ ∼ binomial_measure' p n;
    let X₁ ∼ bernoulli_measure' p;
    return Xₙ + X₁

/- Tests -/
open Classical in

variable {p : I} in
#check bernoulli_measure' (m := Measure) p -- Measure ℕ

#eval bernoulli_measure' (m := RandomVariable ℕ) (0.3 : Float) 3295423908 -- 0

variable {p : I} in

#eval bernoulli_measure' (m := RandomVariable ℕ) (0.4 : Float) 3295423908 -- 0

open Classical in
variable {p : I} {n : ℕ} in
#check binomial_measure' (m := Measure) p n -- Measure ℕ

#eval binomial_measure' (m := RandomVariable ℕ) (0.4 : Float) 1000 3930458 -- 319
