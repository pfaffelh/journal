import Mathlib

open ENNReal

open scoped Monad

universe u v
variable {α β : Type u}
variable {γ : Type v}

section some_notation

-- `PMF.pure`: Dirac measure

-- the Dirac measure
noncomputable abbrev δ : α → PMF α := PMF.pure

@[simp]
lemma do_delta (a : α) : (do let X ← PMF.pure a; return X) = δ a := bind_pure (δ a)

@[simp]
lemma do_bind_delta (a : α) : (do let X ← PMF.pure a; PMF.pure X) = δ a := bind_pure (δ a)

-- map

infixl:100 "ₓ" => PMF.map

-- Now we can write `f ₓ ℙ` for the image PMF of `ℙ` under `f`.
-- This is usually denoted `PMF.map f ℙ` or `f <$> ℙ`.

@[simp]
lemma map_def (ℙ : PMF α) (f : α → β) : PMF.map f ℙ = f <$> ℙ := rfl

lemma map_pure (f : α → β) (a : α) : f <$> (δ a) = δ (f a) := by
  exact PMF.pure_map f a

-- The next two lemmas require that `α` and `β` live in the same universe!
@[simp]
lemma do_map (ℙ : PMF α) (f : α → β) :
  (do let X ← ℙ; PMF.pure (f X)) = f ₓ ℙ := rfl

lemma PMF.pure_eq_pure (a : α) : δ a = (pure a : PMF α) := by rfl

section Pi

noncomputable def PMF.piFin : {n : ℕ} → (Fin n → PMF α) → PMF (Fin n → α)
| 0, _ => PMF.pure (fun x => nomatch x)  -- es gibt kein x : Fin 0
| n + 1, ℙ => do
  let X₀ ← PMF.piFin (fun i => ℙ i.castSucc)
  let X' ← ℙ ⟨n, lt_add_one n⟩
  return (fun i => dite (i < n) (fun h ↦ X₀ ⟨i.val, h⟩) (fun _ ↦ X'))

noncomputable def PMF.pi {ι α : Type} [Fintype ι]
  (ℙ : ι → PMF α) : PMF (ι → α) :=
  do
    let n := Fintype.card ι
    let e : ι ≃ Fin n := Fintype.equivFin ι
    let X ← PMF.piFin (fun i => ℙ (e.symm i))
    return (fun i => X (e i))

end Pi

-- show independence!

/-


noncomputable def PMF.prod {n : ℕ} (ℙ : Fin n → PMF α) : PMF (Fin n → α) :=(do let X ← sequence (f := PMF) ℙ; PMF.pure X)



infixl:71 "⊗" => PMF.prod


@[simp]
lemma do_map₂ (ℙ ℙ' : PMF α) (f : α → α → β) :
  (do let X ← ℙ; let Y ← ℙ'; return f X Y) = (fun (x, y) ↦ f x y) ₓ (ℙ ⊗ ℙ') := by
    simp only [PMF.prod, bind_pure_comp]
    refine PMF.ext ?_
    intro x
    refine DFunLike.congr ?_ rfl
    rw [PMF.map]
    refine PMF.ext ?_
    intro y
    refine DFunLike.congr ?_ rfl

-/

@[simp]
lemma map_def' (ℙ : PMF α) (f : α → β) : f <$> ℙ = f ₓ ℙ := rfl

-- bind

infixl:100 "∘" => PMF.bind

-- Now we can write `ℙ ₓ κ` for the image PMF of `ℙ` under a kernel `κ`.
-- This is usually denoted `PMF.bind ℙ κ` or `ℙ >>= κ`.

lemma bind_def (ℙ : PMF α) (κ : α → PMF β) : ℙ ∘ κ = ℙ.bind κ := by rfl

-- Again, this notation requires that `α` and `β` live in the same universe!
lemma bind_def' (ℙ : PMF α) (κ : α → PMF β) : ℙ >>= κ = ℙ.bind κ := by rfl

@[simp]
lemma do_bind (ℙ : PMF α) (κ : α → PMF β) :
  (do let X ← ℙ; κ X) = (ℙ ∘ κ) := rfl

@[simp]
lemma do_bind' (ℙ : PMF α) (κ : α → PMF β) :
  (do let X ← ℙ; let Y ← κ X; return Y) = (ℙ ∘ κ) := bind_congr (fun _ ↦ bind_pure _)

-- seq

--   In a monad, `mf <*> mx` is the same as
-- `do let f ← mf; x ← mx; pure (f x)`.
noncomputable def seq (ℙ : PMF α) (ℙ' : PMF (α → β)) : PMF β := PMF.seq ℙ' ℙ

-- This feels like evaluating the process `X ← ℙ'` at the random time `T ← ℙ`.
lemma do_seq (ℙ : PMF α) (ℙ' : PMF (α → β)) : (do let X ← ℙ'; let T ← ℙ; return X T) = (ℙ' <*> ℙ) := by rfl


-- join

-- I would call `join ℙ` the first moment measure of the random measure `ℙ`.
noncomputable def join (ℙ : PMF (PMF α)) : PMF α := ℙ ∘ id

@[simp]
lemma do_join (ℙ : PMF (PMF α)) : (do let P ← ℙ; let X ← P; return X) = join ℙ := by
  rw [do_bind']
  rfl

-- Let us look at the laws for `LawfulMonad PMF`.

/- instance : LawfulFunctor PMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)
-/

@[simp]
lemma bind_pure_comp (ℙ : PMF α) (f : α → β) : ℙ >>= (fun y => δ (f y)) = (f <$> ℙ) := rfl

lemma id_map (ℙ : PMF α) : id <$> ℙ = ℙ := by
  exact PMF.map_id ℙ

@[simp]
lemma pure_bind (x : α) (κ : α → PMF α) : δ x ∘ κ = κ x := by
  exact PMF.pure_bind x κ

@[simp]
lemma bind_assoc (ℙ : PMF α) (κ κ' : α → PMF α) : (ℙ ∘ κ) ∘ κ' = ℙ ∘ fun a ↦ κ a∘κ' := by
  exact PMF.bind_bind ℙ κ κ'

@[simp]
lemma map_id (ℙ : PMF α) : id ₓ ℙ = ℙ := by
  exact PMF.map_id ℙ

lemma map_map (ℙ : PMF α) (f : α → β) (g : β → γ) : g ₓ (f ₓ ℙ) = (g ∘ f) ₓ ℙ := by
  exact PMF.map_comp f ℙ g

@[simp]
lemma bind_const (ℙ : PMF α) (ℙ' : PMF β) : ℙ ∘ (Function.const _ ℙ') = ℙ' := by
  exact PMF.bind_const ℙ ℙ'


-- (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
--   (p.bind f).bind g = p.bind fun a ↦ (f a).bind g
@[simp]
lemma bind_bind (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Z ← ((κ X) ∘ κ'); return Z) := by
  simp only [bind_pure]
  rfl

lemma do_bind_bind (ℙ : PMF α) (κ κ' : α → PMF α) : (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) = ℙ ∘ (fun a ↦ κ a ∘ κ') := by
  rw [bind_bind, do_bind']

lemma do_bind_bind' (ℙ : PMF α) (κ κ' : α → PMF α) : (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (ℙ ∘ κ) ∘ κ' := by
  rw [do_bind', do_bind']

lemma bind_bind' (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Z ← ((κ X) ∘ κ'); return Z) := by
  rw [do_bind', do_bind', do_bind', PMF.bind_bind]

lemma bind_bind'' (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) := by
  simp only [bind_pure]
  exact LawfulMonad.bind_assoc ℙ (fun X ↦ κ X) fun Y ↦ κ' Y


open NNReal

section one_coin

variable (p : ℝ≥0) (h : p ≤ 1)

def coin : PMF Bool := PMF.bernoulli p h

lemma coin_apply_true : coin p h true = p := rfl

lemma coin_apply_false : coin p h false = 1 - p := rfl

example : (1 : ℝ≥0∞) = (if (false = false) then (1 : ℝ≥0∞) else (0 : ℝ≥0∞)) := by rfl

-- lemma coin_mix : coin p h = (1 - p) * (δ false) + p * (δ true) := by sorry

example : (0 : ℝ≥0∞) ≤ 1 := by
  exact zero_le_one' ℝ≥0∞

lemma coin_zero_eq_pure : coin (0 : ℝ≥0) (zero_le_one' ℝ≥0) = δ false := by
  ext x
  obtain h₀ | h₁ := x
  · rw [coin_apply_false, PMF.pure_apply]
    simp
  · rw [coin_apply_true, PMF.pure_apply]
    simp

lemma coin_one_eq_pure : coin (1 : ℝ≥0) rfl.le = δ true := by
  ext x
  cases' x
  · rw [coin_apply_false, PMF.pure_apply]
    simp
  · rw [coin_apply_true, PMF.pure_apply]
    simp

@[simp]
lemma zero_le_one_sub : 1 - p ≤ 1 := by
  exact tsub_le_self

@[simp]
lemma pureTrue_of_false : (PMF.pure true) false = 0 := by
  refine PMF.pure_apply_of_ne true false ?_
  simp

@[simp]
theorem pure_apply_self' {α : Type*} (a : α) : PMF.pure a a = 1 :=
  if_pos rfl

open scoped Classical in
@[simp]
theorem PMF.map_apply' {α : Type} (f : α → α) (p : PMF α) (b : α) : (f ₓ p) b = ∑' a, if b = f a then p a else 0 := by
  rw [← PMF.map_apply]

lemma coin_not : not ₓ coin p h = coin (1-p) (zero_le_one_sub _) := by
  simp only [PMF.map, coin]
  ext x
  cases' x <;> simp [tsum_bool, ENNReal.sub_sub_cancel one_ne_top h]

lemma coin_not' : (do let X ← coin p h; return (not X)) = coin (1-p) (zero_le_one_sub _) := by
  rw [do_bind]
  exact coin_not p h

lemma square_le_one_of_le_one (p : ℝ≥0∞) (h : p ≤ 1): p^2 ≤ 1 := by
  refine pow_le_one₀ (zero_le p) h

lemma ENNReal.add_cancel {a b c : ℝ≥0∞} (h' : c ≤ b) (ha : a ≠ ∞) (hb : b ≠ ∞) : a + (b - c) = a + b - c := by
  refine ENNReal.eq_sub_of_add_eq' ?_ ?_
  · exact Finiteness.add_ne_top ha hb
  · have g : (b - c) + c = b := by
      exact tsub_add_cancel_of_le h'
    rw [add_assoc, g]

variable (p₁ p₂ : ℝ≥0) (hp₁ : p₁ ≤ 1) (hp₂ : p₂ ≤ 1)

lemma two_coins_and : ((coin p₁ hp₁) >>= (fun (X : Bool) ↦ X.and <$> coin p₂ hp₂)) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  simp only [map_def', do_bind]
  ext x
  simp [coin, tsum_bool]
  cases' x
  · simp only [cond_false, ↓reduceIte, Bool.false_eq_true, add_zero]
    rw [tsub_add_cancel_of_le hp₂, ENNReal.mul_sub (fun _ _ => (lt_of_le_of_lt hp₁ one_lt_top).ne), mul_one, mul_one, add_cancel, tsub_add_cancel_of_le hp₁]
    · exact mul_le_of_le_one_right' hp₂
    · exact sub_ne_top one_ne_top
    · exact (lt_of_le_of_lt hp₁ one_lt_top).ne
  · simp only [Bool.true_eq_false, ↓reduceIte, add_zero, mul_zero, zero_add, cond_true]

lemma two_coins_and' :
  (do
    let X ← coin p₁ hp₁;
    let Y ← coin p₂ hp₂;
    return (X ∧ Y)
  ) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  simp only [Bool.decide_and, Bool.decide_eq_true, do_bind]
  exact two_coins_and p₁ p₂ hp₁ hp₂

lemma two_coins :
  (do
    let X ← coin p₁ hp₁;
    let Y ← coin p₂ hp₂;
    return (X, Y)
  ) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  simp only [Bool.decide_and, Bool.decide_eq_true, do_bind]
  exact two_coins_and p₁ p₂ hp₁ hp₂

end one_coin

section n_coins

variable {n : ℕ} (p : Fin n → ℝ≥0∞) (hp : ∀ i, p i ≤ 1)

noncomputable def PMF.bernoulliChain : PMF (Fin n → Bool) := PMF.piFin (fun i ↦ coin (p i) (hp i))

theorem bernoulliChain_ext (x : Fin n → Bool): PMF.bernoulliChain p hp x = ∏ (i : Fin n), (p i) ^ (x i).toNat * (1 - p i) ^ (not (x i)).toNat := by
  induction n with
  | zero =>
    simp only [PMF.bernoulliChain, PMF.piFin, Finset.univ_eq_empty, Finset.prod_empty]
    simp at *
    exact List.ofFn_inj.mp rfl
  | succ n hn =>
    simp only [PMF.bernoulliChain, PMF.piFin, do_bind] at hn ⊢



    sorry

  sorry

noncomputable def bernoulli_chain : PMF (List Bool) :=
  sequence <| List.ofFn (fun (i : Fin n) ↦ (coin (p i) (hp i)))

def bernoulli_chain' : PMF (List Bool) :=
  | zero => δ []
  | succ n hn => ((bernoulli_chain' p hp) >>= (fun (X : Bool) ↦ X.and <$> coin p₂ hp₂))

  sequence <| List.ofFn (fun (i : Fin n) ↦ (coin (p i) (hp i)))



lemma two_coins : ((coin p₁ hp₁) >>= (fun (X : Bool) ↦ X.and <$> coin p₂ hp₂)) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  sorry

lemma eq_pure_iff {α : Type} (ℙ : PMF α) (a : α) : ℙ = δ a ↔ (ℙ a = 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact h ▸ pure_apply_self' a
  · ext x
    by_cases h' : x = a
    · rw [h', h]
      simp only [PMF.pure_apply, ↓reduceIte]
    · simp only [PMF.pure_apply, h', ↓reduceIte]
      refine (PMF.apply_eq_zero_iff ℙ x).mpr ?_
      rw [(PMF.apply_eq_one_iff ℙ a).mp h]
      simp [h']

lemma bernoulli_chain_zero (hn : n = 0) : bernoulli_chain p hp = δ [] := by
  simp [eq_pure_iff, bernoulli_chain, hn, sequence, pure]

lemma le_one_of_all_le_one (hp : ∀ i, p i ≤ 1) : ∏ i, p i ≤ 1 := Fintype.prod_le_one hp

lemma all_of_emptyList : (fun x ↦ List.all x id) [] = true := by simp only [List.all_nil]

lemma bernoulli_chain_all (n : ℕ) (p : Fin n → ℝ≥0∞) (hp : ∀ i, p i ≤ 1) : PMF.map (fun x ↦ List.all x id) (bernoulli_chain p hp) = coin (∏ (i : Fin n), p i) (Fintype.prod_le_one hp) := by
  induction n with
  | zero =>
    simp [bernoulli_chain_zero, PMF.pure_map, coin_one_eq_pure]
  | succ n hn =>

    sorry

lemma n_coins (n : ℕ) (p : Fin n → ℝ≥0∞) (hp : ∀ i, p i ≤ 1) :
  (do
    let X ← bernoulli_chain p hp
    PMF.pure (X.all (· = true))
  ) = coin (∏ (i : Fin n), p i) (Fintype.prod_le_one hp) := by
  simp only [Bool.decide_eq_true, do_bind, _root_.bind_pure_comp, ← bernoulli_chain_all n p hp]
  rfl

lemma n_coins' (n : ℕ) {N : Type} [Fintype N] :
  (do
    let mut X ← 0
    for i in List.finRange n do
      X [i] ← coin p h

    return X.all (· = true)
  ) = coin (p^n) (pow_le_one₀ (zero_le p) h) := by
  sorry

end n_coins

namespace PMF

end PMF



open ENNReal

variable (p : ℝ≥0) (h : p ≤ 1)

namespace PMF

def coin (p : ℝ≥0) (h : p ≤ 1) : PMF Bool := PMF.bernoulli p h

lemma add_lt_of_fin_of_bool {n : ℕ} (k : Fin n) (l : Bool) : k + l.toNat < n + 1 := Nat.add_lt_add_of_lt_of_le k.prop (Bool.toNat_le l)

noncomputable def binomial₀ (p : ℝ≥0) (h : p ≤ 1) : (n : ℕ) → PMF (Fin (n + 1))
  | 0 => do let X ← PMF.pure 0; return X
  | n+1 => do
    let Head ← coin p h
    let X ← binomial₀ p h n
    return ⟨X + Head.toNat, add_lt_of_fin_of_bool _ _⟩

theorem binomial₀_eq_binomial : binomial₀ = binomial := by
  ext p h n k
  simp [binomial, binomial₀]
  induction n with
  | zero =>
    simp [binomial, binomial₀]
    exact Fin.fin_one_eq_zero k
  | succ n hn =>
    simp_rw [binomial₀] at *
    rw [do_bind]







    rw [PMF.map_apply]
    simp [bind_map]



    sorry
  sorry

  simp [binomial, binomial₀]

  rw [PMF.bind_apply]

  simp [binomial, binomial₀]
  rw [binomial₀, pure_bind]
  sorry

end PMF


open NNReal

example (p : ℝ≥0) (h : p ≤ 1) : PMF.bernoulli p h = do return ← PMF.bernoulli p h
  :=  by simp only [bind_pure]

universe u v w

example (m : Type u → Type v) {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : (do return ← x) = x
  := by exact (bind_pure x)

example (m : Type u → Type v) {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = x
  := by exact (bind_pure x)

#check bind_pure (PMF.bernoulli _ _)

variable {α β : Type u}

example (a : PMF α) (f : α → β) : a.map f = do
    let X ← a
    return f X
  := by
    rfl

example (p : ℝ≥0∞) (h : p ≤ 1) : PMF.bernoulli p h = do
    have h' : 1 - p ≤ 1 := by simp
    let Head ← PMF.bernoulli (1-p) h'
    return !Head
  := by
  simp only [bind_pure_comp]
  have h' : 1 - p ≤ 1 := by simp
  have h_map : PMF.map (fun a : Bool ↦ !a) (PMF.bernoulli (1 - p) h') = PMF.bernoulli p h := by
    simp [PMF.map]
    ext x
    cases' x
    · simp
      rw [tsum_bool]
      simp
    · simp
      rw [tsum_bool]
      simp
      refine ENNReal.sub_sub_cancel one_ne_top h
  rw [← h_map]
  rfl

example (p : ℝ≥0∞) (h : p ≤ 1) : (do let X ← PMF.bernoulli p h return X) = do
    have h' : 1 - p ≤ 1 := by simp
    let Head ← PMF.bernoulli (1-p) h'
    return !Head
  := by
  simp only [bind_pure_comp]
  have h' : 1 - p ≤ 1 := by simp
  have h_map : PMF.map (fun a : Bool ↦ !a) (PMF.bernoulli (1 - p) h') = PMF.bernoulli p h := by
    simp [PMF.map]
    ext x
    cases' x
    · simp
      rw [tsum_bool]
      simp
    · simp
      rw [tsum_bool]
      simp
      refine ENNReal.sub_sub_cancel one_ne_top h
  rw [← h_map, bind_pure]
  rfl

variable (p : ℝ≥0∞) (h : p ≤ 1)

noncomputable def binom : (n : ℕ) → PMF ℕ
  | 0 => PMF.pure 0
  | n+1 => do
    let Head ← coin p h
    let X ← binom n
    return Head.toNat + X


noncomputable def binom' (p : ℝ≥0∞) (h : p ≤ 1) : (n : ℕ) → PMF (Fin (n+1))
  | 0 => PMF.pure 0
  | n+1 => do
    let Head ← coin p h
    let X ← binom p h n
    return Head.toNat + X

example (n : ℕ) : binom' p h n= PMF.binomial p h n := by
  induction n with
  | zero =>
    ext y
    cases' y with a ha
    have h' : a = 0 := by sorry
    simp_rw [h']
    simp
    simp [binom']
  | succ n hn =>

    sorry




example (α : Type) [MeasurableSpace α] [h : MeasurableSingletonClass α] (x : α) (f : α → ℝ) :∫ a, f a ∂ (PMF.pure x).toMeasure = f x := by
  rw [PMF.toMeasure_pure]
  simp only [MeasureTheory.integral_dirac]


example (p : ℝ≥0∞) (h : p ≤ 1) (n : ℕ) : ∫ a, id (a : ℝ) ∂ (binom p h n).toMeasure = n * p.toReal := by
  induction n
  · simp [binom]
    simp_rw [PMF.toMeasure_pure]
    simp only [MeasureTheory.integral_dirac, CharP.cast_eq_zero]
  · simp only [binom, LawfulMonad.bind_pure_comp, id_eq, Nat.cast_add, Nat.cast_one] at *

--    rw [integral_eq_tsum _ _ _ ] at * -- , PMFmapmap_eq_map]
    sorry

/--
This does not work, probably because Measure is not a real Monad, but something weaker.
noncomputable instance : Monad MeasCat.Measure where
  pure a := pure a
  bind pa pb := pa.bind pb

noncomputable def Mpure (α : MeasCat) (P : MeasureTheory.Measure α) : (MeasureTheory.Measure α) := do
    let X ← P
    return X
-/
