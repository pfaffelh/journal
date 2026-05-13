import Mathlib
import Journal.Notes.DiscreteMeasure.Binomial

open MeasureTheory unitInterval
open DiscreteMeasure (coin)

/-
# Divisibility
-/

example (k n : ℕ) : k ∣ n ↔ ∃ m, n = k * m := by
  rfl

example : 3 ∣ 6 := by
  simp only [Dvd.dvd]
  use 2

example (k m n : ℕ) (hkm : k ∣ m) (hmn : m ∣ n) : k ∣ n := by
  exact Nat.dvd_trans hkm hmn

def IsEven (n : ℕ) := ∃ k, n = 2 * k

example (m n : ℕ) : IsEven m → IsEven (m * n) := by
  -- Take `k` with `hk : m = 2 * k`
  intro ⟨k, hk⟩
  -- We then need to find `l` with `m * n = 2 * l`.
  -- So, we take `k * n` in the `∃` of `IsEven`.
  use k * n
  -- New goal is `⊢ m * n = 2 * (k * n)`
  -- The rest is rewriting `m = 2 * k` and using associativity
  rw [hk, mul_assoc]


example (k n : ℤ) (h : IsRelPrime k n) : ∃ x y, x * k + y * n = 1 := by
  rw [← IsCoprime]
  exact IsRelPrime.isCoprime h

#check IsRelPrime.isCoprime
#print IsRelPrime.isCoprime



/-
# Some unintuitive examples
-/

example : 1 - 2 = 0 := by
  rfl

example : 1 - 2 = -1 := by
  rfl

example : (0 : ℕ) = (0 : ℤ) := by
  rfl

-- example : ({0} : Set ℕ) = ({0} : Set ℤ) := by
--  sorry


/-
Discrete Probability
-/

/-- The binomial distribution with parameters `p` and `n`, as a `DiscreteMeasure ℕ`. -/
noncomputable def binom (p : unitInterval) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)

theorem binom_succ (p : unitInterval) (n : ℕ) :
binom p (n + 1) =
(coin p) >>= fun X => binom p n >>= fun Y => pure (X.toNat + Y)
:= rfl

theorem binom_succ' (p : unitInterval) (n : ℕ) :
binom p (n + 1) =
(coin p).bind (fun X => (binom p n).bind (fun Y => pure (X.toNat + Y)))
:= rfl
