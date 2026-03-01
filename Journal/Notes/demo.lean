import Mathlib

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

example : ({0} : Set ℕ) = ({0} : Set ℤ) := by
  sorry

/-
# Graphs
-/

#check SimpleGraph
#print SimpleGraph



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


lemma l1 (n : ℕ) : (¬ IsEven n) ↔ ∀ k, n ≠ 2 * k := by
  simp_rw [IsEven]
  rw [dvd_iff_exists_eq_mul_right]
  push_neg
  rfl



example (n : ℕ) : IsEven n ↔ IsEven (n*n) := by
  constructor
  · intro ⟨k, hk⟩
    use k * n
    simp [hk]
    ring
  · contrapose
    intro h
    obtain h' := (l1 n).mp h
    rw [l1]
    intro k

    intro h k



    intro ⟨k, hk⟩
    by_contra
    have h : ¬ IsEven (n * n):= by sorry

    apply h


    rw [IsEven]
    apply?
    sorry
  sorry
