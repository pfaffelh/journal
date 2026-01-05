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
