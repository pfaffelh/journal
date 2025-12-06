import Mathlib

open NNReal ENNReal

noncomputable def binom₀ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF ℕ := do
  let choices ← sequence <| List.replicate n (PMF.bernoulli p h)
  return choices.count true


theorem binom_support (p : NNReal) (h0 : 0 < p) (h1 : p < 1) (n : ℕ) :
    (binom₀ p h1.le n).support = Set.Iic n := by
  have : 0 < 1 - p := tsub_pos_of_lt h1
  have h1' : 1 - p ≠ 0 := (ne_of_lt this).symm
  have h0' : p ≠ 0 := h0.ne.symm
  ext i
  simp [binom₀, PMF.monad_map_eq_map]
  constructor
  · rintro ⟨xs, h, rfl⟩
    contrapose! h
    induction n generalizing xs with
    | zero =>
      simp only [List.replicate_zero]
      rw [sequence, Traversable.map_eq_traverse_id]
      simp [List.sequence_nil, PMF.monad_pure_eq_pure]
      rintro rfl
      simp at h
    | succ n ih =>
      simp [List.replicate, List.sequence_cons, PMF.monad_map_eq_map, PMF.monad_seq_eq_seq]
      simp [h1', h0']
      rintro f ys rfl
      rw [or_iff_not_imp_left, not_and_or, not_not, not_not]
      rintro (rfl | rfl)
      · apply ih
        simp at h
        omega
      · apply ih
        simp at h
        omega
  · intro h
    use (List.replicate (n - i) false ++ List.replicate i true)
    simp [List.count_replicate]
    induction n with
    | zero =>
      simp [List.sequence_nil, PMF.monad_pure_eq_pure]
      omega
    | succ n ih =>
      simp [List.replicate, List.sequence_cons, PMF.monad_map_eq_map, PMF.monad_seq_eq_seq]
      simp [h1', h0']
      rw [Nat.le_add_one_iff] at h
      obtain h | rfl := h
      · specialize ih h
        use List.cons false
        use (List.replicate (n - i) false ++ List.replicate i true)
        simp [ih]
        have : n + 1 - i = n - i + 1 := Nat.sub_add_comm h
        simp [this, List.replicate]
      · use List.cons true
        use List.replicate n true
        simp [List.replicate]
        clear ih
        induction n with
        | zero =>
          simp [List.sequence_nil, PMF.monad_pure_eq_pure]
        | succ n ih =>
          simp [List.replicate, List.sequence_cons, PMF.monad_map_eq_map, PMF.monad_seq_eq_seq]
          use List.cons true
          use List.replicate n true
          simp [h0', ih]
