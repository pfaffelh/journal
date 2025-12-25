


section example_prod

noncomputable def prod {α β : Type u} (μ : DiscreteMeasure α) (q : α →  DiscreteMeasure β) : DiscreteMeasure (α × β) := (μ.bind fun X => (q X).bind fun Y => Pure.pure (X, Y))

lemma prod_eq {α β : Type u} (μ : DiscreteMeasure α) (q : α →  DiscreteMeasure β) : prod μ q =
  do
    let X ← μ
    let Y ← q X
    return (X, Y)
 := by
  rw [prod]
  rw [bind_eq_bind]
  simp_rw [bind_eq_bind]

lemma prod_weight {α β : Type u} (μ : DiscreteMeasure α) (q : α →  DiscreteMeasure β) (a : α) (b : β): (prod μ q).weight (a, b) = μ.weight a * (q a).weight b := by
  rw [prod]
  simp_rw [← pure_eq_pure]
  rw [bind_weight]
  simp_rw [bind_weight, pure_weight]
  have h (a' : α) (b' : β) : ({(a', b')} : Set (α × β)).indicator (1 : α × β → ℝ≥0∞) (a, b) = (({a'} : Set α).indicator (1 : α → ℝ≥0∞) a) * (({b'} : Set β).indicator (1 : β → ℝ≥0∞) b) := by
    simp only [Set.indicator]
    aesop
  conv => left; left; intro a'; right; left; intro b'; right; rw [h]
  simp_rw [← mul_assoc]
  conv => left; left; intro a1; right; left; intro b1; rw [mul_assoc, mul_comm, mul_assoc]
  simp_rw [ENNReal.tsum_mul_left]
  conv => left; left; intro a'; right; right; conv => left; intro i; rw [Set.indicator_comm_singleton]; ; conv => left; intro i; rw [mul_comm]; ; simp
  conv => left; left; intro a'; rw [mul_comm, mul_assoc] ; rw [Set.indicator_comm_singleton, mul_comm]; simp
  simp_rw [Set.indicator.mul_indicator_eq (f := fun a' ↦ (q a').weight b * μ.weight a'), mul_comm]
  simp

noncomputable def pi {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) : DiscreteMeasure (α × β) :=
prod μ (fun _ ↦ ν)

lemma pi_eq {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) : pi μ ν = (μ.map Prod.mk).seq (fun _ ↦ ν) := by
  rw [seq_eq_seq, map_eq_map]
  simp [monad_norm]
  rfl

lemma pi_eq' {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) : pi μ ν = ((pure Prod.mk).seq (fun _ ↦ μ)).seq fun _ ↦ ν := by
  rw [pi_eq, pure_eq_pure, seq_eq_seq, seq_eq_seq, seq_eq_seq, map_eq_map]
  simp [monad_norm]

lemma pi_weight {α β : Type u} (μ : DiscreteMeasure α) (ν : DiscreteMeasure β) (a : α) (b : β): (pi μ ν).weight (a,b) = (μ.weight a) * (ν.weight b) := by
  rw [pi, prod_weight]

end example_prod




















-- noncomputable def binom₂' (p : ℝ≥0) (h : p ≤ 1) : (n : ℕ) → DiscreteProbabilityMeasure (Fin (n+1)) := fun n ↦ (sequence <| List.replicate n (coin p h)).map (List.count true)

def List.count' {α : Type u} [BEq α] (a : α) (n : ℕ) : (l : List α) → (hl : l.length = n) → Fin (n + 1) := fun l hl ↦ ⟨l.count a, by
  apply lt_of_le_of_lt List.count_le_length (hl ▸ lt_add_one l.length)⟩

noncomputable def binom₅ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : DiscreteProbabilityMeasure (Fin (n + 1)) := by
  have f : (List.replicate n (coin p h)).length = n := by exact List.length_replicate
  let l := (sequence <| List.replicate n (coin p h))


  -- have l := (sequence <| List.replicate n (coin p h)).map (List.count' true)

  sorry



























section combinatorics

-- TODO: This should hold in greater generality, but is actually not so easy to prove...
--private lemma List.length_eq_sum_count_of_bool (l : List Bool) : l.length = ∑' (a : Bool), l.count a := by
--  rw [← List.count_true_add_count_false, tsum_bool, add_comm]


open scoped BigOperators

variable (n k : ℕ)

def BoolLists := { l : List Bool | l.length = n ∧ l.count true = k }

def TruePositions := { s : Finset (Fin n) | s.card = k }

end combinatorics


example (f g : α → ℝ≥0∞) : ∑' (a : α), (f a + g a) = ∑' (a : α), f a + ∑' (a : α), g a := by
  exact ENNReal.tsum_add

example (a b : α) : a = b ↔ b ∈ ({a} : Set α) := by
  simp only [Set.mem_singleton_iff]
  exact comm

example (f : α → ℝ≥0) (b : α) : ∑' (a : α), f a = f b + (∑' (a : α), if a = b then 0 else f a) := by
  apply NNReal.tsum_eq_add_tsum_ite

example (f : α → ℝ≥0∞) (b : α) : ∑' (a : α), f a = f b + (∑' (a : α), if a = b then 0 else f a) := by
  apply ENNReal.tsum_eq_add_tsum_ite

@[simp]
lemma List.count_eq_tsum_indicator [BEq α] [DecidableEq α] (l : List α) {b : α} : l.count b = ∑ (i : Fin (l.length)), ({l[i.val]} : Set α).indicator 1 b := by
  -- simp [List.count, List.countP]



  rw [List.count_eq_length_filter]


  -- rw [tsum_subtype]
  simp_rw [Set.indicator]
  conv => right; right; intro x; simp only [Set.mem_singleton_iff, Pi.one_apply]
  simp only [Finset.sum_boole, Nat.cast_id]


  induction l with
  | nil => simp
  | cons a l hl =>
    rw [List.count_cons, hl]
    conv => right; right; simp only [List.length_cons]






    sorry
#check List.count_eq_length_filter

lemma List.length_eq_tsum_count (l : List α) : l.length = ∑' (a : α), l.count a := by
  calc
    l.length = ∑' (i : Fin (l.length)), 1 := by
      simp
    _ = ∑' (i : Fin (l.length)) (a : α), ({l[i]} : Set α).indicator 1 a := by
      apply tsum_congr (fun b ↦ ?_)
      rw [← tsum_subtype]
      simp
    _ = ∑' (a : α), ∑' (i : Fin (l.length)), ({l[i]} : Set α).indicator 1 a := by
      -- apply Summable.tsum_comm
      sorry
    _ = ∑' (a : α), l.count a := by
      apply tsum_congr (fun b ↦ ?_)
      simp
noncomputable def binom₀ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF ℕ := do
  let choices ← sequence <| List.replicate n (PMF.bernoulli p h)
  return choices.count true

noncomputable def binom₁ (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF ℕ := (sequence <| List.replicate n (PMF.bernoulli p h)).map (List.count true)


noncomputable def prodList (l : List (DiscreteMeasure α)) :
    DiscreteMeasure (List α) :=
l.foldr
  (fun μ rest => μ.bind (fun a => rest.map (fun as => a :: as)))
  (pure [])



noncomputable def prodList' (v : List (DiscreteMeasure α))
  : DiscreteMeasure (List α) := v.traverse id
