import Mathlib

open ENNReal

noncomputable def coin (p : ℝ≥0∞) (h : p ≤ 1) : PMF Bool := PMF.bernoulli p h

example (p : ℝ≥0∞) (h : p ≤ 1) : PMF.bernoulli p h = do return ← PMF.bernoulli p h
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
