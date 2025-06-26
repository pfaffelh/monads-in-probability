import Mathlib

open ENNReal

def coin (p : ℝ≥0∞) (hp : p ≤ 1) : PMF Bool := PMF.bernoulli p hp

example (p : ℝ≥0∞) (h : p ≤ 1) : coin p h = do let X ← coin p h; return X := by
  simp only [bind_pure]

section binomial

noncomputable def B (n : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1):= PMF.binomial p hp n

-- Now we can write `B n p hp` for the usual binomial distribution.






universe u v w






example (m : Type u → Type v) {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : (do return ← x) = x
  := by exact (bind_pure x)

example (m : Type u → Type v) {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = x
  := by exact (bind_pure x)

#check bind_pure (PMF.bernoulli _ _)

variable {α β : Type u}

section some_notation

-- Dirac measure

notation "δ" => PMF.pure -- for the Dirac measure

example (a : α) : δ a = do return ← pure a := by
  simp only [bind_pure]
  rfl

-- map

infixl:100 "ₓ" => PMF.map

-- Now we can write `f ₓ ℙ` for the image PMF of `ℙ` under `f`.
-- This is usually denoted `PMF.map f ℙ` or `f <$> ℙ`.

example (ℙ : PMF α) (f : α → β) : f ₓ ℙ = PMF.map f ℙ := rfl

example (ℙ : PMF α) (f : α → β) : f ₓ ℙ = f <$> ℙ := rfl

-- bind

infixl:100 "∘" => PMF.bind

-- Now we can write `ℙ ₓ κ` for the image PMF of `ℙ` under a kernel `κ`.
-- This is usually denoted `PMF.bind ℙ κ` or `ℙ >>= κ`.

example (ℙ : PMF α) (κ : α → PMF β) : ℙ ∘ κ = ℙ.bind κ := by rfl

example (ℙ : PMF α) (κ : α → PMF β) : ℙ >>= κ = ℙ.bind κ := by rfl

variable (f : α → β) (x : α)

example : f ₓ (δ x) = δ (f x) := by
  exact PMF.pure_map f x

@[simp] theorem LawfulMonad.map_pure' [Monad m] [LawfulMonad m] {a : α} :
    (f <$> pure a : m β) = pure (f a) := by
  simp only [map_pure]







P ⊗ κ

-- abbreviation for map
example (a : PMF α) (f : α → β) : a.map f = f <$> a := rfl

end some_notation

example (a : PMF α) (f : α → β) : f <$> a = do
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

noncomputable def binom'' (n : ℕ) : PMF ℕ := do
  let mut result := 0
  for _ in [1:n] do
    let X ← coin p h
    result := result + X.toNat
  return result

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
