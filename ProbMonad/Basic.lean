import Mathlib

open ENNReal

def coin (p : ℝ≥0∞) (hp : p ≤ 1) : PMF Bool := PMF.bernoulli p hp

example (p : ℝ≥0∞) (h : p ≤ 1) : coin p h = do let X ← coin p h; return X := by
  simp only [bind_pure]

section binomial

noncomputable def B (n : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1):= PMF.binomial p hp n

-- Now we can write `B n p hp` for the usual binomial distribution.

open PMF



theorem binomial_recurrence (p : ℝ≥0∞) (h : p ≤ 1) (m : ℕ) (x : Fin (m+1)) (hx : 0 < x):
  (binomial p h (m+1)) (Fin.castSucc x) =
    (1 - p) * (PMF.map Fin.castSucc (binomial p h m)) (Fin.castSucc x) +
    p * (PMF.map Fin.castSucc (binomial p h m)) (Fin.castSucc (x - 1)) := by
    let p' := p.toReal
    simp [binomial_apply]
    rw [Nat.choose_succ_left _ _ hx]
    have h' : p ^ x.val * p * 2 = 0 := by sorry
    have h1 : ∑' (a : Fin (m + 1)), (if x = a then p ^ (a.val) * (1 - p) ^ (m - a.val) * ((m.choose a.val)) else 0) = (p ^ x.val * (1 - p) ^ (m - x.val) * (m.choose x.val)) := by
      sorry

    norm_cast at h1

    have h2 : ∑' (a : Fin (m + 1)), (if x - 1 = a then p ^ a.val * (1 - p) ^ (m - a.val) * (m.choose a.val) else 0) = p ^ (x - 1).val * (1 - p) ^ (m - (x.val - 1)) * (m.choose (x.val - 1)) := by sorry
    rw [h1, h2]
    sorry



universe u v w






example (m : Type u → Type v) {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : (do return ← x) = x
  := by exact (bind_pure x)

example (m : Type u → Type v) {α : Type u} [Monad m] [LawfulMonad m] (x : m α) : x >>= pure = x
  := by exact (bind_pure x)

#check PMF.bind_pure (PMF.bernoulli _ _)

variable {α β : Type u}

section some_notation

-- Dirac measure

notation "δ" => PMF.pure -- for the Dirac measure

example (a : α) : δ a = do return ← PMF.pure a := by
  exact Eq.symm (_root_.bind_pure (δ a))

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
    return (Head : Fin 2) + X

example (n m : ℕ) (k : Fin n) (l : Fin m) : (k + l).val = k.val + l.val := by
  sorry


def boolList (n : Nat) : List Bool :=
  let mut acc := []
  for i in [0:n] do
    acc := acc ++ [i % 2 == 0]
  acc


noncomputable def binom₀ (p : ENNReal) (h : p ≤ 1) (n : ℕ) : PMF ℕ := do
  let choices ← sequence <| List.replicate n (PMF.bernoulli p h)
  return choices.count true


def boolListM (n : Nat) : (List (PMF Bool)) := do
  List.range n >>= (fun i => coin p h)

noncomputable def binom_with_for (n : ℕ) : PMF (Fin (n + 1)) := do
  let mut X ← List.replicate n (coin p h)
  for i in [1:n] do
    let (X i) ← coin p h
    return X
  return result

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




example (α : Type) [MeasurableSpace α] [h : MeasurableSingletonClass α] (x : α) (f : α → ℝ) : ∫ a, f a ∂ (PMF.pure x).toMeasure = f x := by
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
