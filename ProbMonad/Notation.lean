import Mathlib

open ENNReal

universe u v
variable {α β : Type u}
variable {γ : Type v}

section some_notation

-- `PMF.pure`: Dirac measure

notation "δ" => PMF.pure -- for the Dirac measure

@[simp]
lemma do_delta (a : α) : (do return ← PMF.pure a) = δ a := PMF.bind_pure (δ a)

-- map

infixl:100 "ₓ" => PMF.map

-- Now we can write `f ₓ ℙ` for the image PMF of `ℙ` under `f`.
-- This is usually denoted `PMF.map f ℙ` or `f <$> ℙ`.

lemma map_def (ℙ : PMF α) (f : α → β) : PMF.map f ℙ  = f ₓ ℙ := rfl

-- The next two lemmas require that `α` and `β` live in the same universe!
lemma do_map (ℙ : PMF α) (f : α → β) :
  (do let X ← ℙ; return f X) = f ₓ ℙ := rfl

lemma map_def' (ℙ : PMF α) (f : α → β) : f ₓ ℙ = f <$> ℙ := rfl

-- bind

infixl:100 "∘" => PMF.bind

-- Now we can write `ℙ ₓ κ` for the image PMF of `ℙ` under a kernel `κ`.
-- This is usually denoted `PMF.bind ℙ κ` or `ℙ >>= κ`.

lemma bind_def (ℙ : PMF α) (κ : α → PMF β) : ℙ ∘ κ = ℙ.bind κ := by rfl

-- Again, this notation requires that `α` and `β` live in the same universe!
lemma bind_def' (ℙ : PMF α) (κ : α → PMF β) : ℙ >>= κ = ℙ.bind κ := by rfl

@[simp]
lemma do_bind (ℙ : PMF α) (κ : α → PMF β) :
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

lemma do_join (ℙ : PMF (PMF α)) : (do let P ← ℙ; let X ← P; return X) = join ℙ := by
  rw [do_bind]
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

lemma map_id (ℙ : PMF α) : id ₓ ℙ = ℙ := by
  exact PMF.map_id ℙ

lemma map_map (ℙ : PMF α) (f : α → β) (g : β → γ) : g ₓ (f ₓ ℙ) = (g ∘ f) ₓ ℙ := by
  exact PMF.map_comp f ℙ g

lemma bind_const (ℙ : PMF α) (ℙ' : PMF β) : ℙ ∘ (Function.const _ ℙ') = ℙ' := by
  exact PMF.bind_const ℙ ℙ'


-- (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
--   (p.bind f).bind g = p.bind fun a ↦ (f a).bind g

lemma bind_bind (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Z ← ((κ X) ∘ κ'); return Z) := by
  simp only [bind_pure]
  rfl

lemma do_bind_bind (ℙ : PMF α) (κ κ' : α → PMF α) : (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) = ℙ ∘ (fun a ↦ κ a ∘ κ') := by
  rw [bind_bind, do_bind]

lemma do_bind_bind' (ℙ : PMF α) (κ κ' : α → PMF α) : (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (ℙ ∘ κ) ∘ κ' := by
  rw [do_bind, do_bind]

lemma bind_bind' (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Z ← ((κ X) ∘ κ'); return Z) := by
  rw [do_bind, do_bind, do_bind, PMF.bind_bind]



lemma map_const (ℙ : PMF α) (b : β) : (Function.const _ b) ₓ ℙ = δ b := by
  have h : (Function.const α b) = (Function.const α b) ∘ id := by sorry
  rw [h, ← map_map, bind_const]


  exact PMF.map_const ℙ b





example (ℙ : PMF α): Function.const _ ℙ <$> ℙ = PMF.map ∘ (fun ℙ ↦ ℙ)



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
