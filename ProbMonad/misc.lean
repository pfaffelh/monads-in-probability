import Mathlib


structure MyMonad (α : Type u) : Type (u+1) where
  run : α → Bool  -- Dummy example

def MyBind' {α β : Type u} (ma : MyMonad α) (f : α → MyMonad β) : MyMonad β :=
  sorry  -- Your implementation here

class MyBind (M : Type u → Type v) where
  bind : ∀ {α β}, M α → (α → M β) → M β

infixl:55 " >>>= " => MyBind.bind


open Lean Elab Macro Term

syntax (name := mydo) "mydo " doSeq : term

-- Recursive macro
macro_rules
  -- Case: x ← a; rest
  | `(mydo ($x:ident ← $a:term); $rest:doSeq) =>
    `(bind $a (fun $x => mydo $rest))

  -- Case: final expression
  | `(mydo $e:term) => `($e)


open Lean Elab Macro Term Meta

-- Step 1: Define the syntax
syntax (name := mydo) "mydo " doSeq : term

-- Step 2: Macro rules for desugaring
macro_rules
  -- match: x ← a; ... (recursively transform the rest)
  | `(mydo ($x:ident ← $a:term; $rest:doSeq)) =>
    `(bind $a (fun $x => mydo $rest))

  -- match: pure expression as final statement
  | `(mydo $e:term) => `($e)


open Lean Elab Term Meta

syntax (name := mydo) "mydo " doSeq : term
syntax (name := mydoLet) ident " ← " term : doElem
syntax (name := mydoRet) term : doElem

macro_rules
  | `(mydo $x:ident ← $a:term; $rest) =>
    `(bind $a (fun $x => mydo $rest))

  | `(mydo $e:term) => `($e)



macro_rules
  | `(mydo $x:doSeq) => expandMyDo x

macro_rules
  | `(doElem| $x:ident ← $e:term) => `(bind $e (fun $x => _))
  | `(doElem| $e:term)            => `($e)




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
