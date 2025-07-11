import Mathlib
import ProbMonad.Notation

open ENNReal

section one_coin

variable (p : ℝ≥0∞) (h : p ≤ 1)

def coin : PMF Bool := PMF.bernoulli p h

lemma coin_apply_true : coin p h true = p := rfl

lemma coin_apply_false : coin p h false = 1 - p := rfl

example : (1 : ℝ≥0∞) = (if (false = false) then (1 : ℝ≥0∞) else (0 : ℝ≥0∞)) := by rfl

-- lemma coin_mix : coin p h = (1 - p) * (δ false) + p * (δ true) := by sorry

example : (0 : ℝ≥0∞) ≤ 1 := by
  exact zero_le_one' ℝ≥0∞

lemma coin_zero_eq_pure : coin (0 : ℝ≥0∞) (zero_le_one' ℝ≥0∞) = δ false := by
  ext x
  cases' x
  · rw [coin_apply_false, PMF.pure_apply, tsub_zero]
    simp
  · rw [coin_apply_true, PMF.pure_apply]
    simp

lemma coin_one_eq_pure : coin (1 : ℝ≥0∞) rfl.le = δ true := by
  ext x
  cases' x
  · rw [coin_apply_false, PMF.pure_apply]
    simp
  · rw [coin_apply_true, PMF.pure_apply]
    simp

@[simp]
lemma zero_le_one_sub : 1 - p ≤ 1 := by
  exact tsub_le_self

@[simp]
lemma pureTrue_of_false : (PMF.pure true) false = 0 := by
  refine PMF.pure_apply_of_ne true false ?_
  simp

@[simp]
theorem pure_apply_self' {α : Type*} (a : α) : PMF.pure a a = 1 :=
  if_pos rfl

open scoped Classical in
@[simp]
theorem PMF.map_apply' {α : Type} (f : α → α) (p : PMF α) (b : α) : (f ₓ p) b = ∑' a, if b = f a then p a else 0 := by
  rw [← PMF.map_apply]

lemma coin_not : not ₓ coin p h = coin (1-p) (zero_le_one_sub _) := by
  simp only [PMF.map, coin]
  ext x
  cases' x <;> simp [tsum_bool, ENNReal.sub_sub_cancel one_ne_top h]

lemma coin_not' : (do let X ← coin p h; return (not X)) = coin (1-p) (zero_le_one_sub _) := by
  rw [do_bind]
  exact coin_not p h

lemma square_le_one_of_le_one (p : ℝ≥0∞) (h : p ≤ 1): p^2 ≤ 1 := by
  refine pow_le_one₀ (zero_le p) h

lemma ENNReal.add_cancel {a b c : ℝ≥0∞} (h' : c ≤ b) (ha : a ≠ ∞) (hb : b ≠ ∞) : a + (b - c) = a + b - c := by
  refine ENNReal.eq_sub_of_add_eq' ?_ ?_
  · exact Finiteness.add_ne_top ha hb
  · have g : (b - c) + c = b := by
      exact tsub_add_cancel_of_le h'
    rw [add_assoc, g]

variable (p₁ p₂ : ℝ≥0∞) (hp₁ : p₁ ≤ 1) (hp₂ : p₂ ≤ 1)

example : p₁ ≠ ⊤ := by
  apply (lt_of_le_of_lt hp₁ one_lt_top).ne

lemma two_coins_and : ((coin p₁ hp₁) >>= (fun (X : Bool) ↦ X.and <$> coin p₂ hp₂)) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  simp only [map_def', do_bind]
  ext x
  simp [coin, tsum_bool]
  cases' x
  · simp only [cond_false, ↓reduceIte, Bool.false_eq_true, add_zero]
    rw [tsub_add_cancel_of_le hp₂, ENNReal.mul_sub (fun _ _ => (lt_of_le_of_lt hp₁ one_lt_top).ne), mul_one, mul_one, add_cancel, tsub_add_cancel_of_le hp₁]
    · exact mul_le_of_le_one_right' hp₂
    · exact sub_ne_top one_ne_top
    · exact (lt_of_le_of_lt hp₁ one_lt_top).ne
  · simp only [Bool.true_eq_false, ↓reduceIte, add_zero, mul_zero, zero_add, cond_true]

lemma two_coins_and' :
  (do
    let X ← coin p₁ hp₁;
    let Y ← coin p₂ hp₂;
    return (X ∧ Y)
  ) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  simp only [Bool.decide_and, Bool.decide_eq_true, do_bind]
  exact two_coins_and p₁ p₂ hp₁ hp₂

lemma two_coins :
  (do
    let X ← coin p₁ hp₁;
    let Y ← coin p₂ hp₂;
    return (X, Y)
  ) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  simp only [Bool.decide_and, Bool.decide_eq_true, do_bind]
  exact two_coins_and p₁ p₂ hp₁ hp₂

end one_coin

section n_coins

variable {n : ℕ} (p : Fin n → ℝ≥0∞) (hp : ∀ i, p i ≤ 1)

noncomputable def PMF.bernoulliChain : PMF (Fin n → Bool) := PMF.piFin (fun i ↦ coin (p i) (hp i))

theorem bernoulliChain_ext (x : Fin n → Bool): PMF.bernoulliChain p hp x = ∏ (i : Fin n), (p i) ^ (x i).toNat * (1 - p i) ^ (not (x i)).toNat := by
  induction n with
  | zero =>
    simp only [PMF.bernoulliChain, PMF.piFin, Finset.univ_eq_empty, Finset.prod_empty]
    simp at *
    exact List.ofFn_inj.mp rfl
  | succ n hn =>
    simp only [PMF.bernoulliChain, PMF.piFin, do_bind] at hn ⊢



    sorry

  sorry

noncomputable def bernoulli_chain : PMF (List Bool) :=
  sequence <| List.ofFn (fun (i : Fin n) ↦ (coin (p i) (hp i)))

def bernoulli_chain' : PMF (List Bool) :=
  | zero => δ []
  | succ n hn => ((bernoulli_chain' p hp) >>= (fun (X : Bool) ↦ X.and <$> coin p₂ hp₂))

  sequence <| List.ofFn (fun (i : Fin n) ↦ (coin (p i) (hp i)))



lemma two_coins : ((coin p₁ hp₁) >>= (fun (X : Bool) ↦ X.and <$> coin p₂ hp₂)) = coin (p₁ * p₂) (Left.mul_le_one hp₁ hp₂) := by
  sorry

lemma eq_pure_iff {α : Type} (ℙ : PMF α) (a : α) : ℙ = δ a ↔ (ℙ a = 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact h ▸ pure_apply_self' a
  · ext x
    by_cases h' : x = a
    · rw [h', h]
      simp only [PMF.pure_apply, ↓reduceIte]
    · simp only [PMF.pure_apply, h', ↓reduceIte]
      refine (PMF.apply_eq_zero_iff ℙ x).mpr ?_
      rw [(PMF.apply_eq_one_iff ℙ a).mp h]
      simp [h']

lemma bernoulli_chain_zero (hn : n = 0) : bernoulli_chain p hp = δ [] := by
  simp [eq_pure_iff, bernoulli_chain, hn, sequence, pure]

lemma le_one_of_all_le_one (hp : ∀ i, p i ≤ 1) : ∏ i, p i ≤ 1 := Fintype.prod_le_one hp

lemma all_of_emptyList : (fun x ↦ List.all x id) [] = true := by simp only [List.all_nil]

lemma bernoulli_chain_all (n : ℕ) (p : Fin n → ℝ≥0∞) (hp : ∀ i, p i ≤ 1) : PMF.map (fun x ↦ List.all x id) (bernoulli_chain p hp) = coin (∏ (i : Fin n), p i) (Fintype.prod_le_one hp) := by
  induction n with
  | zero =>
    simp [bernoulli_chain_zero, PMF.pure_map, coin_one_eq_pure]
  | succ n hn =>

    sorry

lemma n_coins (n : ℕ) (p : Fin n → ℝ≥0∞) (hp : ∀ i, p i ≤ 1) :
  (do
    let X ← bernoulli_chain p hp
    PMF.pure (X.all (· = true))
  ) = coin (∏ (i : Fin n), p i) (Fintype.prod_le_one hp) := by
  simp only [Bool.decide_eq_true, do_bind, _root_.bind_pure_comp, ← bernoulli_chain_all n p hp]
  rfl

lemma n_coins' (n : ℕ) {N : Type} [Fintype N] :
  (do
    let mut X ← 0
    for i in List.finRange n do
      X [i] ← coin p h

    return X.all (· = true)
  ) = coin (p^n) (pow_le_one₀ (zero_le p) h) := by
  sorry

end n_coins

namespace PMF

end PMF
