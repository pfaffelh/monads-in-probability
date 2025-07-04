import Mathlib
import ProbMonad.Notation

open ENNReal

variable (p : ℝ≥0∞) (h : p ≤ 1)

def coin : PMF Bool := PMF.bernoulli p h

lemma coin_apply_true : coin p h true = p := rfl

lemma coin_apply_false : coin p h false = 1 - p := rfl

@[simp]
lemma zero_le_one_sub : 1 - p ≤ 1 := by
  exact tsub_le_self

lemma coin_reverse : not ₓ coin p h = coin (1-p) (zero_le_one_sub _) := by
  simp only [PMF.map, coin]
  ext x
  cases' x <;> simp [tsum_bool, ENNReal.sub_sub_cancel one_ne_top h]

lemma square_le_one_of_le_one (p : ℝ≥0∞) (h : p ≤ 1): p^2 ≤ 1 := by
  refine pow_le_one₀ (zero_le p) h

lemma two_coins :
  (do
    let X ← coin p h;
    let Y ← coin p h;
    return X ∧ Y
  ) = coin (p^2) (square_le_one_of_le_one p h) := by
  rw [PMF.bind_apply]
  simp
  refine PMF.ext ?_
  intro x
  cases' x
  · rw [coin_apply_false, coin]
    apply?
    simp [PMF.bernoulli, PMF.ofFintype, PMF.ofFinset]


    sorry
  · sorry
namespace PMF

end PMF
