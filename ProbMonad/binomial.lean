import Mathlib
import ProbMonad.Notation

open ENNReal

variable (p : ℝ≥0∞) (h : p ≤ 1)

namespace PMF

def coin (p : ℝ≥0∞) (h : p ≤ 1) : PMF Bool := PMF.bernoulli p h

lemma add_lt_of_fin_of_bool {n : ℕ} (k : Fin n) (l : Bool) : k + l.toNat < n + 1 := Nat.add_lt_add_of_lt_of_le k.prop (Bool.toNat_le l)

noncomputable def binomial₀ (p : ℝ≥0∞) (h : p ≤ 1) : (n : ℕ) → PMF (Fin (n + 1))
  | 0 => do let X ← PMF.pure 0; return X
  | n+1 => do
    let Head ← coin p h
    let X ← binomial₀ p h n
    return ⟨X + Head.toNat, add_lt_of_fin_of_bool _ _⟩

theorem binomial₀_eq_binomial : binomial₀ = binomial := by
  ext p h n k
  simp [binomial, binomial₀]
  induction n with
  | zero =>
    simp [binomial, binomial₀]
    exact Fin.fin_one_eq_zero k
  | succ n hn =>
    simp_rw [binomial₀] at *
    rw [do_bind]







    rw [PMF.map_apply]
    simp [bind_map]



    sorry
  sorry

  simp [binomial, binomial₀]

  rw [PMF.bind_apply]

  simp [binomial, binomial₀]
  rw [binomial₀, pure_bind]
  sorry

end PMF
