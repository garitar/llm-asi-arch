import TMS2Cleanroom.Coupling

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

open Dist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Positive residual after removing common mass. -/
def positiveResidual (p q : Dist α) (h : 0 < tv p q) : Dist α where
  mass a := pos (p a - q a) / tv p q
  nonneg a := div_nonneg (pos_nonneg _) (le_of_lt h)
  sum_mass := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change tvPos p q * (tv p q)⁻¹ = 1
    rw [← tv_eq_tvPos]
    exact mul_inv_cancel₀ (ne_of_gt h)

/-- Negative residual after removing common mass. -/
def negativeResidual (p q : Dist α) (h : 0 < tv p q) : Dist α where
  mass a := pos (q a - p a) / tv p q
  nonneg a := div_nonneg (pos_nonneg _) (le_of_lt h)
  sum_mass := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change tvPos q p * (tv p q)⁻¹ = 1
    rw [← tv_eq_tvPos, tv_symm q p]
    exact mul_inv_cancel₀ (ne_of_gt h)

lemma residual_difference (p q : Dist α) (h : 0 < tv p q) (a : α) :
    tv p q * (positiveResidual p q h a - negativeResidual p q h a) = p a - q a := by
  have hne : tv p q ≠ 0 := ne_of_gt h
  simp only [positiveResidual, negativeResidual]
  field_simp [hne]
  have hp := pos_sub_pos_neg (p a - q a)
  convert hp using 1 <;> ring_nf

lemma push_difference_residual (p q : Dist α) (K : Kernel α β)
    (h : 0 < tv p q) (b : β) :
    push p K b - push q K b =
      tv p q * (push (positiveResidual p q h) K b - push (negativeResidual p q h) K b) := by
  simp only [push_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd := residual_difference p q h a
  calc
    p a * K a b - q a * K a b = (p a - q a) * K a b := by ring
    _ = tv p q * ((positiveResidual p q h a - negativeResidual p q h a) * K a b) := by
      rw [← hd]
      ring
    _ = tv p q *
        (positiveResidual p q h a * K a b - negativeResidual p q h a * K a b) := by ring

lemma tv_push_eq_scaled_residual (p q : Dist α) (K : Kernel α β)
    (h : 0 < tv p q) :
    tv (push p K) (push q K) =
      tv p q * tv (push (positiveResidual p q h) K) (push (negativeResidual p q h) K) := by
  unfold tv
  simp_rw [push_difference_residual p q K h]
  have ht : |tv p q| = tv p q := abs_of_pos h
  simp_rw [abs_mul, ht]
  rw [← Finset.mul_sum]
  ring

/-- Dobrushin contraction from any declared uniform pairwise row bound. -/
theorem tv_push_le_mul_of_pairwise_le (p q : Dist α) (K : Kernel α β) (c : ℝ)
    (hc : ∀ i j, tv (K i) (K j) ≤ c) :
    tv (push p K) (push q K) ≤ c * tv p q := by
  by_cases hzero : tv p q = 0
  · have hpq : p = q := (tv_eq_zero_iff p q).mp hzero
    subst q
    simp
  · have hpos : 0 < tv p q := lt_of_le_of_ne (tv_nonneg p q) (Ne.symm hzero)
    rw [tv_push_eq_scaled_residual p q K hpos]
    calc
      tv p q * tv (push (positiveResidual p q hpos) K)
          (push (negativeResidual p q hpos) K)
          ≤ tv p q * c := by
            exact mul_le_mul_of_nonneg_left
              (tv_push_le_of_pairwise_le
                (positiveResidual p q hpos) (negativeResidual p q hpos) K c hc)
              (le_of_lt hpos)
      _ = c * tv p q := by ring

end TMS2Cleanroom
