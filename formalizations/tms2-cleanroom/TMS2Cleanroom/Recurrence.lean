import Mathlib

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

/-- Recursive chronological accumulation of per-step innovations. -/
def weightedBound (c : ℝ) (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => e n + c * weightedBound c e n

/-- Explicit chronological weighted sum. -/
def weightedSum (c : ℝ) (e : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ k in Finset.range t, c ^ (t - 1 - k) * e k

lemma weightedSum_succ (c : ℝ) (e : ℕ → ℝ) (n : ℕ) :
    weightedSum c e (n + 1) = e n + c * weightedSum c e n := by
  unfold weightedSum
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_mul]
  have hsum :
      (∑ k ∈ Finset.range n, c ^ (n - k) * e k) =
        c * (∑ k ∈ Finset.range n, c ^ (n - 1 - k) * e k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hexp : n - k = (n - 1 - k) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [hsum]
  ring

lemma weightedBound_eq_sum (c : ℝ) (e : ℕ → ℝ) :
    ∀ t, weightedBound c e t = weightedSum c e t := by
  intro t
  induction t with
  | zero => simp [weightedBound, weightedSum]
  | succ n ih =>
      rw [weightedBound, weightedSum_succ, ih]

/-- Nonnegative affine recurrences are bounded by their weighted innovation sum. -/
theorem recurrenceBound (c : ℝ) (e d : ℕ → ℝ)
    (hc : 0 ≤ c)
    (h0 : d 0 = 0)
    (hstep : ∀ n, d (n + 1) ≤ e n + c * d n) :
    ∀ t, d t ≤ weightedSum c e t := by
  intro t
  rw [← weightedBound_eq_sum c e t]
  induction t with
  | zero => simp [weightedBound, h0]
  | succ n ih =>
      calc
        d (Nat.succ n) ≤ e n + c * d n := by
          simpa [Nat.succ_eq_add_one] using hstep n
        _ ≤ e n + c * weightedBound c e n := by
          exact add_le_add_left (mul_le_mul_of_nonneg_left ih hc) (e n)
        _ = weightedBound c e (Nat.succ n) := by
          simp [weightedBound, Nat.succ_eq_add_one]

end TMS2Cleanroom
