import TMS2Cleanroom.DobrushinCoeff
import TMS2Cleanroom.Innovation
import TMS2Cleanroom.Recurrence

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

open Dist

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Micro distribution after `n` transitions. -/
def microAt (P : Kernel X X) (μ₀ : Dist X) (n : ℕ) : Dist X :=
  iterate P n μ₀

/-- Actual coarse distribution induced by micro dynamics. -/
def actualAt (C : X → Y) (P : Kernel X X) (μ₀ : Dist X) (n : ℕ) : Dist Y :=
  map C (microAt P μ₀ n)

/-- Autonomous macro prediction. -/
def predictedAt (C : X → Y) (Q : Kernel Y Y) (μ₀ : Dist X) (n : ℕ) : Dist Y :=
  iterate Q n (map C μ₀)

/-- Occupancy-weighted one-step coarse innovation. -/
def epsilonAt (C : X → Y) (P : Kernel X X) (Q : Kernel Y Y)
    (μ₀ : Dist X) (n : ℕ) : ℝ :=
  ∑ x, microAt P μ₀ n x * tv (map C (P x)) (Q (C x))

/-- Coarse prediction error at horizon `n`. -/
def distanceAt (C : X → Y) (P : Kernel X X) (Q : Kernel Y Y)
    (μ₀ : Dist X) (n : ℕ) : ℝ :=
  tv (actualAt C P μ₀ n) (predictedAt C Q μ₀ n)

/-- One-step TMS2 recurrence. -/
theorem distanceAt_succ_le
    (C : X → Y) (P : Kernel X X) (Q : Kernel Y Y)
    (μ₀ : Dist X) (n : ℕ) :
    distanceAt C P Q μ₀ (n + 1) ≤
      epsilonAt C P Q μ₀ n + dobrushin Q * distanceAt C P Q μ₀ n := by
  calc
    distanceAt C P Q μ₀ (n + 1)
        = tv (map C (push (microAt P μ₀ n) P))
            (push (predictedAt C Q μ₀ n) Q) := rfl
    _ ≤ tv (map C (push (microAt P μ₀ n) P))
          (push (map C (microAt P μ₀ n)) Q) +
        tv (push (map C (microAt P μ₀ n)) Q)
          (push (predictedAt C Q μ₀ n) Q) :=
        tv_triangle _ _ _
    _ ≤ epsilonAt C P Q μ₀ n + dobrushin Q * distanceAt C P Q μ₀ n := by
        exact add_le_add
          (occupancyInnovation C (microAt P μ₀ n) P Q)
          (tv_push_le_dobrushin_mul
            (actualAt C P μ₀ n) (predictedAt C Q μ₀ n) Q)

/-- Full finite TMS2 horizon bound with the exact finite Dobrushin coefficient. -/
theorem finiteTMS2
    (C : X → Y) (P : Kernel X X) (Q : Kernel Y Y)
    (μ₀ : Dist X) (t : ℕ) :
    distanceAt C P Q μ₀ t ≤
      weightedSum (dobrushin Q) (epsilonAt C P Q μ₀) t := by
  apply recurrenceBound
  · exact dobrushin_nonneg Q
  · simp [distanceAt, actualAt, predictedAt, microAt]
  · exact distanceAt_succ_le C P Q μ₀

end TMS2Cleanroom
