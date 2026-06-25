import TMS2Cleanroom.Composition
import TMS2Cleanroom.TV

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

open Dist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Occupancy-weighted one-step coarse-graining innovation bound. -/
theorem occupancyInnovation
    (C : α → β) (μ : Dist α) (P : Kernel α α) (Q : Kernel β β) :
    tv (map C (push μ P)) (push (map C μ) Q) ≤
      ∑ x, μ x * tv (map C (P x)) (Q (C x)) := by
  rw [map_push, push_map]
  exact tv_push_same_weights_le μ
    (fun x => map C (P x)) (fun x => Q (C x))

end TMS2Cleanroom
