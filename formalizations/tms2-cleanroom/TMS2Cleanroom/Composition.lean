import TMS2Cleanroom.Probability

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

open Dist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Associativity of finite distribution/kernel composition. -/
theorem push_push (p : Dist α) (P : Kernel α β) (Q : Kernel β γ) :
    push (push p P) Q = push p (fun a => push (P a) Q) := by
  apply Dist.ext
  intro c
  simp only [push_apply]
  calc
    ∑ b, (∑ a, p a * P a b) * Q b c
        = ∑ b, ∑ a, (p a * P a b) * Q b c := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, (p a * P a b) * Q b c := by
          rw [Finset.sum_comm]
    _ = ∑ a, p a * (∑ b, P a b * Q b c) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          ring

@[simp]
theorem push_deterministic (f : α → β) (a : α) (Q : Kernel β γ) :
    push (deterministic f a) Q = Q (f a) := by
  classical
  apply Dist.ext
  intro c
  simp [push_apply, deterministic]

/-- Deterministic pushforward commutes with mixing by a preceding kernel. -/
theorem map_push (f : β → γ) (p : Dist α) (P : Kernel α β) :
    map f (push p P) = push p (fun a => map f (P a)) := by
  unfold map
  exact push_push p P (deterministic f)

/-- Pushing a deterministic coarse distribution through `Q` equals mixing `Q ∘ f`. -/
theorem push_map (f : α → β) (p : Dist α) (Q : Kernel β γ) :
    push (map f p) Q = push p (fun a => Q (f a)) := by
  unfold map
  rw [push_push]
  congr 1
  funext a
  exact push_deterministic f a Q

end TMS2Cleanroom
