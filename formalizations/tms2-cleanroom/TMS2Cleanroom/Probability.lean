import Mathlib

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

/-- A probability distribution on a finite type, represented extensionally. -/
structure Dist (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_mass : ∑ a, mass a = 1

namespace Dist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

instance : CoeFun (Dist α) (fun _ => α → ℝ) := ⟨Dist.mass⟩

@[ext]
theorem ext {p q : Dist α} (h : ∀ a, p a = q a) : p = q := by
  cases p
  cases q
  simp only [Dist.mk.injEq]
  funext a
  exact h a

/-- A finite Markov kernel. -/
abbrev Kernel (α β : Type*) [Fintype β] := α → Dist β

/-- Push a distribution through a finite Markov kernel. -/
def push (p : Dist α) (K : Kernel α β) : Dist β where
  mass b := ∑ a, p a * K a b
  nonneg b := Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) ((K a).nonneg b)
  sum_mass := by
    calc
      ∑ b, ∑ a, p a * K a b = ∑ a, ∑ b, p a * K a b := by
        rw [Finset.sum_comm]
      _ = ∑ a, p a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.mul_sum, (K a).sum_mass, mul_one]
      _ = 1 := p.sum_mass

@[simp]
theorem push_apply (p : Dist α) (K : Kernel α β) (b : β) :
    push p K b = ∑ a, p a * K a b := rfl

/-- Deterministic maps are special Markov kernels. -/
def deterministic (f : α → β) : Kernel α β := by
  classical
  intro a
  exact
    { mass := fun b => if f a = b then 1 else 0
      nonneg := by
        intro b
        split <;> positivity
      sum_mass := by simp }

/-- Pushforward along a deterministic map. -/
def map (f : α → β) (p : Dist α) : Dist β := push p (deterministic f)

/-- The product of two finite distributions. -/
def product (p : Dist α) (q : Dist β) : Dist (α × β) where
  mass ij := p ij.1 * q ij.2
  nonneg ij := mul_nonneg (p.nonneg ij.1) (q.nonneg ij.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ a, ∑ b, p a * q b = ∑ a, p a * (∑ b, q b) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      _ = ∑ a, p a := by simp [q.sum_mass]
      _ = 1 := p.sum_mass

@[simp]
theorem product_apply (p : Dist α) (q : Dist β) (a : α) (b : β) :
    product p q (a, b) = p a * q b := rfl

/-- Iteration of a Markov kernel. -/
def iterate (K : Kernel α α) : ℕ → Dist α → Dist α
  | 0 => id
  | n + 1 => fun p => push (iterate K n p) K

@[simp]
theorem iterate_zero (K : Kernel α α) (p : Dist α) : iterate K 0 p = p := rfl

@[simp]
theorem iterate_succ (K : Kernel α α) (n : ℕ) (p : Dist α) :
    iterate K (n + 1) p = push (iterate K n p) K := rfl

end Dist

end TMS2Cleanroom
