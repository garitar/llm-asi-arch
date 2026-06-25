import TMS2Cleanroom.TV

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

open Dist

variable {α β : Type*} [Fintype α] [Fintype β]

lemma push_product_fst (p q : Dist α) (K : Kernel α β) :
    push (product p q) (fun ij => K ij.1) = push p K := by
  apply Dist.ext
  intro b
  simp only [push_apply, product_apply, Fintype.sum_prod_type]
  calc
    ∑ a, ∑ c, p a * q c * K a b = ∑ a, (p a * K a b) * (∑ c, q c) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = ∑ a, p a * K a b := by simp [q.sum_mass]

lemma push_product_snd (p q : Dist α) (K : Kernel α β) :
    push (product p q) (fun ij => K ij.2) = push q K := by
  apply Dist.ext
  intro b
  simp only [push_apply, product_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    ∑ c, ∑ a, p a * q c * K c b = ∑ c, (q c * K c b) * (∑ a, p a) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ c, q c * K c b := by simp [p.sum_mass]

/-- The independent product coupling bounds the distance between two pushed distributions. -/
theorem tv_push_le_pairwise_product (p q : Dist α) (K : Kernel α β) :
    tv (push p K) (push q K) ≤
      ∑ ij, product p q ij * tv (K ij.1) (K ij.2) := by
  have h := tv_push_same_weights_le (product p q)
    (fun ij => K ij.1) (fun ij => K ij.2)
  simpa [push_product_fst, push_product_snd] using h

/-- A uniform bound on every pair of rows bounds the distance of arbitrary pushes. -/
theorem tv_push_le_of_pairwise_le (p q : Dist α) (K : Kernel α β) (c : ℝ)
    (hc : ∀ i j, tv (K i) (K j) ≤ c) :
    tv (push p K) (push q K) ≤ c := by
  calc
    tv (push p K) (push q K)
        ≤ ∑ ij, product p q ij * tv (K ij.1) (K ij.2) :=
          tv_push_le_pairwise_product p q K
    _ ≤ ∑ ij, product p q ij * c := by
          apply Finset.sum_le_sum
          intro ij hij
          exact mul_le_mul_of_nonneg_left (hc ij.1 ij.2) ((product p q).nonneg ij)
    _ = c := by
          rw [← Finset.sum_mul, (product p q).sum_mass, one_mul]

end TMS2Cleanroom
