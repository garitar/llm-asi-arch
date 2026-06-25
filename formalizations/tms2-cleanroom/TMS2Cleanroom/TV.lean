import TMS2Cleanroom.Probability

open scoped BigOperators

noncomputable section

namespace TMS2Cleanroom

open Dist

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-- Positive part, used to expose the common-mass decomposition explicitly. -/
def pos (x : ℝ) : ℝ := max x 0

lemma pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_right _ _

lemma le_pos (x : ℝ) : x ≤ pos x := le_max_left _ _

lemma pos_add_le (x y : ℝ) : pos (x + y) ≤ pos x + pos y := by
  apply max_le
  · linarith [le_pos x, le_pos y]
  · exact add_nonneg (pos_nonneg x) (pos_nonneg y)

lemma pos_mul_of_nonneg {c x : ℝ} (hc : 0 ≤ c) : pos (c * x) = c * pos x := by
  by_cases hx : 0 ≤ x
  · simp [pos, max_eq_left hx, max_eq_left (mul_nonneg hc hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hcx : c * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hx'
    simp [pos, max_eq_right hx', max_eq_right hcx]

lemma pos_sub_pos_neg (x : ℝ) : pos x - pos (-x) = x := by
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := by linarith
    simp [pos, max_eq_left hx, max_eq_right hnx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hnx : 0 ≤ -x := by linarith
    simp [pos, max_eq_right hx', max_eq_left hnx]

lemma abs_eq_pos_add_pos_neg (x : ℝ) : |x| = pos x + pos (-x) := by
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := by linarith
    simp [abs_of_nonneg hx, pos, max_eq_left hx, max_eq_right hnx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hnx : 0 ≤ -x := by linarith
    simp [abs_of_nonpos hx', pos, max_eq_right hx', max_eq_left hnx]

lemma pos_sum_le_sum_pos (s : Finset ι) (f : ι → ℝ) :
    pos (∑ i ∈ s, f i) ≤ ∑ i ∈ s, pos (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pos]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (pos_add_le (f a) (∑ i ∈ s, f i)).trans (add_le_add_left ih _)

/-- Total variation as positive mass of the signed difference. -/
def tvPos (p q : Dist α) : ℝ := ∑ a, pos (p a - q a)

/-- Standard finite total variation, one half of the L1 distance. -/
def tv (p q : Dist α) : ℝ := (1 / 2 : ℝ) * ∑ a, |p a - q a|

lemma sum_sub_eq_zero (p q : Dist α) : ∑ a, (p a - q a) = 0 := by
  rw [Finset.sum_sub_distrib, p.sum_mass, q.sum_mass]
  ring

lemma tvPos_symm (p q : Dist α) : tvPos p q = tvPos q p := by
  have hzero : ∑ a, (p a - q a) = 0 := sum_sub_eq_zero p q
  have hrel : tvPos p q - tvPos q p = 0 := by
    unfold tvPos
    rw [← Finset.sum_sub_distrib]
    calc
      ∑ a, (pos (p a - q a) - pos (q a - p a)) = ∑ a, (p a - q a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have h := pos_sub_pos_neg (p a - q a)
        convert h using 1 <;> ring
      _ = 0 := hzero
  linarith

lemma tv_eq_tvPos (p q : Dist α) : tv p q = tvPos p q := by
  have habs :
      (∑ a, |p a - q a|) = tvPos p q + tvPos q p := by
    unfold tvPos
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have h := abs_eq_pos_add_pos_neg (p a - q a)
    convert h using 1 <;> ring
  rw [tv, habs, tvPos_symm p q]
  ring

lemma tv_nonneg (p q : Dist α) : 0 ≤ tv p q := by
  rw [tv_eq_tvPos]
  exact Finset.sum_nonneg fun a ha => pos_nonneg _

@[simp]
lemma tv_self (p : Dist α) : tv p p = 0 := by
  simp [tv, pos]

lemma tv_symm (p q : Dist α) : tv p q = tv q p := by
  simp only [tv_eq_tvPos]
  exact tvPos_symm p q

lemma tv_triangle (p q r : Dist α) : tv p r ≤ tv p q + tv q r := by
  simp only [tv_eq_tvPos]
  unfold tvPos
  calc
    ∑ a, pos (p a - r a) ≤ ∑ a, (pos (p a - q a) + pos (q a - r a)) := by
      apply Finset.sum_le_sum
      intro a ha
      have h : p a - r a = (p a - q a) + (q a - r a) := by ring
      rw [h]
      exact pos_add_le _ _
    _ = (∑ a, pos (p a - q a)) + ∑ a, pos (q a - r a) := by
      rw [Finset.sum_add_distrib]

lemma tv_le_one (p q : Dist α) : tv p q ≤ 1 := by
  rw [tv_eq_tvPos]
  calc
    ∑ a, pos (p a - q a) ≤ ∑ a, p a := by
      apply Finset.sum_le_sum
      intro a ha
      apply max_le
      · linarith [q.nonneg a]
      · exact p.nonneg a
    _ = 1 := p.sum_mass

/-- Convexity of total variation under a common finite mixing distribution. -/
theorem tv_push_same_weights_le (w : Dist ι) (P Q : Kernel ι α) :
    tv (push w P) (push w Q) ≤ ∑ i, w i * tv (P i) (Q i) := by
  simp only [tv_eq_tvPos]
  unfold tvPos
  have hpoint : ∀ a,
      pos (push w P a - push w Q a) ≤ ∑ i, w i * pos (P i a - Q i a) := by
    intro a
    calc
      pos (push w P a - push w Q a) = pos (∑ i, w i * (P i a - Q i a)) := by
        simp only [push_apply]
        congr 1
        rw [Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i, pos (w i * (P i a - Q i a)) := by
        simpa only [Finset.sum_filter] using
          pos_sum_le_sum_pos (Finset.univ : Finset ι) (fun i => w i * (P i a - Q i a))
      _ = ∑ i, w i * pos (P i a - Q i a) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [pos_mul_of_nonneg (w.nonneg i)]
  calc
    ∑ a, pos (push w P a - push w Q a)
        ≤ ∑ a, ∑ i, w i * pos (P i a - Q i a) := by
          apply Finset.sum_le_sum
          intro a ha
          exact hpoint a
    _ = ∑ i, w i * (∑ a, pos (P i a - Q i a)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]

end TMS2Cleanroom
