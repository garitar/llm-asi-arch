import TMS2Cleanroom.Recurrence

namespace TMS2Cleanroom.Controls

/-- Concrete recurrence satisfying the step rule at `c = -1`. -/
def dMut : ℕ → ℝ
  | 0 => 0
  | 1 => -1
  | _ => 0

def eMut : ℕ → ℝ
  | 0 => -(1 / 2 : ℝ)
  | _ => 0

example : dMut 0 = 0 := by norm_num [dMut]

example : ∀ n, dMut (n + 1) ≤ eMut n + (-1 : ℝ) * dMut n := by
  intro n
  rcases n with _ | n
  · norm_num [dMut, eMut]
  · rcases n with _ | n
    · norm_num [dMut, eMut]
    · norm_num [dMut, eMut]

/-- The horizon-three conclusion fails when coefficient nonnegativity is removed. -/
example : ¬ (dMut 3 ≤ weightedSum (-1 : ℝ) eMut 3) := by
  norm_num [dMut, eMut, weightedSum]

end TMS2Cleanroom.Controls
