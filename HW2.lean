import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

theorem example_v1 {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc
    x = x + 3 - 3 := by ring
    _ = (2 * y - 3) + 3 - 3 := by rel [h1]
    _ = y + y - 3 := by ring
    _ = y + (1 - 3) := by rel [h2]
    _ = y + (-2) := by ring
    _ ≥ 1 + (-2) := by rel [h2]
    _ = -1 := by ring


theorem example_v2 {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  calc
    a + b = a + 2 * b - b := by ring
    _ ≥ 4 - b := by rel [h2]
    _ ≥ 3 - b + 1 := by rel [h1]
    _ ≥ 3 - 1 + 1 := by rel [h2]
    _ = 3 := by ring

theorem six_c_v2 {x : ℤ} (h1 : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * (x * x - 8 * x + 2) := by ring
    _ = x * (x - 4) * (x - 4) + 14 * x - 2 * 7 * x := by ring
    _ ≥ 9 * (9 - 4) * (9 - 4) + 14 * 9 - 2 * 7 * 9 := by rel [h1]
    _ = 3 := by numbers
