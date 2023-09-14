import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p
-- 3.1
theorem p3_a {p q r : Prop} (h1: p ∧ q → r) : p → (q → r) := by
  intro hp
  intro hq
  have hpq: p ∧ q := by apply And.intro hp hq
  apply h1 hpq

-- 4.1
example {a b : ℤ } (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- 4.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- 4.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = 4 + 5 * b : by rw [h1]
    _ = 4 + 5 * (3 - 2) : by rw [h2]
    _ = 9 : by ring
