import Mathlib

theorem test_theorem (α β : ℝ) (hαβ : α - β = 4) : α = β + 4 := by
  -- exact Eq.symm (add_eq_of_eq_sub' (Eq.symm hαβ))
  calc
    α = α - β + β := by exact Eq.symm (sub_add_cancel α β)
    _ = 4 + β := by rw hαβ
    _ = β + 4 := by sorry
