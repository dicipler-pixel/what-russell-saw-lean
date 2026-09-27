import RussellRebuild
-- The effective steepness 2 + 6M/r reaches 3 at r = 6M, not at r = 3M (M = 1).
example : (2 : ℝ) + 6 * 1 / 3 = 3 := by norm_num
