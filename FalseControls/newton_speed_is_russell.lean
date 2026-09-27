import RussellRebuild
-- Newton's n = -1 gives speeds scaling as lam^(n/2) = lam^(-1/2), not 1/a: n/2 = -1 fails.
example : (-1 : ℝ) / 2 = -1 := by norm_num
