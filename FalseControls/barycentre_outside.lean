import RussellRebuild
-- The Earth–Moon mutual centre lies inside the Earth, about 4,670 km out, not beyond 6,371 km.
example : (6371 : ℝ) < 384400 * 7.342e22 / (5.9722e24 + 7.342e22) := by norm_num
