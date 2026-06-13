import OrbgrandAi

open OrbgrandAi.Section06

example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [1, 2, 3, 0] = 3 := rfl
