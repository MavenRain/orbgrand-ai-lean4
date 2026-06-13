import OrbgrandAi

open OrbgrandAi.Section06

example : kendallTau ([0, 1, 2, 3] : QueryOrder 4) [0, 2, 1, 3] = 1 := rfl
