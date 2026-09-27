import CamposSamotij.Hypergraph.Updates
import CamposSamotij.Probability.RandomSubset

/-!
# The deterministic algorithm (M4)

`State`, `eligible`, `step`, `run` (fuel `|V|`), stopping, termination,
`container`. No probability *proofs* here. See README §4.2.
-/

-- note here a discrepancy with the definition of the algorithm in the paper
-- Give a set a hyprgraph H (our definition), let V be its vertex set, 0 < p ≤ δ < 1
-- container algorithm
-- input: an indepedet set I in H
-- output: a fingerprint S and a container C, both in V

-- Let V_p be the p-random subset of V

-- (1) Start: H_0 = H S_0 = ∅
-- (2)
-- (a) for i; if there is a vertex that is not a singleton in the edge set
-- and Pr(v ∈ V_p | V_p ∈ I(H_i)) < (1 - δ)p then let v_i be such vertex, otherwise J := i and stop
-- returning S_J and C_J
-- (b) if v_i belongs to I, S_i belongs to S_{i+1} and update the 1

namespace CamposSamotij

end CamposSamotij
