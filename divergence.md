# Divergences from the paper

Every place where the Lean formalization differs from Campos–Samotij,
*Towards an Optimal Hypergraph Container Lemma* (IMRN 2022). The paper is
authoritative (CLAUDE.md rule 6). An entry here records a deliberate,
approved difference. It is not a license to change a statement.

Each entry lists: **paper**, **Lean**, **why**, **effect on the result**, **status**.

Status values:

- **Approved (date)**: signed off by the human.
- **Pending**: needs a human decision before the affected statement is frozen.
- **Representation**: a modelling choice that does not change the mathematical content.

---

## D1. Proposition 2.2: nonempty family

- **Paper (p. 5):** $C$ finite, $\mathcal I\subseteq 2^C$ decreasing, $p\in(0,1)$ ⟹
  $\log\Pr(C_p\in\mathcal I)\ge\big(|C|-\mathbb E[|C_p|\mid C_p\in\mathcal I]/p\big)\log(1-p)$.
- **Lean (`Prop22Statement`, `Prop22/Statement.lean`):** the same statement with the extra
  hypothesis `𝓘.Nonempty`.
- **Why:** for $\mathcal I=\varnothing$ the left side is $\log 0$ and the conditional
  expectation is undefined. The paper leaves nonemptiness implicit.
- **Effect:** `Prop22Statement` is *weaker* than the paper's proposition, and it is an assumed
  hypothesis, so we assume less. Lemma 4.3 only applies it to a nonempty family, since
  $\varnothing\in\mathcal F$.
- **Status:** Approved (2026-09-29).

## D2. Proposition 2.2: ground set inside a type

- **Paper:** $C$ is an arbitrary finite set.
- **Lean:** `C : Finset V` for a type `V : Type u` with `DecidableEq V`, and
  `𝓘 : Finset (Finset V)` with `𝓘 ⊆ C.powerset`. The statement is universe-polymorphic.
- **Effect:** none. Every finite set is a `Finset` of some type.
- **Status:** Representation.

## D3. Algorithm: choice of $v_i$

- **Paper (§4.1, step (2a)):** "let $v_i$ be *some* such vertex".
- **Lean (`nextVertex`, `Algorithm/Defs.lean`):** the *least* eligible vertex under a fixed
  `[LinearOrder V]`.
- **Why:** makes $v_i$ an explicit function of $(H_i,S_i)$. The paper's proof needs this
  (§4.2: "$H_i$ depends on $S_i$ only") for $f$ to be well-defined.
- **Effect:** none on Theorem B. The theorem is existential in $g,f,\mathcal S$, and any choice rule works.
- **Status:** Approved (2026-09-29, README §7).

## D4. Algorithm: loop as a fixed number of iterations

- **Paper:** "for $i=0,1,\dots$" until STOP at stage $J$.
- **Lean:** `run = (step p δ I)^[|V|] (H, ∅)`, where `step` is the identity once no vertex is
  eligible. `run_stopped` proves that the result is stopped, i.e. that it is stage $J$.
- **Why:** no well-founded recursion is needed. The paper's remark $J\le|V|$ becomes a lemma.
- **Effect:** none. $J$ itself is not a named object in Lean.
- **Status:** Approved (2026-09-29, README §7).

## D5. Probabilities as finite sums

- **Paper:** $X_p$ is a random subset. $\Pr$ and $\mathbb E$ are with respect to its law.
- **Lean:** `probOn X p E = ∑_{A ⊆ X, E A} p^|A| (1-p)^|X∖A|`, with `condProb` and `condExp` as
  quotients (`Probability/RandomSubset.lean`). No measure is built.
- **Junk value:** `condProb`/`condExp` are `0` when the conditioning event has
  probability `0` (Lean's `x / 0 = 0`). The paper only conditions on events of positive
  probability. Every use must carry the positivity proof.
- **Effect:** none where the paper's expressions are defined.
- **Status:** Approved (2026-09-29, README §7).

## D6. Hypergraphs

- **Paper:** $H$ is a hypergraph with finite vertex set $V$.
- **Lean:** `Hypergraph V := Finset (Finset V)` over `[Fintype V]`. The vertex set is the whole
  type `V`, so isolated vertices are allowed, and so is the empty edge.
- **Effect:** none. This matches the paper's usage, where $V$ is fixed and edges are subsets of $V$.
- **Status:** Representation.

## D7. Theorem B: quantifier in (b), (c)

- **Paper:** (b) and (c) quantify over $S\in\mathcal S$.
- **README §2:** states them per input $I$, with $S=g(I)$.
- **Effect:** equivalent for $\mathcal S := g(\mathcal I(H))$, the paper's own choice.
  `Statement.lean` follows the paper's form.
- **Status:** Pending. It will be settled when the frozen statement of `theoremB` is written.
