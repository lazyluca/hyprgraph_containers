# Motivation and contribution

This repository formalizes one of the hypergraph container lemmas, tools that have become increasingly important in recent years. Specifically, we formalize the hard-core container lemma (Theorem B) of Campos and Samotij [CS], which contains most of the ingredients of the other container lemmas.

## 1. Exact contribution

Every result below is proved in Lean 4 / mathlib with no `sorry` and no `axiom`. `#print axioms` reports only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound` (see [`logs/axioms.log`](logs/axioms.log)). Numbering and pages follow [CS] (arXiv:2408.06617v2).

| Paper result | Statement in [CS] | Lean declaration | File |
|---|---|---|---|
| Theorem B (p. 3) | Hard-core container lemma: for $0<p\le\delta<1$ there are $g,f$ with $g(I)\subseteq I\subseteq f(g(I))$, $\lvert S\rvert\le p\lvert V\rvert/\delta$, and $\mathbb P(S\cup C_p\in\mathcal I(H))\ge(1-p)^{\delta\lvert C\setminus S\rvert}$ | `theoremB_unconditional` | [`TheoremB.lean:114`](CamposSamotij/TheoremB.lean#L114) |
| Theorem B, assuming Prop. 2.2 | Same, with Proposition 2.2 as a hypothesis | `theoremB` | [`TheoremB.lean:91`](CamposSamotij/TheoremB.lean#L91) |
| Lemma 4.1 (p. 12) | $S_i\subseteq I\in\mathcal I(H_i)$, and $I'\in\mathcal I(H_i)\iff S_i\cup I'\in\mathcal I(H_i)$ | `lemma41` | [`Section4/Lemma41.lean:99`](CamposSamotij/Section4/Lemma41.lean#L99) |
| Lemma 4.2 (p. 12) | $\delta\lvert S\rvert\le p\lvert V\rvert$ | `lemma42` | [`Section4/Lemma42.lean:101`](CamposSamotij/Section4/Lemma42.lean#L101) |
| Lemma 4.3 (p. 13) | $\mathbb P(S\cup C_p\in\mathcal I(H))\ge(1-p)^{\delta\lvert C\setminus S\rvert}$ | `lemma43` | [`Section4/Lemma43.lean:200`](CamposSamotij/Section4/Lemma43.lean#L200) |
| Proposition 2.2 (p. 7; proofs in Appendix A) | For a decreasing family $\mathcal I\subseteq 2^C$ and $p\in(0,1)$: $\log\mathbb P(C_p\in\mathcal I)\ge\bigl(\lvert C\rvert-\mathbb E[\lvert C_p\rvert\mid C_p\in\mathcal I]/p\bigr)\log(1-p)$ | `prop22` | [`Prop22/Proof/Induction.lean:156`](CamposSamotij/Prop22/Proof/Induction.lean#L156) |

The formal statements are `TheoremBStatement` ([`Statement.lean:43`](CamposSamotij/Statement.lean#L43)) and `Prop22Statement` ([`Prop22/Statement.lean:42`](CamposSamotij/Prop22/Statement.lean#L42)). Where they differ from the paper (for example, an extra nonemptiness hypothesis in Proposition 2.2), the difference is recorded in [`divergence.md`](divergence.md).

## 2. Why this formalization matters
So far, there have been few projects formalizing recent results in combinatorics. For example, the recent exponential upper bound for induced Ramsey numbers [ACDFM] relies crucially on the hypergraph container method. We see this formalization as one of the first steps towards formalizing these new and exciting results.

## 3. What is reusable
Our definition of a hypergraph differs from the one in mathlib and is easier to use here, because it already builds in the finiteness the proofs require. The other constructions, such as the link operation, and Proposition 2.2 are also reusable.

## 4. Related formalizations and prior work
Related results that have been formalized include Szemerédi's regularity lemma, in Lean by Dillies and Mehta [DM] (now part of mathlib, under the `SzemerediRegularity` namespace) and in Isabelle/HOL by Edmonds, Koutsoukou-Argyraki and Paulson [EKP]. However, we did not find any formalization of a container lemma. We searched mathlib with Loogle (<https://loogle.lean-lang.org>) for declarations whose names contain `container`, `Container` or `hardCore`. The only match was the unrelated field `Lean.Lsp.SymbolInformation.containerName?`. Mathlib's `Hypergraph` (66 declarations) has no notion of independent sets or containers.

## 5. Completed during the event

The event ran from Monday 2026-09-28 to Friday 2026-10-02. The work committed on Sunday
2026-09-27 also counts as event work. It is listed separately so the timeline is clear.

**Sunday 2026-09-27 (commits `c5df8e8`, `eb4be58`):** project setup (Lean/mathlib pins, CI, license, README roadmap, `CLAUDE.md`, the paper), and the basic infrastructure: hypergraphs and independence (`Hypergraph/Basic.lean`), the link and singleton updates (`Hypergraph/Updates.lean`), and the finite random-subset probability API (`Probability/RandomSubset.lean`). The real-analysis lemma (`Probability/RealAux.lean`) still had 2 `sorry`s. `Examples.lean` had six `decide`-checked toy examples, and `Algorithm/Defs.lean` had only an informal description of the algorithm in comments. All other files were empty stubs.

**Tuesday 2026-09-29 to Friday 2026-10-02 (commits `f9973c5` to `816f7e3`, and this packet on Friday):** the frozen statements of Theorem B and Proposition 2.2, the algorithm and its termination, Lemmas 4.1–4.3, the replay lemma, Theorem B, Proposition 2.2, and the documentation (`divergence.md`, README, this packet).

## 6. Completed formal results vs. intended future work
### 6.1 Completed (machine-checked)
Theorem B (unconditionally), Lemmas 4.1, 4.2 and 4.3, and Proposition 2.2. See §1.
### 6.2 Not yet formalized (intended)
Theorems A and D, and the standard container lemma (Theorem C, the efficient container lemma of Balogh and Samotij [BS]). The paper derives Theorem C from Theorem B together with Janson's inequality (Section 5), so this is the natural next step from what is already proved.

## 7. Limitations
The correspondence between the Lean statements and the paper was checked by a human only. Probability in Lean is finicky and seems hard to use in its current form.

## References

- **[CS]** M. Campos and W. Samotij, *Towards an optimal hypergraph container lemma*, Combinatorica **46** (2026), no. 3, Article 24. [doi:10.1007/s00493-026-00214-1](https://link.springer.com/article/10.1007/s00493-026-00214-1); [arXiv:2408.06617](https://arxiv.org/abs/2408.06617).
- **[ACDFM]** L. Aragão, M. Campos, G. Dahia, R. Filipe and J. P. Marciano, *An exponential upper bound for induced Ramsey numbers*, 2025. [arXiv:2509.22629](https://arxiv.org/abs/2509.22629).
- **[BS]** J. Balogh and W. Samotij, *An efficient container lemma*, Discrete Analysis, 2020. [arXiv:1910.09208](https://arxiv.org/abs/1910.09208).
- **[DM]** Y. Dillies and B. Mehta, *Formalising Szemerédi's regularity lemma in Lean*, 13th International Conference on Interactive Theorem Proving (ITP 2022), LIPIcs **237**, 9:1–9:19. [doi:10.4230/LIPIcs.ITP.2022.9](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.9).
- **[EKP]** C. Edmonds, A. Koutsoukou-Argyraki and L. C. Paulson, *Formalising Szemerédi's regularity lemma and Roth's theorem on arithmetic progressions in Isabelle/HOL*, Journal of Automated Reasoning **67** (2023), Article 2. [arXiv:2207.07499](https://arxiv.org/abs/2207.07499).
