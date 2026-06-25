# Frozen full finite TMS2 statement

This file is the only semantic input to the clean-room formalization lane.

Let `X` and `Y` be nonempty finite sets, `C : X → Y` a deterministic coarse map, `P` a row-stochastic Markov kernel on `X`, `Q` a row-stochastic Markov kernel on `Y`, and `μ₀` an initial probability distribution on `X`.

Define

- `μₖ₊₁ = μₖ P`;
- `νₖ = C# μₖ`;
- `ν̂₀ = ν₀` and `ν̂ₖ₊₁ = ν̂ₖ Q`;
- `δ(x) = TV(C#P(x,·), Q(C x,·))`;
- `εₖ = Σₓ μₖ(x) δ(x)`;
- `α = max_{y,y'} TV(Q(y,·), Q(y',·))`;
- `dₖ = TV(νₖ, ν̂ₖ)`.

Prove

`dₖ₊₁ ≤ εₖ + α dₖ`

and, for every finite horizon `t`,

`dₜ ≤ Σ_{k=0}^{t-1} α^(t-1-k) εₖ`,

with the empty sum equal to zero.

Required obligations:

1. finite probability normalization;
2. finite total variation with the conventional half-L1 normalization;
3. triangle inequality;
4. common-weight mixture convexity;
5. maximal-common-mass residual decomposition;
6. Dobrushin contraction;
7. coarse-row mixture identity;
8. occupancy-weighted innovation inequality;
9. scalar recurrence unrolling;
10. empty-horizon and zero-distance boundary cases.

No obligation may be axiomized. No pre-existing project proof source may be imported.
