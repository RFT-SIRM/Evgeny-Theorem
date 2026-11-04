# Theorem statement

## Object

Let $SG(m)$ be the standard Sierpiński-gasket approximation graph at refinement level $m$, built by recursive triangle subdivision in `src/graph/sg_graph.py`. Its vertex count, edge count, and number of elementary triangular faces are

$$
|V_m|=(3^{m+1}+3)/2,\quad |E_m|=3^{m+1},\quad |F_m|=3^m.
$$

The Hilbert space is $\mathbb{C}^{|V_m|}\otimes\mathbb{C}^{2}$. Every graph edge carries a unitary $U(a,b)\in SU(2)$, with $U(b,a)=U(a,b)^\dagger$. Flux is placed on one designated edge per elementary triangle. Two configurations are compared at the same local rotation angle $\theta$:

- **C — non-commuting:** the rotation axis on the flux edge cycles through $x,y,z$ by triangle index.
- **C′ — commuting control:** the axis is fixed to $z$ for every triangle. The edge matrices commute; this is equivalent to two decoupled U(1) magnetic Sierpiński-gasket Laplacians at fluxes $\pm\theta/2$.

At $\theta=0$, both configurations reduce to two decoupled copies of the plain Sierpiński-gasket Laplacian.

## Fourth-moment theorem

Define the fourth-moment trace defect by

$$
\Delta_m(H^4,\theta)=\mathrm{Tr}(H_C^4)-\mathrm{Tr}(H_{C'}^4).
$$

Then, for every $m\ge1$ and every real $\theta$,

$$
\Delta_m(H^4,\theta)=-16(3^{m-1}+1)\sin^2(\theta/2),\quad m\ge1.
$$

This identity has three complementary records:

1. a human-readable proof in [docs/PROOF.md](docs/PROOF.md);
2. exact symbolic verification and locality analysis in [docs/EXACT_VERIFICATION.md](docs/EXACT_VERIFICATION.md) and [docs/SPLIT_AUTOMATON.md](docs/SPLIT_AUTOMATON.md);
3. a Lean 4 machine-checked proof for every $m\ge1$ and every $\theta$, through `traceDefect_closed` in [formalization/README.md](formalization/README.md).

The formula is not restricted to the finite set of tested levels. Numerical and exact-computation tables are provided separately in [VERIFICATION.md](VERIFICATION.md).

## Normalized invariant

The matrix dimension is

$$
\dim(H_m)=2|V_m|=3^{m+1}+3.
$$

Define

$$
I_m(\theta)=\frac{\Delta_m(H^4,\theta)}{3^{m+1}+3}.
$$

Its limit is

$$
I_\infty(\theta)=-\frac{16}{9}\sin^2(\theta/2),\quad I_\infty(\pi/2)=-\frac89.
$$

## Higher-moment results

The table below gives direct numerical regression values at $\theta=\pi/2$. The table is a finite computational record, not the proof of the all-angle higher-moment statements.

| $m$ | $\Delta_m(H^6,\pi/2)$ | $\Delta_m(H^8,\pi/2)$ | $\Delta_m(H^{10},\pi/2)$ |
|---:|---:|---:|---:|
| 1 | −3180.000000000000 | −246909.026268397924 | −14013358.982483163476 |
| 2 | −6956.588745030516 | −595053.284942481667 | −37686518.369789719582 |
| 3 | −18274.354980121832 | −1632052.331668503582 | −107772338.487565994263 |
| 4 | −52227.653685396537 | −4743049.471846580505 | −318029798.840893745422 |

The higher-moment proof status is:

- **H⁶:** Lean proves the all-angle recurrence for $m\ge3$. An exact symbolic certificate supplies the exceptional $m=2\to3$ transition, giving the combined all-angle formula for $m\ge2$. The finite bridge is not yet a Lean-kernel theorem.
- **H⁸:** Lean proves the all-angle affine recurrence for $m\ge3$. The exact sparse-polynomial certificate supplies the finite $m=2\to3$ transition, giving the combined formula for $m\ge2$. The finite bridge is not yet a Lean-kernel theorem.
- **H¹⁰:** the p=10 gluing assembly, orientation recurrences, and row transport through degree nine are machine-checked. The affine closed form from level five is machine-checked under the explicit hypothesis `H10TransportAll`. That hypothesis remains unproved in the current Lean source, and its level-five residual is still an exact trace expression.

The full formulas, theorem names, certificate locations, and proof boundaries are collected in [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md). The numerical values remain locked by [tests/test_higher_moments.py](tests/test_higher_moments.py).

## Six-criterion acceptance record for the normalized H⁴ invariant

| # | Criterion | Evidence |
|---|---|---|
| i | Stable limit as $m\to\infty$ | Exact limit $-8/9$ at $\theta=\pi/2$, with geometric convergence. |
| ii | Distinction from plain SG and U(1)-magnetic SG | The compared configurations differ in their non-commuting axis pattern. |
| iii | Survives normalization | The per-state quantity $I_m$ has a finite nonzero limit for nontrivial angle. |
| iv | Gauge invariance | Spectral invariance under vertex-wise SU(2) gauge transformations; numerical check recorded in VERIFICATION.md. |
| v | Not a trivial counting function | C and C′ have the same graph, dimensions, edges, faces, and flux placement. |
| vi | Vanishes in the commuting limit | The defect vanishes at moments p=1,2,3; the first nonzero moment is p=4. |

## Scope

The unconditional closed-form theorem in this file is the fourth-moment statement. H⁶ and H⁸ have combined Lean-recurrence plus exact-certificate formulas with a finite bridge outside the Lean kernel. H¹⁰ has a machine-checked conditional affine form whose transport hypothesis remains to be proved. These distinctions are maintained explicitly in the research documentation.
