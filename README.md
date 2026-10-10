# A characteristic-zero Tachikawa counterexample in Lean 4

The finite-dimensional symmetric-algebra form of Tachikawa's second conjecture,
specialized to the rational numbers
([Tachikawa (1973), Section 8](https://link.springer.com/chapter/10.1007/BFb0060005)), asks:

> **Conjecture.**
> Let $\Gamma$ be a finite-dimensional symmetric $\mathbb Q$-algebra and $M$
> a finite-dimensional $\Gamma$-module with a compatible rational scalar action.
> If $\operatorname{Ext}_\Gamma^n(M,M)=0$ for every $n>0$, then $M$ is projective.

This repository presents a **Lean 4 counterexample over $\mathbb Q$**.
It constructs a symmetric algebra $\Gamma$ and a finite nonprojective module $M$
whose positive self-Ext groups all vanish.

The mathematical argument is also available in the
[PDF manuscript](https://github.com/KitaKen1/tachikawa-characteristic-zero/blob/main/PDF/tachikawa-characteristic-zero.pdf).

Contributions:

1. **FC-style formalization** of the rational symmetric conjecture
   ([statement](FClikelean/TachikawaCharZero.lean)).
2. **Complete Lean 4 proof of its negative answer**
   ([proof](lean/Tachikawa/Main.lean)).

Further consequence:

1. **A negative answer to the general Artin-algebra Auslander–Reiten conjecture**,
   using the same witness
   ([statement](FClikelean/AuslanderReiten.lean),
   [proof](lean/Tachikawa/AuslanderReiten.lean),
   [relationship](#appendix-relationship-between-the-two-conjectures)).

**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ftachikawa-characteristic-zero%2Fmain%2Flean4web%2FTachikawaCharZeroLean4Web.lean)
(Lean **v4.35.0-rc4**).
Select a server environment compatible with the pinned standalone
project; the large proof may take time and memory to elaborate.

## Formal Conjectures targets

[TachikawaCharZero.lean](FClikelean/TachikawaCharZero.lean) contains the primary
Tachikawa target. [AuslanderReiten.lean](FClikelean/AuslanderReiten.lean) contains
the related Artin-algebra consequence in a separate file.

The proposed FC contribution is the **Tachikawa entry** announced in
[issue #7020](https://github.com/google-deepmind/formal-conjectures/issues/7020).
The AR result is a candidate for a **separate future update** to the
[existing Artin-algebra entry](https://github.com/google-deepmind/formal-conjectures/blob/d838afa7a62f66dc034c96fb011c10b9bde3f44c/FormalConjectures/Paper/AuslanderReiten.lean).

The **rational symmetric Tachikawa target** is:

~~~lean
@[category research solved, AMS 16]
theorem tachikawaSecondConjecture :
    answer(False) ↔
      ∀ (Γ : Type) [Ring Γ] [Algebra ℚ Γ] [Module.Finite ℚ Γ],
        SymmetricOver ℚ Γ →
          ∀ (M : Type) [AddCommGroup M] [Module Γ M] [Module ℚ M]
            [IsScalarTower ℚ Γ M] [Module.Finite ℚ M],
            (∀ n : ℕ, 0 < n →
              Subsingleton (CategoryTheory.Abelian.Ext
                (ModuleCat.of Γ M) (ModuleCat.of Γ M) n)) →
              Module.Projective Γ M := by
  sorry
~~~

Here `SymmetricOver ℚ Γ` means that $\Gamma$ is linearly isomorphic to its
rational dual, compatibly with both regular actions. `IsScalarTower` makes
the rational scalar action on $M$ compatible with the $\Gamma$-action.

The **related general Artin-algebra Auslander–Reiten target** is:

~~~lean
@[category research solved, AMS 16]
theorem artinAuslanderReiten :
    answer(False) ↔
      ∀ (Λ : Type) [Ring Λ] (M : Type) [AddCommGroup M] [Module Λ M]
        [Module.Finite Λ M] (A : Type) [CommRing A] [IsArtinianRing A]
        [Algebra A Λ] [Module.Finite A Λ],
        (∀ n : ℕ, 0 < n →
          Subsingleton (CategoryTheory.Abelian.Ext
            (ModuleCat.of Λ M) (ModuleCat.of Λ Λ) n)) →
        (∀ n : ℕ, 0 < n →
          Subsingleton (CategoryTheory.Abelian.Ext
            (ModuleCat.of Λ M) (ModuleCat.of Λ M) n)) →
          Module.Projective Λ M := by
  sorry
~~~

Both targets place `answer(False)` outside all universal quantifiers.
Vanishing is expressed by `Subsingleton` on the actual Mathlib `Abelian.Ext`
groups. The two `by sorry` bodies are FC statement placeholders with
`formal_proof` links to the complete proofs in
[Main.lean](lean/Tachikawa/Main.lean) and
[AuslanderReiten.lean](lean/Tachikawa/AuslanderReiten.lean).
Those proofs establish the same statements without holes or custom axioms.

## Mathematical explanation (AI generated)

The construction adapts the characteristic-two example in
[OpenAI Math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026)
to $\mathbb Q$, retaining the signs in the homological comparisons.
The following sketch links each stage to its Lean implementation.
Write $D=\operatorname{Hom}_{\mathbb Q}(-,\mathbb Q)$ for rational duality.

**1. Construct a symmetric starting algebra with computable self-Ext.**
Start with the rational algebra $C$ at parameter $q=2$ and its explicit
corner-module resolution. Form the trivial extension

~~~math
T=C\ltimes DC,\qquad \dim_{\mathbb Q}T=20.
~~~

The algebra $T$ is symmetric. A concrete complex of projective corner modules
produces a one-dimensional nonprojective module $S$ with

~~~math
\operatorname{Ext}_T^n(S,S)\cong
\begin{cases}
\mathbb Q,&n=3m,\quad m\ge0,\\
0,&n\not\equiv0\pmod3.
\end{cases}
~~~

The three-degree periodicity comes from four short exact sequences;
their connecting maps identify the period with Yoneda multiplication by a
nonzero degree-three class. See
[Resolution.lean](lean/TachikawaCharZero/Resolution.lean),
[StartingSymmetric.lean](lean/TachikawaCharZero/StartingSymmetric.lean),
[PeriodThree.lean](lean/TachikawaCharZero/PeriodThree.lean) and
[PeriodicExt.lean](lean/TachikawaCharZero/PeriodicExt.lean).

**2. Tensor the example and compute its complete-resolution profile.**
Set $E=T\otimes_{\mathbb Q}T$ and $X=S\otimes_{\mathbb Q}S$.
Then $E$ is symmetric of dimension $400$, and $X$ remains one-dimensional
and nonprojective. For $m\ge0$, the signed Künneth comparison gives

~~~math
\operatorname{Ext}_E^{3m}(X,X)\cong\mathbb Q^{m+1},\qquad
\operatorname{Ext}_E^n(X,X)=0\quad(n\not\equiv0\pmod3).
~~~

A complete projective resolution of $X$ extends this calculation to every
integer degree. Its Tate self-Ext is $\mathbb Q^{m+1}$ in degree $3m$, the
dual of that space in degree $-3m-1$, and zero elsewhere. These are
isomorphisms of actual cohomology spaces, with explicit bases in the
nonnegative supported degrees. See
[TensorProfile.lean](lean/TachikawaCharZero/TensorProfile.lean),
[MonomialBasis.lean](lean/TachikawaCharZero/MonomialBasis.lean) and
[TateProfile.lean](lean/TachikawaCharZero/TateProfile.lean).

**3. Use two scaling twists to obtain a triangular cone with vanishing self-Hom.**
The two rational scaling parameters are $H_1=2$ and $H_2=3$.
On supported Tate degrees, the corresponding actions have weights for $m\ge0$:

~~~math
w_H(3m)=H^{-m},\qquad w_H(-3m-1)=H^{m+2}.
~~~

The constructed bimodule $F$ has two projections realizing these actions.
After applying the projections, its signed connecting map has the form

~~~math
\Delta_a(x,y)=
\bigl(w_{H_1}(a)x-\varepsilon_a y,
      w_{H_2}(a)x-\varepsilon_a y\bigr),
\qquad \varepsilon_a=(-1)^a.
~~~

Distinct weights give the required injectivity and surjectivity in the
supported degrees; the zero spaces and exceptional degrees are handled
separately. The sign remains present over $\mathbb Q$. See
[TwistedBranchWeights.lean](lean/TachikawaCharZero/TwistedBranchWeights.lean),
[TwoBranchDelta.lean](lean/TachikawaCharZero/TwoBranchDelta.lean) and
[TwoBranchBijectivity.lean](lean/TachikawaCharZero/TwoBranchBijectivity.lean).

The bimodule and its complete lift define a totally acyclic cone $P$ over
the finite triangular algebra $R=\operatorname{Triangular}(E,F)$.
Let $Z=\operatorname{coker}(P_1\to P_0)$. The connecting-map calculation proves

~~~math
H^a\operatorname{Hom}_R(P,Z)=0
\qquad\text{for }a>0\text{ or }a\le-2.
~~~

If $Z$ were projective, the cone would be contractible, forcing the original
complete resolution of $X$ to be contractible and contradicting the
nonprojectivity of $X$. See
[TriangularWitness.lean](lean/TachikawaCharZero/TriangularWitness.lean),
[TriangularSelfHom.lean](lean/TachikawaCharZero/TriangularSelfHom.lean) and
[TriangularNonprojective.lean](lean/TachikawaCharZero/TriangularNonprojective.lean).

**4. Transfer to the final symmetric algebra.**
Take the trivial extension and its induced module:

~~~math
\Gamma=R\ltimes DR,\qquad
M=Z\oplus D\operatorname{Hom}_R(Z,R).
~~~

The algebra $\Gamma$ is finite-dimensional and symmetric, and $M$ is finite
and nonprojective. The positive and negative Hom-vanishing ranges from Step 3
give exactness on both sides of the transfer construction, yielding

~~~math
\operatorname{Ext}_\Gamma^n(M,M)=0\quad\text{for every }n>0.
~~~

This is the rational Tachikawa counterexample. Since a finite-dimensional
symmetric algebra is self-injective, the same module also satisfies
$\operatorname{Ext}_\Gamma^n(M,\Gamma)=0$ for every $n>0$.
Taking the Artinian base ring to be $\mathbb Q$ therefore refutes the general
Artin-algebra Auslander–Reiten statement. See
[FinalTransfer.lean](lean/TachikawaCharZero/FinalTransfer.lean) and
[ArtinWitness.lean](lean/TachikawaCharZero/ArtinWitness.lean).

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [FClikelean/](FClikelean/) | v4.33.1 | Separate Tachikawa and AR statements, definitions, docstrings and proof links |
| [lean/](lean/) | v4.34.1 | Complete modular proofs and vendored supporting infrastructure |
| [lean4web/](lean4web/) | v4.35.0-rc4 | Complete single-file proof importing only Mathlib |

The modular entry point is [Tachikawa.lean](lean/Tachikawa.lean).
The single-file edition is generated from its dependencies by
[make_lean4web.py](lean/scripts/make_lean4web.py), which scopes the source
modules separately and applies the adaptations needed for Lean 4.35.
Each project pins its dependencies in `lake-manifest.json`.

## Verification

The native and standalone proofs have passed local compilation, together
with FC metadata checks and comparison of the compiled mathematical statements.
Both final theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
The complete proofs have no proof holes; the FC display contains two intentional
statement placeholders.

These checks used existing dependency caches. A cold build, live-browser
execution, independent review and Formal Conjectures acceptance remain unverified.

To build the native proof from the repository root:

~~~sh
cd lean
lake exe cache get
lake build Tachikawa
~~~

To build the standalone proof, run from the repository root:

~~~sh
cd lean4web
lake exe cache get
lake build TachikawaCharZeroLean4Web
~~~

To check the primary FC statement and the separate AR statement, run from
the repository root:

~~~sh
cd FClikelean
lake --wfail build TachikawaCharZero
lake --wfail build AuslanderReiten
~~~

To regenerate the standalone source, run
`python3 lean/scripts/make_lean4web.py` from the repository root.

## References

- [Ki26] K. Kitamura, *A characteristic-zero Tachikawa counterexample* (2026),
  [PDF manuscript](https://github.com/KitaKen1/tachikawa-characteristic-zero/blob/main/PDF/tachikawa-characteristic-zero.pdf)
  and [Lean proof in this repository](lean/Tachikawa/Main.lean).
- [Tac73] H. Tachikawa,
  [Quasi-Frobenius Rings and Generalizations](https://link.springer.com/chapter/10.1007/BFb0060005),
  Lecture Notes in Mathematics 351 (1973), Section 8.
- [AR75] M. Auslander and I. Reiten,
  [On a generalized version of the Nakayama conjecture](https://doi.org/10.1090/S0002-9939-1975-0389977-6),
  Proc. Amer. Math. Soc. 52 (1975), 69–74.
- [OAI26] OpenAI Math,
  [A counterexample to Tachikawa's second conjecture](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026)
  (September 2026), source revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
  The rational construction adapts this characteristic-two example and its
  supporting Lean infrastructure.
- [FC26] The Formal Conjectures Authors,
  [AuslanderReiten.lean](https://github.com/google-deepmind/formal-conjectures/blob/d838afa7a62f66dc034c96fb011c10b9bde3f44c/FormalConjectures/Paper/AuslanderReiten.lean),
  source revision `d838afa7a62f66dc034c96fb011c10b9bde3f44c`.
  This supplies the general Artin-algebra conjecture statement.

The project is distributed under Apache-2.0. See [LICENSE](LICENSE),
[NOTICE](NOTICE) and the preserved vendor license and source headers.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol.

## Appendix: relationship between the two conjectures

### Natural-language relationship

| Statement | Hypotheses on the algebra and module | Vanishing premise |
|---|---|---|
| Rational symmetric Tachikawa conjecture | A finite-dimensional symmetric $\mathbb Q$-algebra $\Gamma$ and a finite-dimensional compatible module $M$ | $\operatorname{Ext}_\Gamma^n(M,M)=0$ for all $n>0$ |
| General Artin-algebra Auslander–Reiten conjecture | An algebra $\Lambda$ finite over a commutative Artinian base ring and a finitely generated $\Lambda$-module $M$ | $\operatorname{Ext}_\Lambda^n(M,\Lambda)=\operatorname{Ext}_\Lambda^n(M,M)=0$ for all $n>0$ |

Both conjectures conclude that $M$ is projective. The rational symmetric
case satisfies the extra regular-module Ext premise because $\Gamma$
is self-injective, and $M$ is finitely generated over $\Gamma$ because it is
finite-dimensional over $\mathbb Q$. Therefore **the general Artin-algebra
AR conjecture would imply the rational symmetric Tachikawa conjecture**.
By contraposition, **the Tachikawa counterexample also refutes AR**.
The AR result here is a consequence of the main counterexample.

### Lean statements

Both files use the namespace `TachikawaCharZero`:

| Result | Public theorem | Complete proof |
|---|---|---|
| Primary Tachikawa result | `TachikawaCharZero.tachikawaSecondConjecture` | [Main.lean](lean/Tachikawa/Main.lean) |
| Related AR result | `TachikawaCharZero.artinAuslanderReiten` | [AuslanderReiten.lean](lean/Tachikawa/AuslanderReiten.lean) |

[ArtinWitness.lean](lean/TachikawaCharZero/ArtinWitness.lean) proves the
regular-module vanishing and finite generation used by the second theorem.
The witness is over $\mathbb Q$ and concerns possibly noncommutative algebras;
the result does not assert a counterexample to a commutative variant or over
every characteristic-zero field.

## Appendix: timeline

| Year | Who | Problem or result |
|---|---|---|
| 1973 | [Hiroyuki Tachikawa](https://link.springer.com/chapter/10.1007/BFb0060005) | Proposes Tachikawa's second conjecture. |
| 1975 | [Maurice Auslander and Idun Reiten](https://doi.org/10.1090/S0002-9939-1975-0389977-6) | Propose the Auslander–Reiten conjecture. |
| 2024 | [Hongxing Chen, Ming Fang and Changchang Xi](https://doi.org/10.1112/S0010437X24007395) | Give an equivalent formulation for symmetric algebras. |
| September 2026 | [Haruhisa Enomoto](https://arxiv.org/abs/2609.19172v1) | Reduces Auslander–Reiten to Tachikawa's second conjecture. |
| September 2026 | [OpenAI Math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026) | Constructs a symmetric counterexample in characteristic two. |
| October 2026 | **This repository (Kenta Kitamura)** | **Proves both negative answers over $\mathbb Q$ in Lean 4.** |
