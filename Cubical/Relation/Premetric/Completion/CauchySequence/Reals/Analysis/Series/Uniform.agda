module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (≤<ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteSum
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute


-- A uniform tail at one radius contains one cutoff that works for every
-- parameter.  The cutoff is kept under truncation below: uniform convergence
-- needs common cutoffs radius by radius, but does not need a function choosing
-- all of them simultaneously.

UniformCauchyTail : ∀ {ℓ} (X : Type ℓ) →
  (X → RealSequence) → ℚ₊ → Type ℓ
UniformCauchyTail X terms ε =
  Σ[ N ∈ ℕ ]
    (∀ x m n →
      N ℕ.≤ m → N ℕ.≤ n →
      partialSum (terms x) m Real.Base.≈ᶜ[ ε ]
      partialSum (terms x) n)


UniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ) →
  (X → RealSequence) → Type ℓ
UniformlyCauchySeries X terms =
  ∀ ε → ∥ UniformCauchyTail X terms ε ∥₁


isPropUniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ)
  (terms : X → RealSequence) →
  isProp (UniformlyCauchySeries X terms)
isPropUniformlyCauchySeries X terms =
  isPropΠ λ _ → squash₁


UniformlyAbsolutelyCauchySeries : ∀ {ℓ} (X : Type ℓ) →
  (X → RealSequence) → Type ℓ
UniformlyAbsolutelyCauchySeries X terms =
  UniformlyCauchySeries X (λ x → Abs.absℝ ∘ terms x)


isPropUniformlyAbsolutelyCauchySeries : ∀ {ℓ} (X : Type ℓ)
  (terms : X → RealSequence) →
  isProp (UniformlyAbsolutelyCauchySeries X terms)
isPropUniformlyAbsolutelyCauchySeries X terms =
  isPropUniformlyCauchySeries X (λ x → Abs.absℝ ∘ terms x)


-- This is the conventional, stronger interface.  It is useful when a
-- concrete modulus is already available, but it is intentionally not the
-- definition of uniform Cauchyness used by this development.

ChosenUniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ) →
  (X → RealSequence) → Type ℓ
ChosenUniformlyCauchySeries X terms =
  Σ[ modulus ∈ (ℚ₊ → ℕ) ]
    (∀ ε x m n →
      modulus ε ℕ.≤ m → modulus ε ℕ.≤ n →
      partialSum (terms x) m Real.Base.≈ᶜ[ ε ]
      partialSum (terms x) n)


chosenUniformlyCauchy→uniformlyCauchy : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) →
  ChosenUniformlyCauchySeries X terms →
  UniformlyCauchySeries X terms
chosenUniformlyCauchy→uniformlyCauchy X terms (modulus , close) ε =
  ∣ modulus ε , close ε ∣₁


-- No converse is exported.  It would commute the product over all positive
-- rational radii with propositional truncation, i.e. choose all uniform tails
-- at once.  The analytic results below only eliminate one radius at a time.

uniformlyCauchySeriesAt : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  ∀ x → IsCauchySeries (terms x)
uniformlyCauchySeriesAt X terms uniform x ε =
  PT.map (λ (N , close) →
    N , λ m n N≤m N≤n → close x m n N≤m N≤n)
    (uniform ε)


uniformlyAbsolutelyCauchySeriesAt : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) →
  UniformlyAbsolutelyCauchySeries X terms →
  ∀ x → IsAbsolutelyCauchySeries (terms x)
uniformlyAbsolutelyCauchySeriesAt X terms uniform =
  uniformlyCauchySeriesAt X (λ x → Abs.absℝ ∘ terms x) uniform


-- The same tail of the majorant works for every member of the family.  This
-- is stronger than applying the pointwise domination theorem separately,
-- which would hide a potentially different cutoff for every parameter.

familyDominatedByCauchySeriesIsUniformlyCauchy : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) (bound : RealSequence) →
  (∀ x n → Abs.absℝ (terms x n) ≤ℝ bound n) →
  IsCauchySeries bound →
  UniformlyCauchySeries X terms
familyDominatedByCauchySeriesIsUniformlyCauchy
  X terms bound dominates bound-cauchy ε =
  PT.map makeTail (bound-cauchy ε)
  where
  makeTail : CauchyTail (partialSum bound) ε →
    UniformCauchyTail X terms ε
  makeTail (N , closeBound) =
    N , λ x m n N≤m N≤n →
      absDifference<→closeness
        (partialSum (terms x) m) (partialSum (terms x) n) ε
        (≤<ℝ-trans
          (Abs.absℝ
            (partialSum (terms x) m Group.- partialSum (terms x) n))
          (Abs.absℝ
            (partialSum bound m Group.- partialSum bound n))
          (Real.ιℚ (fst ε))
          (partialSumDistanceBoundBy
            (terms x) bound (dominates x) m n)
          (closeness→absDifference<
            (partialSum bound m) (partialSum bound n) ε
            (closeBound m n N≤m N≤n)))


familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) (bound : RealSequence) →
  (∀ x n → Abs.absℝ (terms x n) ≤ℝ bound n) →
  IsCauchySeries bound →
  UniformlyAbsolutelyCauchySeries X terms
familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
  X terms bound dominates bound-cauchy =
  familyDominatedByCauchySeriesIsUniformlyCauchy
    X (λ x → Abs.absℝ ∘ terms x) bound
    (λ x n →
      subst (_≤ℝ bound n) (sym (Abs.absℝ-idempotent (terms x n)))
        (dominates x n))
    bound-cauchy


uniformAbsoluteCauchySeriesIsUniformCauchy : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) →
  UniformlyAbsolutelyCauchySeries X terms →
  UniformlyCauchySeries X terms
uniformAbsoluteCauchySeriesIsUniformCauchy X terms absolute ε =
  PT.map makeTail (absolute ε)
  where
  makeTail : UniformCauchyTail X (λ x → Abs.absℝ ∘ terms x) ε →
    UniformCauchyTail X terms ε
  makeTail (N , closeAbsolute) =
    N , λ x m n N≤m N≤n →
      absDifference<→closeness
        (partialSum (terms x) m) (partialSum (terms x) n) ε
        (≤<ℝ-trans
          (Abs.absℝ
            (partialSum (terms x) m Group.- partialSum (terms x) n))
          (Abs.absℝ
            (partialSum (Abs.absℝ ∘ terms x) m Group.-
             partialSum (Abs.absℝ ∘ terms x) n))
          (Real.ιℚ (fst ε))
          (partialSumDistanceBound (terms x) m n)
          (closeness→absDifference<
            (partialSum (Abs.absℝ ∘ terms x) m)
            (partialSum (Abs.absℝ ∘ terms x) n) ε
            (closeAbsolute x m n N≤m N≤n)))


uniformlyCauchySeriesSummableAt : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  ∀ x → Summable (terms x)
uniformlyCauchySeriesSummableAt X terms uniform x =
  cauchySeriesIsSummable (terms x)
    (uniformlyCauchySeriesAt X terms uniform x)


uniformSeriesValue : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence) →
  UniformlyCauchySeries X terms → X → Real.ℝ
uniformSeriesValue X terms uniform x =
  seriesSum (terms x)
    (uniformlyCauchySeriesSummableAt X terms uniform x)


UniformlyConvergesSeries : ∀ {ℓ} (X : Type ℓ) →
  (X → RealSequence) → (X → Real.ℝ) → Type ℓ
UniformlyConvergesSeries X terms value =
  ∀ ε →
    ∥ Σ[ N ∈ ℕ ]
        (∀ x n → N ℕ.≤ n →
          partialSum (terms x) n Real.Base.≈ᶜ[ ε ] value x)
    ∥₁


isPropUniformlyConvergesSeries : ∀ {ℓ} (X : Type ℓ)
  (terms : X → RealSequence) (value : X → Real.ℝ) →
  isProp (UniformlyConvergesSeries X terms value)
isPropUniformlyConvergesSeries X terms value =
  isPropΠ λ _ → squash₁


-- A radiuswise uniform Cauchy family converges uniformly to its canonical
-- pointwise sum.  The common cutoff remains under truncation.  For each x,
-- the pointwise limit tail is eliminated only into closeness, a proposition;
-- no family of pointwise limit indices is selected.

uniformPartialSumsConvergeToSeriesValue : ∀ {ℓ}
  (X : Type ℓ) (terms : X → RealSequence)
  (uniform : UniformlyCauchySeries X terms) →
  UniformlyConvergesSeries X terms
    (uniformSeriesValue X terms uniform)
uniformPartialSumsConvergeToSeriesValue X terms uniform ε =
  PT.map makeUniformLimit (uniform (ε /2₊))
  where
  value : X → Real.ℝ
  value = uniformSeriesValue X terms uniform

  makeUniformLimit : UniformCauchyTail X terms (ε /2₊) →
    Σ[ N ∈ ℕ ]
      (∀ x n → N ℕ.≤ n →
        partialSum (terms x) n Real.Base.≈ᶜ[ ε ] value x)
  makeUniformLimit (N , closeUniform) =
    N , λ x n N≤n →
      PT.rec
        (Real.Base.isProp≈ᶜ (partialSum (terms x) n) ε (value x))
        (λ (K , closeLimit) →
          subst
            (λ ρ →
              partialSum (terms x) n Real.Base.≈ᶜ[ ρ ] value x)
            (ℚ₊≡ (/2+/2≡id (fst ε)))
            (Real.Approximation.tri≈ᶜ
              (partialSum (terms x) n)
              (partialSum (terms x) (n +ℕ K))
              (value x) (ε /2₊) (ε /2₊)
              (closeUniform x n (n +ℕ K) N≤n
                (ℕ.≤-trans N≤n ℕ.≤SumLeft))
              (closeLimit (n +ℕ K) ℕ.≤SumRight)))
        (seriesSumHasSum (terms x)
          (uniformlyCauchySeriesSummableAt X terms uniform x)
          (ε /2₊))


-- Uniform limits of continuous partial sums are continuous.  A chosen
-- uniform modulus is unnecessary: at the requested output radius we open
-- exactly one truncated common cutoff, and the continuity conclusion is
-- itself propositionally truncated.

uniformSeriesValueIsContinuousFromPartialSums : ∀ {ℓ ℓ'}
  {X : Type ℓ}
  (source : PremetricStr ℓ' X)
  (terms : X → RealSequence)
  (uniform : UniformlyCauchySeries X terms) →
  (∀ n → isContinuous source
    (λ x → partialSum (terms x) n)
    (snd Real.ℝPremetricSpace)) →
  isContinuous source
    (uniformSeriesValue X terms uniform)
    (snd Real.ℝPremetricSpace)
uniformSeriesValueIsContinuousFromPartialSums
  {X = X} source terms uniform partial-sum-continuous x
  .IsContinuousAt.pres≈ ε =
  PT.rec squash₁ useUniformCutoff
    (uniformPartialSumsConvergeToSeriesValue
      X terms uniform (ε /4₊))
  where
  value : X → Real.ℝ
  value = uniformSeriesValue X terms uniform

  useUniformCutoff :
    (Σ[ N ∈ ℕ ]
      (∀ y n → N ℕ.≤ n →
        partialSum (terms y) n Real.Base.≈ᶜ[ ε /4₊ ] value y)) →
    ∥ Σ[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_ source x δ y →
          value x Real.Base.≈ᶜ[ ε ] value y)
    ∥₁
  useUniformCutoff (N , closeToValue) =
    PT.map usePartialSumContinuity
      (partial-sum-continuous N x
        .IsContinuousAt.pres≈ (ε /2₊))
    where
    usePartialSumContinuity :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ y → PremetricStr._≈[_]_ source x δ y →
          partialSum (terms x) N Real.Base.≈ᶜ[ ε /2₊ ]
          partialSum (terms y) N)) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ y → PremetricStr._≈[_]_ source x δ y →
          value x Real.Base.≈ᶜ[ ε ] value y)
    usePartialSumContinuity (δ , partial-close) =
      δ , λ y x≈y →
        subst
          (λ ρ → value x Real.Base.≈ᶜ[ ρ ] value y)
          (ℚ₊≡ ℚ!)
          (Real.Approximation.tri≈ᶜ
            (value x) (partialSum (terms x) N) (value y)
            (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
            (Real.Base.sym≈ᶜ
              (partialSum (terms x) N) (value x) (ε /4₊)
              (closeToValue x N ℕ.≤-refl))
            (Real.Approximation.tri≈ᶜ
              (partialSum (terms x) N)
              (partialSum (terms y) N) (value y)
              (ε /2₊) (ε /4₊)
              (partial-close y x≈y)
              (closeToValue y N ℕ.≤-refl)))


partialSumFamilyIsContinuous : ∀ {ℓ ℓ'}
  {X : Type ℓ}
  (source : PremetricStr ℓ' X)
  (terms : X → RealSequence) →
  (∀ n → isContinuous source (λ x → terms x n)
    (snd Real.ℝPremetricSpace)) →
  ∀ n → isContinuous source
    (λ x → partialSum (terms x) n)
    (snd Real.ℝPremetricSpace)
partialSumFamilyIsContinuous source terms term-continuous zero x
  .IsContinuousAt.pres≈ ε =
  ∣ 1 , (λ _ _ → Real.Base.isRefl≈ᶜ zeroℝ ε) ∣₁
partialSumFamilyIsContinuous source terms term-continuous (suc n) =
  addOfContinuousIsContinuous source
    (λ x → partialSum (terms x) n)
    (λ x → terms x n)
    (partialSumFamilyIsContinuous source terms term-continuous n)
    (term-continuous n)


uniformSeriesValueIsContinuous : ∀ {ℓ ℓ'}
  {X : Type ℓ}
  (source : PremetricStr ℓ' X)
  (terms : X → RealSequence)
  (uniform : UniformlyCauchySeries X terms) →
  (∀ n → isContinuous source (λ x → terms x n)
    (snd Real.ℝPremetricSpace)) →
  isContinuous source
    (uniformSeriesValue X terms uniform)
    (snd Real.ℝPremetricSpace)
uniformSeriesValueIsContinuous source terms uniform term-continuous =
  uniformSeriesValueIsContinuousFromPartialSums source terms uniform
    (partialSumFamilyIsContinuous source terms term-continuous)
