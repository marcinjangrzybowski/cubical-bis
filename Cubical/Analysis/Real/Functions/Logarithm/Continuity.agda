module Cubical.Analysis.Real.Functions.Logarithm.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (subAddCancel)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Metric
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Logarithm.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity.Reflection

open PositiveRationals using (ℚ₊; 1₊; min₊; min₊≤L; min₊≤R)


private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)

  opaque
    subtractOneLess : ∀ x → x - 1ℝ <ℝ x
    subtractOneLess x =
      subst2 _<ℝ_ (addIdR (x - 1ℝ)) (subAddCancel x 1ℝ)
        (<ℝ-addL 0ℝ 1ℝ (x - 1ℝ) (<ℚ→<ℝ 0 1 (snd 1₊)))

    closePreservesLowerGap : ∀ lower center (gap : ℚ₊) →
      lower + rat (fst gap) ≤ℝ center → ∀ value →
      center ∼[ gap ] value → lower ≤ℝ value
    closePreservesLowerGap lower center gap bounded value near =
      addReflects≤R lower value (rat (fst gap))
        (≤ℝ-trans (lower + rat (fst gap)) center (value + rat (fst gap))
          bounded (close→upperBound center value gap near))


-- A neighborhood of a positive input stays above exp(log(input) - 1).
-- On that half-line the exponential has uniform closeness reflection, so
-- every supplied equivalence has a continuous inverse.  The finitely many
-- neighborhood witnesses are eliminated into continuity itself, without
-- any countable-choice assumption.
logarithmFromEquivalenceIsContinuous : (equivalent : isEquiv expPositive) →
  isContinuous (LowerOpenHalfLinePremetricSpace 0ℝ .snd)
    (logarithmFromEquivalence equivalent) (ℝPremetricSpace .snd)
logarithmFromEquivalenceIsContinuous equivalent point .IsContinuousAt.pres≈ ε =
  PT.rec squash₁ fromGap image-gap
  where
  lower-source : ℝ
  lower-source = logarithmFromEquivalence equivalent point - 1ℝ

  point-above : lower-source ≤ℝ logarithmFromEquivalence equivalent point
  point-above =
    <ℝ-weaken lower-source (logarithmFromEquivalence equivalent point)
      (subtractOneLess (logarithmFromEquivalence equivalent point))

  image-gap : exponentialEntireValue lower-source <ℝ fst point
  image-gap =
    subst (exponentialEntireValue lower-source <ℝ_)
      (expℝ-logarithm equivalent point)
      (exponentialEntireValue-strictlyIncreasing
        lower-source (logarithmFromEquivalence equivalent point)
        (subtractOneLess (logarithmFromEquivalence equivalent point)))

  fromGap : PositiveGap (exponentialEntireValue lower-source) (fst point) →
    ∃[ δ ∈ ℚ₊ ] (∀ value → fst point ∼[ δ ] fst value →
      logarithmFromEquivalence equivalent point ∼[ ε ]
      logarithmFromEquivalence equivalent value)
  fromGap (gap , lower-gap) =
    PT.rec squash₁ fromReflection
      (exponentialEntireValueClosenessReflectionAbove lower-source ε)
    where
    fromReflection :
      (Σ[ radius ∈ ℚ₊ ]
        (∀ x y → lower-source ≤ℝ x → lower-source ≤ℝ y →
          exponentialEntireValue x ∼[ radius ] exponentialEntireValue y →
          x ∼[ ε ] y)) →
      ∃[ δ ∈ ℚ₊ ] (∀ value → fst point ∼[ δ ] fst value →
        logarithmFromEquivalence equivalent point ∼[ ε ]
        logarithmFromEquivalence equivalent value)
    fromReflection (radius , reflects) =
      ∣ min₊ gap radius , preserves ∣₁
      where
      preserves : ∀ value → fst point ∼[ min₊ gap radius ] fst value →
        logarithmFromEquivalence equivalent point ∼[ ε ]
        logarithmFromEquivalence equivalent value
      preserves value near =
        reflects
          (logarithmFromEquivalence equivalent point)
          (logarithmFromEquivalence equivalent value)
          point-above value-above image-close
        where
        value-above : lower-source ≤ℝ logarithmFromEquivalence equivalent value
        value-above =
          exponentialEntireValue-reflects≤ lower-source
            (logarithmFromEquivalence equivalent value)
            (subst (exponentialEntireValue lower-source ≤ℝ_)
              (sym (expℝ-logarithm equivalent value))
              (closePreservesLowerGap (exponentialEntireValue lower-source)
                (fst point) gap lower-gap (fst value)
                (Pℝ.isMonotone≈≤ (fst point) (fst value)
                  (min₊ gap radius) gap (min₊≤L gap radius) near)))

        image-close :
          exponentialEntireValue (logarithmFromEquivalence equivalent point) ∼[ radius ]
          exponentialEntireValue (logarithmFromEquivalence equivalent value)
        image-close =
          subst2 (λ x y → x ∼[ radius ] y)
            (sym (expℝ-logarithm equivalent point))
            (sym (expℝ-logarithm equivalent value))
            (Pℝ.isMonotone≈≤ (fst point) (fst value)
              (min₊ gap radius) radius (min₊≤R gap radius) near)
