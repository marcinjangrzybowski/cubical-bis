module Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale where

-- All tolerances in the matching argument are actual rational functions.
-- In particular, no Archimedean or truncated choice of a radius is used.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊; y·[x/y])
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Metric
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric

⟦_⟧₊ : ℚ₊ → ℝ
⟦ q ⟧₊ = rat (fst q)

radius-positive : ∀ q → 0ℝ <ℝ ⟦ q ⟧₊
radius-positive q = <ℚ→<ℝ 0 (fst q) (snd q)

radius-nonnegative : ∀ q → 0ℝ ≤ℝ ⟦ q ⟧₊
radius-nonnegative q = <ℝ-weaken 0ℝ ⟦ q ⟧₊ (radius-positive q)

radius-monotone : ∀ p q → p ≤₊ q → ⟦ p ⟧₊ ≤ℝ ⟦ q ⟧₊
radius-monotone p q = invEq (rat≤rat≃ (fst p) (fst q))

radius-sumL : ∀ p q → ⟦ p ⟧₊ ≤ℝ ⟦ p +₊ q ⟧₊
radius-sumL p q = subst2 _≤ℝ_ (addIdR ⟦ p ⟧₊) (rat+rat (fst p) (fst q))
  (addPres≤L 0ℝ ⟦ q ⟧₊ ⟦ p ⟧₊ (radius-nonnegative q))

radius-sumR : ∀ p q → ⟦ q ⟧₊ ≤ℝ ⟦ p +₊ q ⟧₊
radius-sumR p q = subst2 _≤ℝ_ (addIdL ⟦ q ⟧₊) (rat+rat (fst p) (fst q))
  (addPres≤R 0ℝ ⟦ p ⟧₊ ⟦ q ⟧₊ (radius-nonnegative p))

scaleTolerance : ℚ₊ → ℚ₊ → ℚ₊
scaleTolerance constant ε = ((constant ⁻¹₊) ·₊ (ε /2₊)) /2₊

scaleTolerance-law : ∀ constant ε →
  ⟦ constant ⟧₊ · (⟦ scaleTolerance constant ε ⟧₊ + ⟦ scaleTolerance constant ε ⟧₊) ≡ ⟦ ε /2₊ ⟧₊
scaleTolerance-law constant ε = cong (⟦ constant ⟧₊ ·_)
  (rat+rat (fst (scaleTolerance constant ε)) (fst (scaleTolerance constant ε))
    ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ((constant ⁻¹₊) ·₊ (ε /2₊)))))
    ∙ mul-rat (fst constant) (fst ((constant ⁻¹₊) ·₊ (ε /2₊)))
    ∙ cong rat (y·[x/y] constant (fst (ε /2₊)))

scaledBound→closeness : ∀ constant ε z w →
  normℂ (z -ℂ w) ≤ℝ
    ⟦ constant ⟧₊ · (⟦ scaleTolerance constant ε ⟧₊ + ⟦ scaleTolerance constant ε ⟧₊) →
  z ∼ℂ[ ε ] w
scaledBound→closeness constant ε z w bounded = normℂ-difference<→closeness z w ε
  (≤<ℝ-trans (normℂ (z -ℂ w)) ⟦ ε /2₊ ⟧₊ ⟦ ε ⟧₊
    (subst (normℂ (z -ℂ w) ≤ℝ_) (scaleTolerance-law constant ε) bounded)
    (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)))
