module Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Inverse using (_₊／₊_; ·／)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Integration.UniformContinuity

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)

  productDifferencePath : ∀ a b c d →
    a · c - b · d ≡ c · (a - b) + b · (c - d)
  productDifferencePath a b c d =
    cong ((a · c) +_) (sym (addIdL (- (b · d))))
    ∙ cong (λ value → a · c + (value + (- (b · d))))
        (sym (addInvL (b · c)))
    ∙ addAssoc (a · c) ((- (b · c)) + b · c) (- (b · d))
    ∙ cong (_+ (- (b · d))) (addAssoc (a · c) (- (b · c)) (b · c))
    ∙ sym (addAssoc ((a · c) + (- (b · c))) (b · c) (- (b · d)))
    ∙ cong₂ _+_ (sym (ℝRing.·DistL- a b c)) (sym (ℝRing.·DistR- b c d))
    ∙ cong (_+ b · (c - d)) (mulComm (a - b) c)

  boundedFactorDifference : ∀ a b c (bound ε : ℚ₊) →
    absℝ c ≤ℝ rat (fst bound) → a ∼[ ε ₊／₊ bound ] b →
    absℝ (c · (a - b)) <ℝ rat (fst ε)
  boundedFactorDifference a b c bound ε c≤bound close =
    subst2 _<ℝ_ (sym (absMul c (a - b)))
      (mul-rat (fst bound) (fst (ε ₊／₊ bound)) ∙ cong rat (·／ bound ε))
      (≤<ℝ-trans
        (absℝ c · absℝ (a - b))
        (rat (fst bound) · absℝ (a - b))
        (rat (fst bound) · rat (fst (ε ₊／₊ bound)))
        (mulPres≤R-0≤ (absℝ c) (rat (fst bound)) (absℝ (a - b))
          (absNonnegative (a - b)) c≤bound)
        (mulPres<PosL (absℝ (a - b)) (rat (fst (ε ₊／₊ bound)))
          (rat (fst bound)) (<ℚ→<ℝ 0 (fst bound) (snd bound))
          (closeness→absDifference< a b (ε ₊／₊ bound) close)))

  boundedProductPreservesCloseness : ∀ a b c d (B C ε : ℚ₊) →
    absℝ b ≤ℝ rat (fst B) → absℝ c ≤ℝ rat (fst C) →
    a ∼[ (ε /2₊) ₊／₊ C ] b → c ∼[ (ε /2₊) ₊／₊ B ] d →
    a · c ∼[ ε ] b · d
  boundedProductPreservesCloseness a b c d B C ε b≤B c≤C ab cd =
    absDifference<→closeness (a · c) (b · d) ε
      (subst2 _<ℝ_ (sym (cong absℝ (productDifferencePath a b c d)))
        (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (/2+/2≡id (fst ε)))
        (≤<ℝ-trans
          (absℝ (c · (a - b) + b · (c - d)))
          (absℝ (c · (a - b)) + absℝ (b · (c - d)))
          (rat (fst (ε /2₊)) + rat (fst (ε /2₊)))
          (absTriangle (c · (a - b)) (b · (c - d)))
          (<ℝ-add
            (absℝ (c · (a - b))) (rat (fst (ε /2₊)))
            (absℝ (b · (c - d))) (rat (fst (ε /2₊)))
            (boundedFactorDifference a b c C (ε /2₊) c≤C ab)
            (boundedFactorDifference c d b B (ε /2₊) b≤B cd))))


-- All radii are chosen only for the current tolerance. Finite combinations
-- of such choices remain under propositional truncation.
module _ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) where
  private
    module Source = PremetricStr source

  constantIsRadiuswiseUniformlyContinuous : ∀ value →
    IsRadiuswiseUniformlyContinuous source (λ (_ : A) → value) (ℝPremetricSpace .snd)
  constantIsRadiuswiseUniformlyContinuous value ε =
    ∣ ε , (λ _ _ _ → refl∼ value ε) ∣₁

  sumIsRadiuswiseUniformlyContinuous : ∀ f g →
    IsRadiuswiseUniformlyContinuous source f (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source g (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source (λ x → f x + g x) (ℝPremetricSpace .snd)
  sumIsRadiuswiseUniformlyContinuous f g f-uc g-uc ε =
    PT.map2 (λ { (δf , f-near) (δg , g-near) →
      min₊ δf δg , λ x y near →
        Pℝ.subst≈ (f x + g x) (f y + g y) (/2+/2≡id (fst ε))
          (add-pres∼ (f x) (f y) (g x) (g y) (ε /2₊) (ε /2₊)
            (f-near x y (Source.isMonotone≈≤ x y (min₊ δf δg) δf
              (min₊≤L δf δg) near))
            (g-near x y (Source.isMonotone≈≤ x y (min₊ δf δg) δg
              (min₊≤R δf δg) near))) })
      (f-uc (ε /2₊)) (g-uc (ε /2₊))

  boundedProductIsRadiuswiseUniformlyContinuous : ∀ f g bound-f bound-g →
    (∀ x → absℝ (f x) ≤ℝ bound-f) →
    (∀ x → absℝ (g x) ≤ℝ bound-g) →
    IsRadiuswiseUniformlyContinuous source f (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source g (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source (λ x → f x · g x) (ℝPremetricSpace .snd)
  boundedProductIsRadiuswiseUniformlyContinuous f g bound-f bound-g
      f-bound g-bound f-uc g-uc ε =
    PT.rec2 squash₁ useBounds
      (∃naturalUpperBound bound-f) (∃naturalUpperBound bound-g)
    where
    useBounds : _ → _ → _
    useBounds (n , f<n) (m , g<m) =
      PT.map2 (λ { (δf , f-near) (δg , g-near) →
        min₊ δf δg , λ x y near →
          boundedProductPreservesCloseness (f x) (f y) (g x) (g y)
            (naturalBound n) (naturalBound m) ε
            (≤ℝ-trans (absℝ (f y)) bound-f (rat (naturalRational n))
              (f-bound y) (<ℝ-weaken bound-f (rat (naturalRational n)) f<n))
            (≤ℝ-trans (absℝ (g x)) bound-g (rat (naturalRational m))
              (g-bound x) (<ℝ-weaken bound-g (rat (naturalRational m)) g<m))
            (f-near x y (Source.isMonotone≈≤ x y (min₊ δf δg) δf
              (min₊≤L δf δg) near))
            (g-near x y (Source.isMonotone≈≤ x y (min₊ δf δg) δg
              (min₊≤R δf δg) near)) })
        (f-uc ((ε /2₊) ₊／₊ naturalBound m))
        (g-uc ((ε /2₊) ₊／₊ naturalBound n))
