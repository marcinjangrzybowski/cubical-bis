module Cubical.Analysis.Complex.Calculus.Derivative.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Norm.Metric
open import Cubical.Analysis.Complex.Metric

private module P = PremetricStr (ℂPremetricSpace .snd)

opaque
  complexNormRationalBound : ∀ z → ∃[ B ∈ ℚ₊ ] normℂ z ≤ℝ rat (fst B)
  complexNormRationalBound z = do
    (n , bound) ← ∃naturalUpperBound (normℂ z)
    return (naturalBound n , <ℝ-weaken (normℂ z) (rat (naturalRational n)) bound)

  halfNormCloseness : ∀ z w ε → z ∼ℂ[ ε /2₊ ] w → normℂ (z -ℂ w) <ℝ rat (fst ε)
  halfNormCloseness z w ε close = subst (normℂ (z -ℂ w) <ℝ_)
    (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (/2+/2≡id (fst ε)))
    (closeness→normℂ-difference< z w (ε /2₊) close)

  continuousComplexNormDifferenceAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (f : A → ℂ) x →
    IsContinuousAt source f (ℂPremetricSpace .snd) x → ∀ (ε : ℚ₊) →
    ∃[ δ ∈ ℚ₊ ] (∀ y → PremetricStr._≈[_]_ source x δ y →
      normℂ (f y -ℂ f x) <ℝ rat (fst ε))
  continuousComplexNormDifferenceAt source f x continuous ε = do
    (δ , near) ← continuous .IsContinuousAt.pres≈ (ε /2₊)
    return (δ , λ y close → halfNormCloseness (f y) (f x) ε
      (P.isSym≈ (f x) (f y) (ε /2₊) (near y close)))

  continuousComplexNormBoundAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (f : A → ℂ) x →
    IsContinuousAt source f (ℂPremetricSpace .snd) x →
    ∃[ B ∈ ℚ₊ ] ∃[ δ ∈ ℚ₊ ]
      (∀ y → PremetricStr._≈[_]_ source x δ y → normℂ (f y) ≤ℝ rat (fst B))
  continuousComplexNormBoundAt source f x continuous = do
    (B , bounded) ← complexNormRationalBound (f x)
    (δ , near) ← continuousComplexNormDifferenceAt source f x continuous 1₊
    return (1₊ +₊ B , return (δ , λ y close →
      subst2 _≤ℝ_ (cong normℂ (ℂRing.minusPlus (f y) (f x))) (rat+rat 1 (fst B))
        (normℂ-addBound (f y -ℂ f x) (f x) (rat 1) (rat (fst B))
          (<ℝ-weaken (normℂ (f y -ℂ f x)) (rat 1) (near y close)) bounded)))

  halfErrorSum : ∀ ε distance →
    rat (fst (ε /2₊)) · distance + rat (fst (ε /2₊)) · distance ≡ rat (fst ε) · distance
  halfErrorSum ε distance = sym (mulDistL (rat (fst (ε /2₊))) (rat (fst (ε /2₊))) distance)
    ∙ cong (_· distance) (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (/2+/2≡id (fst ε)))

  rationalScaleCancel : ∀ B ε distance →
    rat (fst B) · (rat (fst (ε ₊／₊ B)) · distance) ≡ rat (fst ε) · distance
  rationalScaleCancel B ε distance = mulAssoc (rat (fst B)) (rat (fst (ε ₊／₊ B))) distance
    ∙ cong (_· distance) (mul-rat (fst B) (fst (ε ₊／₊ B)) ∙ cong rat (·／ B ε))

  boundedComplexErrorProduct : ∀ value error distance B ε →
    normℂ value ≤ℝ rat (fst B) →
    normℂ error ≤ℝ rat (fst (ε ₊／₊ B)) · distance →
    normℂ (value ·ℂ error) ≤ℝ rat (fst ε) · distance
  boundedComplexErrorProduct value error distance B ε bound small =
    subst (normℂ (value ·ℂ error) ≤ℝ_) (rationalScaleCancel B ε distance)
      (normℂ-mulBound value error (rat (fst B)) (rat (fst (ε ₊／₊ B)) · distance) bound small)

  complexErrorThroughLinearInput : ∀ error input distance B ε →
    normℂ error ≤ℝ rat (fst (ε ₊／₊ B)) · input →
    input ≤ℝ rat (fst B) · distance → normℂ error ≤ℝ rat (fst ε) · distance
  complexErrorThroughLinearInput error input distance B ε small bound =
    ≤ℝ-trans (normℂ error) (rat (fst (ε ₊／₊ B)) · input) (rat (fst ε) · distance) small
      (subst (rat (fst (ε ₊／₊ B)) · input ≤ℝ_)
        (mulAssoc (rat (fst (ε ₊／₊ B))) (rat (fst B)) distance
          ∙ cong (_· distance) (mulComm (rat (fst (ε ₊／₊ B))) (rat (fst B)) ∙ mul-rat (fst B) (fst (ε ₊／₊ B))
            ∙ cong rat (·／ B ε)))
        (mulPres≤L input (rat (fst B) · distance) (rat (fst (ε ₊／₊ B)))
          (0≤→isNonnegative (rat (fst (ε ₊／₊ B)))
            (<ℝ-weaken 0ℝ (rat (fst (ε ₊／₊ B))) (positiveSlack (ε ₊／₊ B)))) bound))

  rationalLinearBoundGivesCloseness : ∀ z w input B ε →
    normℂ (w -ℂ z) ≤ℝ rat (fst B) · input →
    input <ℝ rat (fst (ε ₊／₊ B)) → z ∼ℂ[ ε ] w
  rationalLinearBoundGivesCloseness z w input B ε bound small =
    P.isSym≈ w z ε (normℂ-difference<→closeness w z ε
      (≤<ℝ-trans (normℂ (w -ℂ z)) (rat (fst B) · input) (rat (fst ε)) bound
        (subst (rat (fst B) · input <ℝ_)
          (mul-rat (fst B) (fst (ε ₊／₊ B)) ∙ cong rat (·／ B ε))
          (mulPres<PosL input (rat (fst (ε ₊／₊ B))) (rat (fst B)) (positiveSlack B) small))))
