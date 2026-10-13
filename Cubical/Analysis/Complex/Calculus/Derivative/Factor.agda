module Cubical.Analysis.Complex.Calculus.Derivative.Factor where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.SmallError

-- A supplied divided difference need not be obtained by division. This
-- criterion applies directly to the existing polynomial quotient identity.
opaque
  continuousComplexDifferenceFactorGivesDerivativeAt : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f : A → ℂ) d x (factor : A → ℂ) →
    (∀ y → f y -ℂ f x ≡ (coordinate y -ℂ coordinate x) ·ℂ factor y) →
    factor x ≡ d → IsContinuousAt source factor (ℂPremetricSpace .snd) x →
    IsComplexDerivativeAlongAt source coordinate f d x
  continuousComplexDifferenceFactorGivesDerivativeAt {A = A} source coordinate f d x factor
    factorization diagonal continuous =
    smallComplexErrorCong source x displacement
      (λ y → (factor y -ℂ factor x) ·ℂ displacement y)
      (complexDerivativeErrorAlong coordinate f d x) (λ y → sym (errorPath y))
      (smallComplexErrorContinuousFactor source x displacement factor continuous)
    where
    displacement : A → ℂ
    displacement y = coordinate y -ℂ coordinate x
    errorPath : ∀ y → complexDerivativeErrorAlong coordinate f d x y ≡
      (factor y -ℂ factor x) ·ℂ displacement y
    errorPath y = cong (_-ℂ d ·ℂ displacement y)
      (factorization y ∙ ·ℂComm (displacement y) (factor y))
      ∙ sym (ℂRing.·DistL- (factor y) d (displacement y))
      ∙ cong (λ v → (factor y -ℂ v) ·ℂ displacement y) (sym diagonal)
