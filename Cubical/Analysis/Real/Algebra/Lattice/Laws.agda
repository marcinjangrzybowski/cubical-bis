module Cubical.Analysis.Real.Algebra.Lattice.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Mappings
  using (identityRealMapIsContinuous; constantRealMapIsContinuous)
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Lattice.Base

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures


private
  composeContinuous :
    (f g : ℝ → ℝ) →
    isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) (f ∘ g) (ℝPremetricSpace .snd)
  composeContinuous f g f-cont g-cont =
    snd ((f , f-cont) ∘C (g , g-cont))

  identity-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (idfun ℝ) (ℝPremetricSpace .snd)
  identity-isContinuous = identityRealMapIsContinuous

  constant-isContinuous : ∀ c → isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → c) (ℝPremetricSpace .snd)
  constant-isContinuous = constantRealMapIsContinuous (ℝPremetricSpace .snd)


maxComm : ∀ x y → maxℝ x y ≡ maxℝ y x
maxComm = continuousExtensionality₂
  maxℝ (flip maxℝ)
  max-isContinuous₁ max-isContinuous₂
  max-isContinuous₂ max-isContinuous₁
  λ p q →
    max-rat p q
    ∙ cong rat (ℚ.maxComm p q)
    ∙ sym (max-rat q p)

maxAssoc : ∀ x y z →
  maxℝ x (maxℝ y z) ≡ maxℝ (maxℝ x y) z
maxAssoc = continuousExtensionality₃
  (λ x y z → maxℝ x (maxℝ y z))
  (λ x y z → maxℝ (maxℝ x y) z)
  (λ y z → max-isContinuous₁ (maxℝ y z))
  (λ x z → composeContinuous
    (maxℝ x) (λ y → maxℝ y z)
    (max-isContinuous₂ x) (max-isContinuous₁ z))
  (λ x y → composeContinuous
    (maxℝ x) (maxℝ y)
    (max-isContinuous₂ x) (max-isContinuous₂ y))
  (λ y z → composeContinuous
    (λ u → maxℝ u z) (λ x → maxℝ x y)
    (max-isContinuous₁ z) (max-isContinuous₁ y))
  (λ x z → composeContinuous
    (λ u → maxℝ u z) (maxℝ x)
    (max-isContinuous₁ z) (max-isContinuous₂ x))
  (λ x y → max-isContinuous₂ (maxℝ x y))
  λ p q r →
    cong (maxℝ (rat p)) (max-rat q r)
    ∙ max-rat p (ℚ.max q r)
    ∙ cong rat (ℚ.maxAssoc p q r)
    ∙ sym (max-rat (ℚ.max p q) r)
    ∙ cong (λ u → maxℝ u (rat r)) (sym (max-rat p q))

maxIdem : ∀ x → maxℝ x x ≡ x
maxIdem = funExt⁻
  (continuousExtensionality
    (λ x → maxℝ x x) (idfun ℝ)
    (maxOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      (idfun ℝ) (idfun ℝ)
      identity-isContinuous identity-isContinuous)
    identity-isContinuous
    λ q → max-rat q q ∙ cong rat (ℚ.maxIdem q))


minComm : ∀ x y → minℝ x y ≡ minℝ y x
minComm x y = cong (λ u → - u) (maxComm (- x) (- y))

minAssoc : ∀ x y z →
  minℝ x (minℝ y z) ≡ minℝ (minℝ x y) z
minAssoc = continuousExtensionality₃
  (λ x y z → minℝ x (minℝ y z))
  (λ x y z → minℝ (minℝ x y) z)
  (λ y z → min-isContinuous₁ (minℝ y z))
  (λ x z → composeContinuous
    (minℝ x) (λ y → minℝ y z)
    (min-isContinuous₂ x) (min-isContinuous₁ z))
  (λ x y → composeContinuous
    (minℝ x) (minℝ y)
    (min-isContinuous₂ x) (min-isContinuous₂ y))
  (λ y z → composeContinuous
    (λ u → minℝ u z) (λ x → minℝ x y)
    (min-isContinuous₁ z) (min-isContinuous₁ y))
  (λ x z → composeContinuous
    (λ u → minℝ u z) (minℝ x)
    (min-isContinuous₁ z) (min-isContinuous₂ x))
  (λ x y → min-isContinuous₂ (minℝ x y))
  λ p q r →
    cong (minℝ (rat p)) (min-rat q r)
    ∙ min-rat p (ℚ.min q r)
    ∙ cong rat (ℚ.minAssoc p q r)
    ∙ sym (min-rat (ℚ.min p q) r)
    ∙ cong (λ u → minℝ u (rat r)) (sym (min-rat p q))

minIdem : ∀ x → minℝ x x ≡ x
minIdem x = cong (λ u → - u) (maxIdem (- x)) ∙ negInvol x


maxAbsorbMin : ∀ x y → maxℝ x (minℝ x y) ≡ x
maxAbsorbMin = continuousExtensionality₂
  (λ x y → maxℝ x (minℝ x y))
  (λ x _ → x)
  (λ y → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (idfun ℝ) (λ x → minℝ x y)
    identity-isContinuous (min-isContinuous₁ y))
  (λ x → composeContinuous
    (maxℝ x) (minℝ x)
    (max-isContinuous₂ x) (min-isContinuous₂ x))
  (λ _ → identity-isContinuous)
  (λ x → constant-isContinuous x)
  λ p q →
    cong (maxℝ (rat p)) (min-rat p q)
    ∙ max-rat p (ℚ.min p q)
    ∙ cong rat (ℚ.maxAbsorbLMin p q)

minAbsorbMax : ∀ x y → minℝ x (maxℝ x y) ≡ x
minAbsorbMax = continuousExtensionality₂
  (λ x y → minℝ x (maxℝ x y))
  (λ x _ → x)
  (λ y → minOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (idfun ℝ) (λ x → maxℝ x y)
    identity-isContinuous (max-isContinuous₁ y))
  (λ x → composeContinuous
    (minℝ x) (maxℝ x)
    (min-isContinuous₂ x) (max-isContinuous₂ x))
  (λ _ → identity-isContinuous)
  (λ x → constant-isContinuous x)
  λ p q →
    cong (minℝ (rat p)) (max-rat p q)
    ∙ min-rat p (ℚ.max p q)
    ∙ cong rat (ℚ.minAbsorbLMax p q)
