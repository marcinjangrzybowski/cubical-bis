module Cubical.Analysis.Real.Order.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Mappings
  using (constantRealMapIsContinuous)
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures
open OrderedCommRingTheory ℚOrderedCommRing


private
  composeContinuous :
    (f g : ℝ → ℝ) →
    isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
    isContinuous (ℝPremetricSpace .snd) (f ∘ g) (ℝPremetricSpace .snd)
  composeContinuous f g f-cont g-cont =
    snd ((f , f-cont) ∘C (g , g-cont))

  constant-isContinuous : ∀ c → isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → c) (ℝPremetricSpace .snd)
  constant-isContinuous = constantRealMapIsContinuous (ℝPremetricSpace .snd)


mulMaxAbs : ∀ x y z →
  maxℝ x y · absℝ z ≡
  maxℝ (x · absℝ z) (y · absℝ z)
mulMaxAbs = continuousExtensionality₃
  (λ x y z → maxℝ x y · absℝ z)
  (λ x y z → maxℝ (x · absℝ z) (y · absℝ z))
  (λ y z → composeContinuous
    (_· absℝ z) (λ x → maxℝ x y)
    (mul-isContinuous₁ (absℝ z)) (max-isContinuous₁ y))
  (λ x z → composeContinuous
    (_· absℝ z) (maxℝ x)
    (mul-isContinuous₁ (absℝ z)) (max-isContinuous₂ x))
  (λ x y → composeContinuous
    (maxℝ x y ·_) absℝ
    (mul-isContinuous₂ (maxℝ x y)) abs-isContinuous)
  (λ y z → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (_· absℝ z) (λ _ → y · absℝ z)
    (mul-isContinuous₁ (absℝ z))
    (constant-isContinuous (y · absℝ z)))
  (λ x z → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (λ _ → x · absℝ z) (_· absℝ z)
    (constant-isContinuous (x · absℝ z))
    (mul-isContinuous₁ (absℝ z)))
  (λ x y → maxOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (λ z → x · absℝ z) (λ z → y · absℝ z)
    (composeContinuous (x ·_) absℝ
      (mul-isContinuous₂ x) abs-isContinuous)
    (composeContinuous (y ·_) absℝ
      (mul-isContinuous₂ y) abs-isContinuous))
  λ p q r →
    cong₂ _·_ (max-rat p q) (abs-rat r)
    ∙ mul-rat (ℚ.max p q) (abs r)
    ∙ cong rat (ℚ.·MaxDistrℚ' p q (abs r) (0≤abs r))
    ∙ sym (max-rat (p ℚ.· abs r) (q ℚ.· abs r))
    ∙ cong₂ maxℝ
        (sym (mul-rat p (abs r))
          ∙ cong (rat p ·_) (sym (abs-rat r)))
        (sym (mul-rat q (abs r))
          ∙ cong (rat q ·_) (sym (abs-rat r)))

mulMaxNonnegative : ∀ x y z → IsNonnegative z →
  maxℝ x y · z ≡ maxℝ (x · z) (y · z)
mulMaxNonnegative x y z z≥0 =
  cong (maxℝ x y ·_) (sym z≥0)
  ∙ mulMaxAbs x y z
  ∙ cong₂ maxℝ
      (cong (x ·_) z≥0)
      (cong (y ·_) z≥0)

mulPres≤R : ∀ x y z →
  IsNonnegative z → x ≤ℝ y → x · z ≤ℝ y · z
mulPres≤R x y z z≥0 x≤y =
  sym (mulMaxNonnegative x y z z≥0)
  ∙ cong (_· z) x≤y

mulPres≤L : ∀ x y z →
  IsNonnegative z → x ≤ℝ y → z · x ≤ℝ z · y
mulPres≤L x y z z≥0 x≤y = subst2 _≤ℝ_
  (mulComm x z) (mulComm y z)
  (mulPres≤R x y z z≥0 x≤y)

mulPres≤R-0≤ : ∀ x y z →
  0ℝ ≤ℝ z → x ≤ℝ y → x · z ≤ℝ y · z
mulPres≤R-0≤ x y z 0≤z =
  mulPres≤R x y z (0≤→isNonnegative z 0≤z)

mulPres≤ : ∀ x y z w →
  0ℝ ≤ℝ y → 0ℝ ≤ℝ z →
  x ≤ℝ y → z ≤ℝ w → x · z ≤ℝ y · w
mulPres≤ x y z w 0≤y 0≤z x≤y z≤w =
  ≤ℝ-trans (x · z) (y · z) (y · w)
    (mulPres≤R-0≤ x y z 0≤z x≤y)
    (mulPres≤L z w y (0≤→isNonnegative y 0≤y) z≤w)
