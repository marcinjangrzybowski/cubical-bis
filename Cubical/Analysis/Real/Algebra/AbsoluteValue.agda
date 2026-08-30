module Cubical.Analysis.Real.Algebra.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.UniversalProperty
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Analysis.Completion.NonExpanding
  as NonExpandingDefinition

private module AbsLift = NonExpandingDefinition ℚPremetricSpace ℚPremetricSpace

open CategoryStructures
open OrderedCommRingTheory ℚOrderedCommRing


private
  absAbsDistance≤ : ∀ x y →
    abs (abs x ℚ.- abs y) ≤ℚ abs (x ℚ.- y)
  absAbsDistance≤ x y =
    ℚ.absFrom≤×≤ distance difference lowerBound upperBound
    where
    distance = abs (x ℚ.- y)
    difference = abs x ℚ.- abs y

    upperBound : difference ≤ℚ distance
    upperBound = abs-abs≤abs- x y

    swapped : abs y ℚ.- abs x ≤ℚ distance
    swapped = subst ((abs y ℚ.- abs x) ≤ℚ_)
      (abs-Comm y x) (abs-abs≤abs- y x)

    lowerBound : ℚ.- distance ≤ℚ difference
    lowerBound = subst ((ℚ.- distance) ≤ℚ_)
      (ℚ.-[x-y]≡y-x (abs y) (abs x))
      (ℚ.minus-≤ (abs y ℚ.- abs x) distance swapped)

  absℚⁿ : NE[ ℚPremetricSpace , ℚPremetricSpace ]
  absℚⁿ .fst = abs
  absℚⁿ .snd .IsNonExpanding.pres≈ x y ε x≈y =
    ℚ.isTrans≤< _ _ _ (absAbsDistance≤ x y) x≈y

  absℝⁿ : NE[ ℝPremetricSpace , ℝPremetricSpace ]
  absℝⁿ = AbsLift.liftNonExpanding absℚⁿ


absℝ : ℝ → ℝ
absℝ = fst absℝⁿ

abs-rat : ∀ q → absℝ (rat q) ≡ rat (abs q)
abs-rat = AbsLift.liftNonExpanding-ι absℚⁿ

abs-isNonExpanding : IsNonExpanding
  (ℝPremetricSpace .snd) absℝ (ℝPremetricSpace .snd)
abs-isNonExpanding = snd absℝⁿ

abs-isUniformlyContinuous : isUniformlyContinuous
  (ℝPremetricSpace .snd) absℝ (ℝPremetricSpace .snd)
abs-isUniformlyContinuous = isNonExpanding→isUniformlyContinuous
  (ℝPremetricSpace .snd) absℝ (ℝPremetricSpace .snd)
  abs-isNonExpanding

abs-isContinuous : isContinuous
  (ℝPremetricSpace .snd) absℝ (ℝPremetricSpace .snd)
abs-isContinuous = isUniformlyContinuous→isContinuous
  (ℝPremetricSpace .snd) absℝ (ℝPremetricSpace .snd)
  abs-isUniformlyContinuous

abs-pres∼ : ∀ x y ε →
  x ∼[ ε ] y → absℝ x ∼[ ε ] absℝ y
abs-pres∼ x y ε =
  abs-isNonExpanding .IsNonExpanding.pres≈ x y ε

private
  absAfterNeg-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (absℝ ∘ -_) (ℝPremetricSpace .snd)
  absAfterNeg-isContinuous = snd
    ((absℝ , abs-isContinuous) ∘C (-_ , neg-isContinuous))

  absAfterAbs-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (absℝ ∘ absℝ) (ℝPremetricSpace .snd)
  absAfterAbs-isContinuous = snd
    ((absℝ , abs-isContinuous) ∘C (absℝ , abs-isContinuous))


absNeg : ∀ x → absℝ (- x) ≡ absℝ x
absNeg = funExt⁻
  (continuousExtensionality
    (absℝ ∘ -_) absℝ
    absAfterNeg-isContinuous abs-isContinuous
    λ q →
      cong absℝ (neg-rat q)
      ∙ abs-rat (ℚ.- q)
      ∙ cong rat (sym (ℚ.-abs q))
      ∙ sym (abs-rat q))

absIdem : ∀ x → absℝ (absℝ x) ≡ absℝ x
absIdem = funExt⁻
  (continuousExtensionality
    (absℝ ∘ absℝ) absℝ
    absAfterAbs-isContinuous abs-isContinuous
    λ q →
      cong absℝ (abs-rat q)
      ∙ abs-rat (abs q)
      ∙ cong rat (0≤→abs≡id (abs q) (0≤abs q))
      ∙ sym (abs-rat q))

absZero : absℝ (rat 0) ≡ rat 0
absZero = abs-rat 0
  ∙ cong rat (0≤→abs≡id 0 (ℚ.isRefl≤ 0))

absOne : absℝ 1ℝ ≡ 1ℝ
absOne = abs-rat 1
  ∙ cong rat (0≤→abs≡id 1 0≤1)

absMul : ∀ x y →
  absℝ (x · y) ≡ absℝ x · absℝ y
absMul = continuousExtensionality₂
  (λ x y → absℝ (x · y))
  (λ x y → absℝ x · absℝ y)
  (λ y → snd
    ((absℝ , abs-isContinuous) ∘C
      (_· y , mul-isContinuous₁ y)))
  (λ x → snd
    ((absℝ , abs-isContinuous) ∘C
      (x ·_ , mul-isContinuous₂ x)))
  (λ y → snd
    ((_· absℝ y , mul-isContinuous₁ (absℝ y)) ∘C
      (absℝ , abs-isContinuous)))
  (λ x → snd
    ((absℝ x ·_ , mul-isContinuous₂ (absℝ x)) ∘C
      (absℝ , abs-isContinuous)))
  λ p q →
    cong absℝ (mul-rat p q)
    ∙ abs-rat (p ℚ.· q)
    ∙ cong rat (sym (abs·abs p q))
    ∙ sym (mul-rat (abs p) (abs q))
    ∙ cong₂ _·_ (sym (abs-rat p)) (sym (abs-rat q))

absSquared : ∀ x → absℝ x · absℝ x ≡ x · x
absSquared = funExt⁻
  (continuousExtensionality
    (λ x → absℝ x · absℝ x)
    (λ x → x · x)
    (mulOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      absℝ absℝ abs-isContinuous abs-isContinuous)
    (mulOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      (λ x → x) (λ x → x)
      (isNonExpanding→isContinuous
        (ℝPremetricSpace .snd) (λ x → x) (ℝPremetricSpace .snd)
        λ where
          .IsNonExpanding.pres≈ _ _ _ x∼y → x∼y)
      (isNonExpanding→isContinuous
        (ℝPremetricSpace .snd) (λ x → x) (ℝPremetricSpace .snd)
        λ where
          .IsNonExpanding.pres≈ _ _ _ x∼y → x∼y))
    λ q →
      cong₂ _·_ (abs-rat q) (abs-rat q)
      ∙ mul-rat (abs q) (abs q)
      ∙ cong rat (abs·abs q q)
      ∙ cong rat (0≤→abs≡id (q ℚ.· q) (0≤² q))
      ∙ sym (mul-rat q q))

absAddAbs : ∀ x y →
  absℝ (absℝ x + absℝ y) ≡ absℝ x + absℝ y
absAddAbs = continuousExtensionality₂
  (λ x y → absℝ (absℝ x + absℝ y))
  (λ x y → absℝ x + absℝ y)
  (λ y → snd (NE→C
    ((absℝ , abs-isNonExpanding) ∘NE
      (((_+ absℝ y) , add-isNonExpanding₁ (absℝ y)) ∘NE
        (absℝ , abs-isNonExpanding)))))
  (λ x → snd (NE→C
    ((absℝ , abs-isNonExpanding) ∘NE
      (((absℝ x +_) , add-isNonExpanding₂ (absℝ x)) ∘NE
        (absℝ , abs-isNonExpanding)))))
  (λ y → snd (NE→C
    (((_+ absℝ y) , add-isNonExpanding₁ (absℝ y)) ∘NE
      (absℝ , abs-isNonExpanding))))
  (λ x → snd (NE→C
    (((absℝ x +_) , add-isNonExpanding₂ (absℝ x)) ∘NE
      (absℝ , abs-isNonExpanding))))
  λ p q →
    cong absℝ (cong₂ _+_ (abs-rat p) (abs-rat q))
    ∙ cong absℝ (rat+rat (abs p) (abs q))
    ∙ abs-rat (abs p ℚ.+ abs q)
    ∙ cong rat (0≤→abs≡id (abs p ℚ.+ abs q)
        (isTrans≤ 0 (abs p) (abs p ℚ.+ abs q)
          (0≤abs p) (≤SumLeftNonNeg (abs p) (abs q) (0≤abs q))))
    ∙ sym (rat+rat (abs p) (abs q))
    ∙ cong₂ _+_ (sym (abs-rat p)) (sym (abs-rat q))
