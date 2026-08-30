module Cubical.Analysis.Real.Order.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition

open import Cubical.Relation.Premetric.Mappings

open CategoryStructures
open OrderedCommRingTheory ℚOrderedCommRing


private
  constantZero-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → 0ℝ) (ℝPremetricSpace .snd)
  constantZero-isContinuous = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (λ (_ : ℝ) → 0ℝ) (ℝPremetricSpace .snd)
    λ where
      .IsNonExpanding.pres≈ _ _ ε _ → refl∼ 0ℝ ε


absAsMax : ∀ x → absℝ x ≡ maxℝ x (- x)
absAsMax = funExt⁻
  (continuousExtensionality
    absℝ (λ x → maxℝ x (- x))
    abs-isContinuous
    (maxOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      (idfun ℝ) -_
      (isNonExpanding→isContinuous
        (ℝPremetricSpace .snd) (idfun ℝ) (ℝPremetricSpace .snd)
        (snd (idⁿ {M = ℝPremetricSpace})))
      neg-isContinuous)
    λ q →
      abs-rat q
      ∙ sym (max-rat q (ℚ.- q))
      ∙ cong (maxℝ (rat q)) (sym (neg-rat q)))

leAbs : ∀ x → x ≤ℝ absℝ x
leAbs x = subst (x ≤ℝ_)
  (sym (absAsMax x)) (left≤max x (- x))

negLeAbs : ∀ x → (- x) ≤ℝ absℝ x
negLeAbs x = subst ((- x) ≤ℝ_)
  (sym (absAsMax x)) (right≤max x (- x))

absNonnegative : ∀ x → 0ℝ ≤ℝ absℝ x
absNonnegative = funExt⁻
  (continuousExtensionality
    (λ x → maxℝ 0ℝ (absℝ x)) absℝ
    (maxOfContinuousIsContinuous
      (ℝPremetricSpace .snd)
      (λ _ → 0ℝ) absℝ
      constantZero-isContinuous abs-isContinuous)
    abs-isContinuous
    λ q →
      cong (maxℝ 0ℝ) (abs-rat q)
      ∙ max-rat 0 (abs q)
      ∙ cong rat (ℚ.≤→max 0 (abs q) (0≤abs q))
      ∙ sym (abs-rat q))

isNonnegative→0≤ : ∀ x → IsNonnegative x → 0ℝ ≤ℝ x
isNonnegative→0≤ x fixed =
  subst (0ℝ ≤ℝ_) fixed (absNonnegative x)

0≤→isNonnegative : ∀ x → 0ℝ ≤ℝ x → IsNonnegative x
0≤→isNonnegative x 0≤x =
  absAsMax x
  ∙ maxComm x (- x)
  ∙ neg≤x
  where
  neg≤0 : (- x) ≤ℝ 0ℝ
  neg≤0 = subst2 _≤ℝ_ (addIdL (- x)) (addInvR x)
    (addPres≤R 0ℝ x (- x) 0≤x)

  neg≤x : (- x) ≤ℝ x
  neg≤x = ≤ℝ-trans (- x) 0ℝ x neg≤0 0≤x

isNonnegative≃0≤ : ∀ x →
  IsNonnegative x ≃ (0ℝ ≤ℝ x)
isNonnegative≃0≤ x = propBiimpl→Equiv
  (isPropIsNonnegative x) (isProp≤ℝ 0ℝ x)
  (isNonnegative→0≤ x) (0≤→isNonnegative x)

absOfNonnegative : ∀ x → 0ℝ ≤ℝ x → absℝ x ≡ x
absOfNonnegative = 0≤→isNonnegative

nonnegativeSub : ∀ x y → x ≤ℝ y → 0ℝ ≤ℝ y - x
nonnegativeSub x y x≤y =
  subst2 _≤ℝ_ (subSelf x) refl
    (addPres≤R x y (- x) x≤y)
