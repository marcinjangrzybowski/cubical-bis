module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Power


private
  module AbstractPolarization {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)
    open RingTheory (CommRing→Ring R)

    polarization : ∀ h a b →
      h · (((a + b) · (a + b) + (- (a · a))) + (- (b · b)))
        ≡ (h + h) · (a · b)
    polarization h a b = solve! R

    polarizationDerivative : ∀ h t a b a' b' →
      h · ((((t · (a + b)) · (a' + b') + (- ((t · a) · a')))
        + (- ((t · b) · b'))))
        ≡ (h · t) · (a' · b + a · b')
    polarizationDerivative h t a b a' b' = solve! R


private
  module ℝStr = CommRingStr (snd ℝCommRing)

  two : ℕ
  two = suc (suc zero)

  halfℚ : ℚ
  halfℚ = fst (1₊ /2₊)

  halfℝ : Real.ℝ
  halfℝ = Real.ιℚ halfℚ

  twoℝ : Real.ℝ
  twoℝ = realNatural two

  half-plus-half :
    halfℝ Add.+ halfℝ ≡ Real.ιℚ 1
  half-plus-half =
    Add.add-ι-ι halfℚ halfℚ
    ∙ cong Real.ιℚ (/2+/2≡id 1)

  half-times-two :
    halfℝ Mul.· twoℝ ≡ Real.ιℚ 1
  half-times-two =
    Mul.mul-ι-ι halfℚ (ℚ.fromNat two)
    ∙ cong Real.ιℚ ℚ!

  naturalPowerDerivativeTwo : ∀ x →
    naturalPowerDerivative two x ≡ twoℝ Mul.· x
  naturalPowerDerivativeTwo x =
    cong (twoℝ Mul.·_)
      (ℝExponentiation.x^1≡x x)

  polarizedFunction :
    ∀ {ℓ} {A : Type ℓ} →
    (A → Real.ℝ) → (A → Real.ℝ) → A → Real.ℝ
  polarizedFunction f g x =
    halfℝ Mul.·
      ((((f x Add.+ g x) ^ⁿ two) Group.- (f x ^ⁿ two))
        Group.- (g x ^ⁿ two))

  polarizedDerivative :
    ∀ {ℓ} {A : Type ℓ} →
    (A → Real.ℝ) → (A → Real.ℝ) →
    (A → Real.ℝ) → (A → Real.ℝ) → A → Real.ℝ
  polarizedDerivative f g f' g' x =
    halfℝ Mul.·
      (((naturalPowerDerivative two (f x Add.+ g x) Mul.·
            (f' x Add.+ g' x))
          Group.-
        (naturalPowerDerivative two (f x) Mul.· f' x))
        Group.-
      (naturalPowerDerivative two (g x) Mul.· g' x))

  polarizationPolynomialIdentity : ∀ a b →
    ℝStr._·_ halfℝ
        (ℝStr._+_
          (ℝStr._+_
            (ℝStr._·_
              (ℝStr._+_ a b) (ℝStr._+_ a b))
            (ℝStr.-_ (ℝStr._·_ a a)))
          (ℝStr.-_ (ℝStr._·_ b b)))
      ≡
    ℝStr._·_ (ℝStr._+_ halfℝ halfℝ) (ℝStr._·_ a b)
  polarizationPolynomialIdentity a b =
    AbstractPolarization.polarization ℝCommRing halfℝ a b

  polarizationDerivativePolynomialIdentity :
    ∀ a b a' b' →
    ℝStr._·_ halfℝ
      (ℝStr._+_
        (ℝStr._+_
          (ℝStr._·_
            (ℝStr._·_ twoℝ (ℝStr._+_ a b))
            (ℝStr._+_ a' b'))
          (ℝStr.-_
            (ℝStr._·_ (ℝStr._·_ twoℝ a) a')))
        (ℝStr.-_
          (ℝStr._·_ (ℝStr._·_ twoℝ b) b')))
      ≡
    ℝStr._·_ (ℝStr._·_ halfℝ twoℝ)
      (ℝStr._+_ (ℝStr._·_ a' b) (ℝStr._·_ a b'))
  polarizationDerivativePolynomialIdentity a b a' b' =
    AbstractPolarization.polarizationDerivative
      ℝCommRing halfℝ twoℝ a b a' b'

  polarizedFunctionPath :
    ∀ {ℓ} {A : Type ℓ} (f g : A → Real.ℝ) →
    polarizedFunction f g ≡
      (λ x → f x Mul.· g x)
  polarizedFunctionPath f g =
    funExt λ x →
      cong
          (halfℝ Mul.·_)
          (cong₂ Group._-_
            (cong₂ Group._-_
              (x²EqMulSelf (f x Add.+ g x))
              (x²EqMulSelf (f x)))
            (x²EqMulSelf (g x)))
      ∙ polarizationPolynomialIdentity (f x) (g x)
      ∙ cong (Mul._· (f x Mul.· g x)) half-plus-half
      ∙ mul-one-left (f x Mul.· g x)

  polarizedDerivativePath :
    ∀ {ℓ} {A : Type ℓ}
      (f g f' g' : A → Real.ℝ) →
    polarizedDerivative f g f' g' ≡
      (λ x →
        (f' x Mul.· g x) Add.+ (f x Mul.· g' x))
  polarizedDerivativePath f g f' g' =
    funExt λ x →
      cong
          (halfℝ Mul.·_)
          (cong₂ Group._-_
            (cong₂ Group._-_
              (cong
                (Mul._· (f' x Add.+ g' x))
                (naturalPowerDerivativeTwo (f x Add.+ g x)))
              (cong
                (Mul._· f' x)
                (naturalPowerDerivativeTwo (f x))))
            (cong
              (Mul._· g' x)
              (naturalPowerDerivativeTwo (g x))))
      ∙ polarizationDerivativePolynomialIdentity
          (f x) (g x) (f' x) (g' x)
      ∙ cong
          (Mul._·
            ((f' x Mul.· g x) Add.+ (f x Mul.· g' x)))
          half-times-two
      ∙ mul-one-left
          ((f' x Mul.· g x) Add.+ (f x Mul.· g' x))


-- Polarization derives the product rule from addition, subtraction, scalar
-- multiplication, and the chain rule for squaring.  This replaces a much
-- larger direct three-error estimate and exposes useful algebraic reuse.

mulHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → Real.ℝ) →
  isContinuous source coordinate (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ x → f x Mul.· g x)
    (λ x →
      (f' x Mul.· g x) Add.+ (f x Mul.· g' x))
mulHasDerivativeAlong
  source coordinate f g f' g'
  coordinate-continuous f-derivative g-derivative =
  subst2
    (IsDerivativeAlong source coordinate)
    (polarizedFunctionPath f g)
    (polarizedDerivativePath f g f' g')
    polarized-has-derivative
  where
  sum-has-derivative :
    IsDerivativeAlong source coordinate
      (λ x → f x Add.+ g x)
      (λ x → f' x Add.+ g' x)
  sum-has-derivative =
    addHasDerivativeAlong
      source coordinate f g f' g'
      f-derivative g-derivative

  sum-square-has-derivative :
    IsDerivativeAlong source coordinate
      (λ x → (f x Add.+ g x) ^ⁿ two)
      (λ x →
        naturalPowerDerivative two (f x Add.+ g x) Mul.·
          (f' x Add.+ g' x))
  sum-square-has-derivative =
    naturalPowerCompositionHasDerivativeAlong
      source coordinate
      (λ x → f x Add.+ g x)
      (λ x → f' x Add.+ g' x)
      coordinate-continuous sum-has-derivative two

  f-square-has-derivative :
    IsDerivativeAlong source coordinate
      (λ x → f x ^ⁿ two)
      (λ x →
        naturalPowerDerivative two (f x) Mul.· f' x)
  f-square-has-derivative =
    naturalPowerCompositionHasDerivativeAlong
      source coordinate f f'
      coordinate-continuous f-derivative two

  g-square-has-derivative :
    IsDerivativeAlong source coordinate
      (λ x → g x ^ⁿ two)
      (λ x →
        naturalPowerDerivative two (g x) Mul.· g' x)
  g-square-has-derivative =
    naturalPowerCompositionHasDerivativeAlong
      source coordinate g g'
      coordinate-continuous g-derivative two

  difference-has-derivative :
    IsDerivativeAlong source coordinate
      (λ x →
        ((f x Add.+ g x) ^ⁿ two) Group.- (f x ^ⁿ two))
      (λ x →
        (naturalPowerDerivative two (f x Add.+ g x) Mul.·
            (f' x Add.+ g' x)) Group.-
        (naturalPowerDerivative two (f x) Mul.· f' x))
  difference-has-derivative =
    subHasDerivativeAlong
      source coordinate
      (λ x → (f x Add.+ g x) ^ⁿ two)
      (λ x → f x ^ⁿ two)
      (λ x →
        naturalPowerDerivative two (f x Add.+ g x) Mul.·
          (f' x Add.+ g' x))
      (λ x → naturalPowerDerivative two (f x) Mul.· f' x)
      sum-square-has-derivative f-square-has-derivative

  unscaled-has-derivative :
    IsDerivativeAlong source coordinate
      (λ x →
        (((f x Add.+ g x) ^ⁿ two) Group.- (f x ^ⁿ two))
          Group.- (g x ^ⁿ two))
      (λ x →
        ((naturalPowerDerivative two (f x Add.+ g x) Mul.·
            (f' x Add.+ g' x)) Group.-
          (naturalPowerDerivative two (f x) Mul.· f' x))
          Group.-
        (naturalPowerDerivative two (g x) Mul.· g' x))
  unscaled-has-derivative =
    subHasDerivativeAlong
      source coordinate
      (λ x →
        ((f x Add.+ g x) ^ⁿ two) Group.- (f x ^ⁿ two))
      (λ x → g x ^ⁿ two)
      (λ x →
        (naturalPowerDerivative two (f x Add.+ g x) Mul.·
            (f' x Add.+ g' x)) Group.-
        (naturalPowerDerivative two (f x) Mul.· f' x))
      (λ x → naturalPowerDerivative two (g x) Mul.· g' x)
      difference-has-derivative g-square-has-derivative

  polarized-has-derivative :
    IsDerivativeAlong source coordinate
      (polarizedFunction f g)
      (polarizedDerivative f g f' g')
  polarized-has-derivative =
    scaleHasDerivativeAlong
      source coordinate
      (λ x →
        (((f x Add.+ g x) ^ⁿ two) Group.- (f x ^ⁿ two))
          Group.- (g x ^ⁿ two))
      (λ x →
        ((naturalPowerDerivative two (f x Add.+ g x) Mul.·
            (f' x Add.+ g' x)) Group.-
          (naturalPowerDerivative two (f x) Mul.· f' x))
          Group.-
        (naturalPowerDerivative two (g x) Mul.· g' x))
      halfℝ unscaled-has-derivative


mulHasDerivative :
  ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x Mul.· g x)
    (λ x →
      (f' x Mul.· g x) Add.+ (f x Mul.· g' x))
mulHasDerivative f g f' g' f-derivative g-derivative =
  mulHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)
    f g f' g'
    (snd
      (CategoryStructures.idᶜ
        {M = Real.ℝPremetricSpace}))
    f-derivative g-derivative
