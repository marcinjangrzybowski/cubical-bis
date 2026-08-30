module Cubical.Analysis.Real.Algebra.Lattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.FunctionSpace

import Cubical.Analysis.Completion.BinaryNonExpanding
  as BinaryLiftDefinition

private
  module RationalBinaryMax = BinaryNonExpanding
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace
  module RealBinaryMax = BinaryNonExpanding
    ℝPremetricSpace ℝPremetricSpace ℝPremetricSpace
  module MaxLift = BinaryLiftDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

open CategoryStructures
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing

private module Pℝ = PremetricStr (ℝPremetricSpace .snd)


private
  maxℚ₂ : RationalBinaryMax.NE₂[_,_,_]
  maxℚ₂ .RationalBinaryMax.NE₂[_,_,_].fun = ℚ.max
  maxℚ₂ .RationalBinaryMax.NE₂[_,_,_].leftNE y
    .IsNonExpanding.pres≈ x x' ε x≈x' =
    subst (ℚ._< fst ε)
      (cong abs
        (cong₂ ℚ._-_ (ℚ.maxComm y x) (ℚ.maxComm y x')))
      (ℚ.isTrans≤< _ _ _ (ℚ.maxDist y x' x) x≈x')
  maxℚ₂ .RationalBinaryMax.NE₂[_,_,_].rightNE x
    .IsNonExpanding.pres≈ y y' ε y≈y' =
    ℚ.isTrans≤< _ _ _ (ℚ.maxDist x y' y) y≈y'


private
  max₂ : RealBinaryMax.NE₂[_,_,_]
  max₂ = MaxLift.liftBinaryNonExpanding maxℚ₂

maxℝ : ℝ → ℝ → ℝ
maxℝ = RealBinaryMax.NE₂[_,_,_].fun max₂

max-rat : ∀ p q → maxℝ (rat p) (rat q) ≡ rat (ℚ.max p q)
max-rat = MaxLift.liftBinaryNonExpanding-ι maxℚ₂

max-isNonExpanding₁ : ∀ y → IsNonExpanding
  (ℝPremetricSpace .snd) (flip maxℝ y) (ℝPremetricSpace .snd)
max-isNonExpanding₁ = RealBinaryMax.NE₂[_,_,_].leftNE max₂

max-isNonExpanding₂ : ∀ x → IsNonExpanding
  (ℝPremetricSpace .snd) (maxℝ x) (ℝPremetricSpace .snd)
max-isNonExpanding₂ = RealBinaryMax.NE₂[_,_,_].rightNE max₂

max-isContinuous₁ : ∀ y → isContinuous
  (ℝPremetricSpace .snd) (flip maxℝ y) (ℝPremetricSpace .snd)
max-isContinuous₁ y = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (flip maxℝ y) (ℝPremetricSpace .snd)
  (max-isNonExpanding₁ y)

max-isContinuous₂ : ∀ x → isContinuous
  (ℝPremetricSpace .snd) (maxℝ x) (ℝPremetricSpace .snd)
max-isContinuous₂ x = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (maxℝ x) (ℝPremetricSpace .snd)
  (max-isNonExpanding₂ x)

max-pres∼₁ : ∀ x x' y ε →
  x ∼[ ε ] x' → maxℝ x y ∼[ ε ] maxℝ x' y
max-pres∼₁ x x' y ε =
  max-isNonExpanding₁ y .IsNonExpanding.pres≈ x x' ε

max-pres∼₂ : ∀ x y y' ε →
  y ∼[ ε ] y' → maxℝ x y ∼[ ε ] maxℝ x y'
max-pres∼₂ x y y' ε =
  max-isNonExpanding₂ x .IsNonExpanding.pres≈ y y' ε


minℝ : ℝ → ℝ → ℝ
minℝ x y = - maxℝ (- x) (- y)

min-rat : ∀ p q → minℝ (rat p) (rat q) ≡ rat (ℚ.min p q)
min-rat p q =
  cong -_ (cong₂ maxℝ (neg-rat p) (neg-rat q))
  ∙ cong -_ (max-rat (ℚ.- p) (ℚ.- q))
  ∙ neg-rat (ℚ.max (ℚ.- p) (ℚ.- q))
  ∙ cong rat
      (cong ℚ.-_ (ℚ.maxNeg≡negMin p q)
      ∙ ℚ.-Invol (ℚ.min p q))

min-isNonExpanding₁ : ∀ y → IsNonExpanding
  (ℝPremetricSpace .snd) (flip minℝ y) (ℝPremetricSpace .snd)
min-isNonExpanding₁ y = snd
  ((-_ , neg-isNonExpanding) ∘NE
    (((λ x → maxℝ x (- y)) , max-isNonExpanding₁ (- y)) ∘NE
      (-_ , neg-isNonExpanding)))

min-isNonExpanding₂ : ∀ x → IsNonExpanding
  (ℝPremetricSpace .snd) (minℝ x) (ℝPremetricSpace .snd)
min-isNonExpanding₂ x = snd
  ((-_ , neg-isNonExpanding) ∘NE
    ((maxℝ (- x) , max-isNonExpanding₂ (- x)) ∘NE
      (-_ , neg-isNonExpanding)))

min-isContinuous₁ : ∀ y → isContinuous
  (ℝPremetricSpace .snd) (flip minℝ y) (ℝPremetricSpace .snd)
min-isContinuous₁ y = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (flip minℝ y) (ℝPremetricSpace .snd)
  (min-isNonExpanding₁ y)

min-isContinuous₂ : ∀ x → isContinuous
  (ℝPremetricSpace .snd) (minℝ x) (ℝPremetricSpace .snd)
min-isContinuous₂ x = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (minℝ x) (ℝPremetricSpace .snd)
  (min-isNonExpanding₂ x)

private
  min₂ : RealBinaryMax.NE₂[_,_,_]
  min₂ .RealBinaryMax.NE₂[_,_,_].fun = minℝ
  min₂ .RealBinaryMax.NE₂[_,_,_].leftNE = min-isNonExpanding₁
  min₂ .RealBinaryMax.NE₂[_,_,_].rightNE = min-isNonExpanding₂


module _
  {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  where

  private
    binaryOfContinuousIsContinuous :
      (operation : RealBinaryMax.NE₂[_,_,_]) →
      (f g : A → ℝ) →
      isContinuous source f (ℝPremetricSpace .snd) →
      isContinuous source g (ℝPremetricSpace .snd) →
      isContinuous source
        (λ x → RealBinaryMax.NE₂[_,_,_].fun operation (f x) (g x))
        (ℝPremetricSpace .snd)
    binaryOfContinuousIsContinuous operation f g f-cont g-cont x
      .IsContinuousAt.pres≈ ε = PT.map2
        (λ (δf , f-near) (δg , g-near) →
          min₊ δf δg
          , λ y x≈y →
              Pℝ.subst≈ _ _ (/2+/2≡id (fst ε))
                (Pℝ.isTriangular≈
                  _
                  (RealBinaryMax.NE₂[_,_,_].fun operation (f y) (g x))
                  _
                  (ε /2₊) (ε /2₊)
                  (RealBinaryMax.NE₂[_,_,_].leftNE operation (g x)
                    .IsNonExpanding.pres≈ _ _ _
                    (f-near y
                      (PremetricStr.isMonotone≈≤ source
                        x y (min₊ δf δg) δf
                        (min₊≤L δf δg) x≈y)))
                  (RealBinaryMax.NE₂[_,_,_].rightNE operation (f y)
                    .IsNonExpanding.pres≈ _ _ _
                    (g-near y
                      (PremetricStr.isMonotone≈≤ source
                        x y (min₊ δf δg) δg
                        (min₊≤R δf δg) x≈y)))))
        (f-cont x .IsContinuousAt.pres≈ (ε /2₊))
        (g-cont x .IsContinuousAt.pres≈ (ε /2₊))

  maxOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (ℝPremetricSpace .snd) →
    isContinuous source g (ℝPremetricSpace .snd) →
    isContinuous source (λ x → maxℝ (f x) (g x))
      (ℝPremetricSpace .snd)
  maxOfContinuousIsContinuous =
    binaryOfContinuousIsContinuous max₂

  minOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (ℝPremetricSpace .snd) →
    isContinuous source g (ℝPremetricSpace .snd) →
    isContinuous source (λ x → minℝ (f x) (g x))
      (ℝPremetricSpace .snd)
  minOfContinuousIsContinuous =
    binaryOfContinuousIsContinuous min₂
