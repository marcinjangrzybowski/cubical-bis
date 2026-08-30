module Cubical.Analysis.Real.Algebra.Negation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Analysis.Real.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Analysis.Completion.NonExpanding
  as NonExpandingDefinition

private module NE = NonExpandingDefinition ℚPremetricSpace ℚPremetricSpace

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)


negateℚ : ℚ → ℚ
negateℚ q = ℚ.- q

private
  negatedDistance : ∀ x y →
    abs ((ℚ.- x) ℚ.- (ℚ.- y)) ≡ abs (x ℚ.- y)
  negatedDistance x y =
    cong abs
      (cong ((ℚ.- x) ℚ.+_) (ℚRing.-Idempotent y)
        ∙ ℚ.+Comm (ℚ.- x) y)
    ∙ abs-Comm y x

  negateℚⁿ : NE[ ℚPremetricSpace , ℚPremetricSpace ]
  fst negateℚⁿ = negateℚ
  negateℚⁿ .snd .IsNonExpanding.pres≈ x y ε x≈y =
    subst (ℚ._< fst ε) (sym (negatedDistance x y)) x≈y


infix 8 -_

-_ : ℝ → ℝ
-_ = fst (NE.liftNonExpanding negateℚⁿ)

neg-rat : ∀ q → - rat q ≡ rat (ℚ.- q)
neg-rat = NE.liftNonExpanding-ι negateℚⁿ

neg-isNonExpanding : IsNonExpanding
  (ℝPremetricSpace .snd) -_ (ℝPremetricSpace .snd)
neg-isNonExpanding = snd (NE.liftNonExpanding negateℚⁿ)

neg-isUniformlyContinuous :
  isUniformlyContinuous
    (ℝPremetricSpace .snd) -_ (ℝPremetricSpace .snd)
neg-isUniformlyContinuous =
  isNonExpanding→isUniformlyContinuous
    (ℝPremetricSpace .snd) -_ (ℝPremetricSpace .snd)
    neg-isNonExpanding

neg-isContinuous :
  isContinuous (ℝPremetricSpace .snd) -_ (ℝPremetricSpace .snd)
neg-isContinuous = isUniformlyContinuous→isContinuous
  (ℝPremetricSpace .snd) -_ (ℝPremetricSpace .snd)
  neg-isUniformlyContinuous

neg-presCauchy : ∀ x →
  PremetricTheory.isCauchySeq ℝPremetricSpace x →
  PremetricTheory.isCauchySeq ℝPremetricSpace (-_ ∘ x)
neg-presCauchy = NE→presIsCauchySeq (-_ , neg-isNonExpanding)
