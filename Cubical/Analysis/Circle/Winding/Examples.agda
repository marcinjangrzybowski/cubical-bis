module Cubical.Analysis.Circle.Winding.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using ([_/_])
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (idᵘᶜ; _∘UC_)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Circle.Base
open import Cubical.Analysis.Circle.Metric
open import Cubical.Analysis.Circle.Winding

private
  module R = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)
  standard-step : ∀ x y → cover x +ᶜ cover (y - x) ≡ cover y
  standard-step x y = sym (cover-add x (y - x))
    ∙ cong cover (addComm x (y - x) ∙ subAddCancel y x)

winding-one-turn : windingLoop coverUC cover-endpoints ≡ pos 1
winding-one-turn = integer-injective
  (windingLoop-lift coverUC cover-endpoints idᵘᶜ standard-step ∙ subZero (rat 1))

winding-identity : windingNumber idᵘᶜ ≡ pos 1
winding-identity = integer-injective
  (windingNumber-lift idᵘᶜ idᵘᶜ standard-step ∙ subZero (rat 1))

private
  constantRealUC : UC[ ℝPremetricSpace , ℝPremetricSpace ]
  constantRealUC = NE→UC ((λ _ → 0ℝ) , record { pres≈ = λ _ _ ε _ → refl∼ 0ℝ ε })

constantCircleMap : Circle → UC[ CirclePremetricSpace , CirclePremetricSpace ]
constantCircleMap c = NE→UC ((λ _ → c) , record
  { pres≈ = λ _ _ ε _ → PremetricStr.isRefl≈ (snd CirclePremetricSpace) c ε })

winding-constant : ∀ c → windingNumber (constantCircleMap c) ≡ pos 0
winding-constant c = integer-injective
  (windingNumber-lift (constantCircleMap c) constantRealUC
    (λ _ _ → cong (c +ᶜ_) (cong cover (subSelf 0ℝ)) ∙ circle-add-zero c)
    ∙ subSelf 0ℝ)

integerLift : ℤ → UC[ ℝPremetricSpace , ℝPremetricSpace ]
integerLift k = ([ k / 1 ] ⋆_) , scalar-isUniformlyContinuous [ k / 1 ]

integerLoop : ℤ → UC[ ℝPremetricSpace , CirclePremetricSpace ]
integerLoop k = coverUC ∘UC integerLift k

private
  lift-zero : ∀ k → fst (integerLift k) 0ℝ ≡ 0ℝ
  lift-zero k = scalar-rat [ k / 1 ] 0 ∙ cong rat (R.0RightAnnihilates [ k / 1 ])

  lift-one : ∀ k → fst (integerLift k) (rat 1) ≡ integer k
  lift-one k = scalar-rat [ k / 1 ] 1 ∙ cong rat (ℚ.·IdR [ k / 1 ])

integerLoop-closed : ∀ k → fst (integerLoop k) (rat 0) ≡ fst (integerLoop k) (rat 1)
integerLoop-closed k = cong cover (lift-zero k)
  ∙ sym (cover-integer k) ∙ cong cover (sym (lift-one k))

-- Includes arbitrarily many positive and negative traversals, as well as zero.
winding-integer-loop : ∀ k → windingLoop (integerLoop k) (integerLoop-closed k) ≡ k
winding-integer-loop k = integer-injective
  (windingLoop-lift (integerLoop k) (integerLoop-closed k) (integerLift k)
    (λ x y → standard-step (fst (integerLift k) x) (fst (integerLift k) y))
    ∙ cong₂ _-_ (lift-one k) (lift-zero k) ∙ subZero (integer k))
