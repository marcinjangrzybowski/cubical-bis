module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Lift.MapsCauchySequences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.PropositionalTruncation.Properties as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition

-- module S = SequentialDefinition ℚPremetricSpace
-- module SP = SequentialPropertiesDefinition ℚPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous

-- The deliberately weak hypothesis investigated in this module.  Both its
-- premise and conclusion retain only mere Cauchy witnesses.

MapsRationalCauchySequencesToReals : (ℚ → S.ℭ̂ₛ) → Type₀
MapsRationalCauchySequencesToReals f =
  ∀ q → S.SeqWitness (S.ι ∘ q) → S.SeqWitness (f ∘ q)

isPropMapsRationalCauchySequencesToReals : ∀ f →
  isProp (MapsRationalCauchySequencesToReals f)
isPropMapsRationalCauchySequencesToReals f =
  isPropΠ2 λ _ _ → squash₁




liftMapsRationalCauchySequences :
  (f : ℚ → S.ℭ̂ₛ) →
  MapsRationalCauchySequencesToReals f →
  S.ℭ̂ₛ → S.ℭ̂ₛ
liftMapsRationalCauchySequences f maps x = (S.Elimℭ̂ₛ.go w x)

 where

 R : ∀ {x y : S.ℭ̂ₛ} →
     -- Σ
     S.ℭ̂ₛ -- (JointlyApproximableFor f x)
   → -- Σ
     S.ℭ̂ₛ -- (JointlyApproximableFor f y)
   → (ε : ℚ₊) →
          x SP.S.∼̂ₛ[ ε ] y
          → Type ℓ-zero
 R x y ε _ = x SP.S.∼̂ₛ[ ε ] y

 w : S.Elimℭ̂ₛ (λ _ → S.ℭ̂ₛ) R
 w .SequentialDefinition.Elimℭ̂ₛ.ιA = f
 w .SequentialDefinition.Elimℭ̂ₛ.limA x gx a∘x =
   S.lim a∘x ∘ PT.map (map-snd λ xx → λ ε m n <m <n → snd (xx ε m n <m <n) )
 -- Rec→Set.go ww
 --  where
 --  ff : Σ[ μ ∈ (ℚ₊ → ℕ) ]
 --        (
 --           (ε : ℚ₊) (m n : ℕ) →
 --           μ ε ℕ.≤ m →
 --           μ ε ℕ.≤ n →
 --           (Σ[ rr ∈  (x m S.∼̂ₛ[ ε ] x n) ] (R (a∘x m) (a∘x n) ε rr))) →
 --        S.ℭ̂ₛ
 --  ff (μ , xs) = S.lim a∘x ∣ {!!} ∣₁
 --  ww : Rec→Set S.ℭ̂ₛ
 --  ww .Rec→Set.isSetB = S.isSetℭ̂ₛ
 --  ww .Rec→Set.f = ff
 --  ww .Rec→Set.fconst = {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.eqA {x} {y} p a a' u v =
   S.eqℭ _ _ {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.ι-ι-B a a' ε x≈y = {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.ι-lim-B = {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.lim-ι-B = {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.lim-lim-B = {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.tri-B = {!!}
 w .SequentialDefinition.Elimℭ̂ₛ.isPropB = {!!}
