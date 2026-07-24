module Cubical.HITs.CauchyReals.Complex.Domain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Unit.Properties using (isPropUnit)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Subspace
  using (PremetricSubspace)

open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Base


ComplexPredicate : Type₁
ComplexPredicate = ℙ ℂ


wholeℂ : ComplexPredicate
wholeℂ _ = Unit , isPropUnit


ComplexSubspace : ComplexPredicate → PremetricSpace ℓ-zero ℓ-zero
ComplexSubspace = PremetricSubspace ℂPremetricSpace


ComplexOpenBall : ℂ → ℚ₊ → ComplexPredicate
ComplexOpenBall center ε z =
  (center ≈ℂ[ ε ] z) , isProp<ᵣ _ _


complexOpenBallCenter : ∀ center ε →
  center ∈ ComplexOpenBall center ε
complexOpenBallCenter center ε =
  IsPremetric.isRefl≈ isPremetricℂ center ε


HasComplexOpenBallAt : ComplexPredicate → ℂ → Type₀
HasComplexOpenBallAt P z =
  ∃[ ε ∈ ℚ₊ ] ComplexOpenBall z ε ⊆ P


isPropHasComplexOpenBallAt : ∀ P z →
  isProp (HasComplexOpenBallAt P z)
isPropHasComplexOpenBallAt P z = squash₁


IsComplexOpen : ComplexPredicate → Type₀
IsComplexOpen P =
  (z : ℂ) → z ∈ P → HasComplexOpenBallAt P z


isPropIsComplexOpen : ∀ P → isProp (IsComplexOpen P)
isPropIsComplexOpen P =
  isPropΠ2 λ z _ → isPropHasComplexOpenBallAt P z


ComplexOpenDomain : Type₁
ComplexOpenDomain =
  Σ[ P ∈ ComplexPredicate ] IsComplexOpen P


wholeℂIsOpen : IsComplexOpen wholeℂ
wholeℂIsOpen z _ =
  ∣ 1 , (λ _ _ → tt) ∣₁


complexOpenBallGapSum :
  ∀ ε δ (δ<ε : δ <₊ ε) →
  δ +₊ [ ε -₊ δ ]⟨ δ<ε ⟩ ≡ ε
complexOpenBallGapSum ε δ δ<ε =
  ℚ₊≡
    (ℚ.+Comm ⟨ δ ⟩₊ (ε -₊ δ)
    ∙ minusPlus₊ ε δ)


complexOpenBallNeighborhood :
  ∀ center ε z δ (δ<ε : δ <₊ ε) →
  center ≈ℂ[ δ ] z →
  ComplexOpenBall z [ ε -₊ δ ]⟨ δ<ε ⟩ ⊆
  ComplexOpenBall center ε
complexOpenBallNeighborhood center ε z δ δ<ε center≈δz w z≈w =
  subst
    (λ radius → center ≈ℂ[ radius ] w)
    (complexOpenBallGapSum ε δ δ<ε)
    (complexCloseTriangle
      center z w δ [ ε -₊ δ ]⟨ δ<ε ⟩ center≈δz z≈w)


complexOpenBallIsOpen : ∀ center ε →
  IsComplexOpen (ComplexOpenBall center ε)
complexOpenBallIsOpen center ε z center≈z =
  PT.map
    (λ (δ , δ<ε , center≈δz) →
      [ ε -₊ δ ]⟨ δ<ε ⟩ ,
      complexOpenBallNeighborhood center ε z δ δ<ε center≈δz)
    (complexCloseRounded center z ε center≈z)
