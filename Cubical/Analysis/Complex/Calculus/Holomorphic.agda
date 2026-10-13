module Cubical.Analysis.Complex.Calculus.Holomorphic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Basic
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniqueness
open import Cubical.Analysis.Complex.Calculus.Derivative.Continuity
open import Cubical.Analysis.Complex.Calculus.Derivative.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.Product
open import Cubical.Analysis.Complex.Calculus.Derivative.Chain
open import Cubical.Analysis.Complex.Calculus.Derivative.Polynomial

-- Ambient differentiability at all selected points. For an open domain this
-- is the usual holomorphicity of a function defined on the ambient plane.
-- Intrinsic functions on open subspaces will use the Along interface.
IsHolomorphicOn : ∀ {ℓ} → (ℂ → Type ℓ) → (ℂ → ℂ) → Type ℓ
IsHolomorphicOn domain f = ∀ z → domain z → HasComplexDerivativeAt f z

IsEntire : (ℂ → ℂ) → Type₀
IsEntire f = ∀ z → HasComplexDerivativeAt f z

isPropIsHolomorphicOn : ∀ {ℓ} (domain : ℂ → Type ℓ) f → isProp (IsHolomorphicOn domain f)
isPropIsHolomorphicOn domain f = isPropΠ2 λ z _ → isPropHasComplexDerivativeAt f z

isPropIsEntire : ∀ f → isProp (IsEntire f)
isPropIsEntire f = isPropΠ (isPropHasComplexDerivativeAt f)

-- Pointwise witnesses already include their unique values. Projecting them
-- does not invoke choice or select any family of local radii.
entireDerivative : ∀ f → IsEntire f → ℂ → ℂ
entireDerivative f entire z = fst (entire z)

entireHasComplexDerivative : ∀ f (entire : IsEntire f) → IsComplexDerivative f (entireDerivative f entire)
entireHasComplexDerivative f entire z = snd (entire z)

complexDerivativeGivesEntire : ∀ f d → IsComplexDerivative f d → IsEntire f
complexDerivativeGivesEntire f d differentiable z = d z , differentiable z

entireIsContinuous : ∀ f → IsEntire f → isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd)
entireIsContinuous f entire = complexDerivativeIsContinuous f (entireDerivative f entire)
  (entireHasComplexDerivative f entire)

entireIsHolomorphicOn : ∀ {ℓ} (domain : ℂ → Type ℓ) f → IsEntire f → IsHolomorphicOn domain f
entireIsHolomorphicOn domain f entire z _ = entire z

restrictHolomorphic : ∀ {ℓ ℓ'} (domain : ℂ → Type ℓ) (subdomain : ℂ → Type ℓ') f →
  (∀ z → subdomain z → domain z) → IsHolomorphicOn domain f → IsHolomorphicOn subdomain f
restrictHolomorphic domain subdomain f include holomorphic z inside = holomorphic z (include z inside)

holomorphicOnIsContinuousAt : ∀ {ℓ} (domain : ℂ → Type ℓ) f → IsHolomorphicOn domain f →
  ∀ z → domain z → IsContinuousAt (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd) z
holomorphicOnIsContinuousAt domain f holomorphic z inside =
  complexDerivativeAtIsContinuous f (fst (holomorphic z inside)) z (snd (holomorphic z inside))

constantIsEntire : ∀ c → IsEntire (λ _ → c)
constantIsEntire c = complexDerivativeGivesEntire (λ _ → c) (λ _ → 0ℂ) (constantHasComplexDerivative c)

identityIsEntire : IsEntire (idfun ℂ)
identityIsEntire = complexDerivativeGivesEntire (idfun ℂ) (λ _ → 1ℂ) identityHasComplexDerivative

linearIsEntire : ∀ c → IsEntire (c ·ℂ_)
linearIsEntire c = complexDerivativeGivesEntire (c ·ℂ_) (λ _ → c) (linearHasComplexDerivative c)

polynomialIsEntire : ∀ p → IsEntire (evaluatePolynomialℂ p)
polynomialIsEntire p = complexDerivativeGivesEntire (evaluatePolynomialℂ p) (polynomialDerivativeℂ p)
  (polynomialHasComplexDerivative p)

addIsEntire : ∀ f g → IsEntire f → IsEntire g → IsEntire (λ z → f z +ℂ g z)
addIsEntire f g first second = complexDerivativeGivesEntire (λ z → f z +ℂ g z)
  (λ z → entireDerivative f first z +ℂ entireDerivative g second z)
  (addHasComplexDerivative f g (entireDerivative f first) (entireDerivative g second)
    (entireHasComplexDerivative f first) (entireHasComplexDerivative g second))

negIsEntire : ∀ f → IsEntire f → IsEntire (λ z → -ℂ f z)
negIsEntire f entire = complexDerivativeGivesEntire (λ z → -ℂ f z) (λ z → -ℂ entireDerivative f entire z)
  (negHasComplexDerivative f (entireDerivative f entire) (entireHasComplexDerivative f entire))

subIsEntire : ∀ f g → IsEntire f → IsEntire g → IsEntire (λ z → f z -ℂ g z)
subIsEntire f g first second = addIsEntire f (λ z → -ℂ g z) first (negIsEntire g second)

mulIsEntire : ∀ f g → IsEntire f → IsEntire g → IsEntire (λ z → f z ·ℂ g z)
mulIsEntire f g first second = complexDerivativeGivesEntire (λ z → f z ·ℂ g z)
  (λ z → entireDerivative f first z ·ℂ g z +ℂ f z ·ℂ entireDerivative g second z)
  (mulHasComplexDerivative f g (entireDerivative f first) (entireDerivative g second)
    (entireHasComplexDerivative f first) (entireHasComplexDerivative g second))

composeIsEntire : ∀ inner outer → IsEntire inner → IsEntire outer → IsEntire (outer ∘ inner)
composeIsEntire inner outer first second = complexDerivativeGivesEntire (outer ∘ inner)
  (λ z → entireDerivative outer second (inner z) ·ℂ entireDerivative inner first z)
  (chainHasComplexDerivative inner (entireDerivative inner first) outer (entireDerivative outer second)
    (entireHasComplexDerivative inner first) (entireHasComplexDerivative outer second))
