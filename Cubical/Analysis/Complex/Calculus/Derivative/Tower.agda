module Cubical.Analysis.Complex.Calculus.Derivative.Tower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat as Nat
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniqueness

-- An explicit coherent family, rather than separate truncated choices of
-- derivatives. D 0 is the original function and D (n+1) differentiates D n.
IsComplexDerivativeTowerAlong : ∀ {ℓ ℓ'} {A : Type ℓ} →
  PremetricStr ℓ' A → (A → ℂ) → (ℕ → A → ℂ) → Type (ℓ-max ℓ ℓ')
IsComplexDerivativeTowerAlong source coordinate derivatives =
  ∀ order → IsComplexDerivativeAlong source coordinate (derivatives order) (derivatives (suc order))

IsComplexDerivativeTower : (ℕ → ℂ → ℂ) → Type₀
IsComplexDerivativeTower = IsComplexDerivativeTowerAlong (ℂPremetricSpace .snd) (idfun ℂ)

isPropIsComplexDerivativeTowerAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coordinate derivatives →
  isProp (IsComplexDerivativeTowerAlong source coordinate derivatives)
isPropIsComplexDerivativeTowerAlong source coordinate derivatives = isPropΠ λ order →
  isPropIsComplexDerivativeAlong source coordinate (derivatives order) (derivatives (suc order))

shiftComplexDerivativeTowerAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coordinate derivatives →
  IsComplexDerivativeTowerAlong source coordinate derivatives → ∀ start →
  IsComplexDerivativeTowerAlong source coordinate (λ n → derivatives (n Nat.+ start))
shiftComplexDerivativeTowerAlong source coordinate derivatives tower start n = tower (n Nat.+ start)

-- Ambient complex derivatives are unique. No uniqueness is asserted on an
-- arbitrary parameter space, which may have isolated or constant coordinates.
opaque
  complexDerivativeTowerUnique : ∀ first second →
    IsComplexDerivativeTower first → IsComplexDerivativeTower second →
    first zero ≡ second zero → first ≡ second
  complexDerivativeTowerUnique first second firstTower secondTower base = funExt equal
    where
    equal : ∀ n → first n ≡ second n
    equal zero = base
    equal (suc n) = complexDerivativeFunctionUnique (first n) (first (suc n)) (second (suc n))
      (firstTower n) (subst (λ f → IsComplexDerivative f (second (suc n))) (sym (equal n)) (secondTower n))
