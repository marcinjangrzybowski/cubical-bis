module Cubical.Analysis.Complex.Roots.Existence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.Arguments
open import Cubical.Analysis.Complex.Roots.FromPolar

ComplexRoot : ℕ → ℂ → Type₀
ComplexRoot n z = Σ[ w ∈ ℂ ] w ^ℂ suc n ≡ z

-- The root's degree is suc n. Apartness is expressed by positive modulus.
-- Local arguments are used only under propositional truncation.
nonzeroComplexRoot : ∀ n z → 0ℝ <ℝ modulusℂ z → ∥ ComplexRoot n z ∥₁
nonzeroComplexRoot n z positive = PT.map
  (λ (θ , reconstruct) → polarRootℂ n (modulusℂ z) positive θ ,
    polarRootℂ-power n (modulusℂ z) positive θ ∙ reconstruct)
  (nonzeroPolarWitness z positive)

UnitComplexRoot : ℕ → ℂ → Type₀
UnitComplexRoot n z = Σ[ w ∈ ℂ ] (w ^ℂ suc n ≡ z) × (modulusℂ w ≡ 1ℝ)

unitComplexRoot : ∀ n z → modulusℂ z ≡ 1ℝ → ∥ UnitComplexRoot n z ∥₁
unitComplexRoot n z unit = PT.map fromArgument
  (nonzeroPolarWitness z (subst (0ℝ <ℝ_) (sym unit) (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt))))
  where
  fromArgument : PolarWitness z → UnitComplexRoot n z
  fromArgument (θ , reconstruct) = unitRootℂ n θ ,
    (unitRootℂ-power n θ
      ∙ sym (·ℂComm 1ℂ (cisℝ θ) ∙ ·ℂIdR (cisℝ θ))
      ∙ cong (λ r → polarℂ r θ) (sym unit) ∙ reconstruct) , unitRootℂ-modulus n θ
