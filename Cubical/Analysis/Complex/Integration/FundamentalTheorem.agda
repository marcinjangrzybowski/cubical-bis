module Cubical.Analysis.Complex.Integration.FundamentalTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Integration.FundamentalTheorem.Second as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Curve

-- Newton--Leibniz for a complex-valued function of one real parameter.
-- Each coordinate uses the existing real partition theorem, which constructs
-- the Riemann integral directly from the uniform derivative estimate.
complexFundamentalTheoremOfCalculus : ∀ F f a b →
  IsUniformComplexCurveDerivativeOn F f a b → HasComplexRiemannIntegralOn f a b (F b -ℂ F a)
complexFundamentalTheoremOfCalculus F f a b derivative =
  Real.fundamentalTheoremOfCalculusSecond (re ∘ F) (re ∘ f) a b (fst derivative) ,
  Real.fundamentalTheoremOfCalculusSecond (im ∘ F) (im ∘ f) a b (snd derivative)

uniformComplexCurveDerivativeIsIntegrable : ∀ F f a b →
  IsUniformComplexCurveDerivativeOn F f a b → IsComplexRiemannIntegrableOn f a b
uniformComplexCurveDerivativeIsIntegrable F f a b derivative =
  (F b -ℂ F a) , complexFundamentalTheoremOfCalculus F f a b derivative

complexIntegralOfUniformDerivative : ∀ F f a b → a ≤ℝ b →
  IsUniformComplexCurveDerivativeOn F f a b → (integrable : IsComplexRiemannIntegrableOn f a b) →
  complexIntegral {f = f} {a = a} {b = b} integrable ≡ F b -ℂ F a
complexIntegralOfUniformDerivative F f a b ordered derivative integrable =
  complexRiemannIntegralUnique f a b ordered (fst integrable) (F b -ℂ F a) (snd integrable)
    (complexFundamentalTheoremOfCalculus F f a b derivative)
