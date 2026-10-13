module Cubical.Analysis.Complex.FundamentalTheorem.Matching.NearRoot where

-- A sufficiently small finite product has a small factor. Locatedness
-- supplies overlapping alternatives with a half-radius margin. A finite
-- search gives a positively small factor without deciding exact vanishing
-- or extracting an existential witness from a negated universal statement.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Empty as ⊥
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Located using (dichotomyℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Metric
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
import Cubical.Analysis.Complex.Polynomial.Monic.DeflationAlgebra as DeflationDefinition
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.FiniteOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale

private module D = DeflationDefinition.Deflation ℂCommRing

smallProductThreshold : ℕ → ℚ₊ → ℚ₊
smallProductThreshold n ε = finitePositivePower n (ε /2₊)

private
  Near : ∀ {n} → Vec ℂ n → ℂ → ℚ₊ → Type₀
  Near {n} roots z ε = Σ[ i ∈ Fin n ] (modulusℂ (z -ℂ lookup i roots) <ℝ ⟦ ε ⟧₊)

  Far : ∀ {n} → Vec ℂ n → ℂ → ℚ₊ → Type₀
  Far {n} roots z ε = ∀ (i : Fin n) → ⟦ ε /2₊ ⟧₊ ≤ℝ modulusℂ (z -ℂ lookup i roots)

  search : ∀ {n} (roots : Vec ℂ n) z ε → PT.∥ Near roots z ε ⊎ Far roots z ε ∥₁
  search {n} roots z ε = finiteOrderAlternative n (λ i → modulusℂ (z -ℂ lookup i roots))
    ⟦ ε /2₊ ⟧₊ ⟦ ε ⟧₊ (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε))

  product-modulus : ∀ {n} (roots : Vec ℂ n) z →
    modulusℂ (productOfLinearFactors roots z) ≡ finiteRealProduct n (λ i → modulusℂ (z -ℂ lookup i roots))
  product-modulus [] z = modulusℂ-one
  product-modulus (r ∷ roots) z = cong modulusℂ (D.product-cons r roots z)
    ∙ modulusℂ-mul (z -ℂ r) (productOfLinearFactors roots z)
    ∙ cong (modulusℂ (z -ℂ r) ·_) (product-modulus roots z)

  product-lower : ∀ {n} (roots : Vec ℂ n) z ε → Far roots z ε →
    ⟦ smallProductThreshold n ε ⟧₊ ≤ℝ modulusℂ (productOfLinearFactors roots z)
  product-lower {n} roots z ε far = subst (⟦ smallProductThreshold n ε ⟧₊ ≤ℝ_)
    (sym (product-modulus roots z))
    (finiteProduct-lower n (λ i → modulusℂ (z -ℂ lookup i roots)) (ε /2₊) far)

opaque
  smallProduct-nearRoot : ∀ {n} (roots : Vec ℂ n) z ε →
    modulusℂ (evaluateMonic (linearFactors roots) z) <ℝ ⟦ smallProductThreshold n ε ⟧₊ →
    PT.∥ Σ[ i ∈ Fin n ] (z ∼ℂ[ ε ] lookup i roots) ∥₁
  smallProduct-nearRoot {n} roots z ε small = PT.rec PT.isPropPropTrunc cases (search roots z ε)
    where
    cases : Near roots z ε ⊎ Far roots z ε → PT.∥ Σ[ i ∈ Fin n ] (z ∼ℂ[ ε ] lookup i roots) ∥₁
    cases (inl (i , near)) = PT.∣ i , modulusℂ-difference<→closeness z (lookup i roots) ε near ∣₁
    cases (inr far) = ⊥.rec (≤ℝ→≯ ⟦ smallProductThreshold n ε ⟧₊
      (modulusℂ (evaluateMonic (linearFactors roots) z))
      (subst (λ v → ⟦ smallProductThreshold n ε ⟧₊ ≤ℝ modulusℂ v)
        (sym (evaluate-linearFactors roots z)) (product-lower roots z ε far)) small)
