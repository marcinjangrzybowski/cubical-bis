module Cubical.Analysis.Complex.FundamentalTheorem.Quadratic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using ([_/_]; eq/)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Addition using (rat+rat)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.SquareRoot.Approximate
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement
open import Cubical.Analysis.Complex.FundamentalTheorem.Factorization
open import Cubical.Analysis.Complex.Polynomial.Quadratic.Disk
open import Cubical.Analysis.Complex.Polynomial.Quadratic.Small
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
import Cubical.Analysis.Complex.Polynomial.Quadratic.Algebra as AlgebraDefinition

private
  module C = AlgebraDefinition.Quadratic ℂCommRing

  half : ℂ
  half = fromℝ (rat [ pos 1 / 1+ 1 ])

  twice-half : half +ℂ half ≡ 1ℂ
  twice-half = sym (fromℝ-pres+ (rat [ pos 1 / 1+ 1 ]) (rat [ pos 1 / 1+ 1 ]))
    ∙ cong fromℝ (rat+rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 1 ] ∙ cong rat (eq/ _ _ refl))

  quadraticCloseness : ∀ a b c ε → a ∼ℂ[ ε ] c →
    CoefficientCloseness (a ∷ b ∷ []) ε (c ∷ b ∷ [])
  quadraticCloseness a b c ε close zero = close
  quadraticCloseness a b c ε close (suc zero) = refl∼ℂ b ε

-- Every native monic quadratic is approximated by two linear factors.
-- The coefficient of X is exact; all error is confined to the constant.
approximateFactorization-quadratic : (a b : ℂ) (ε : ℚ₊) →
  ApproximateFactorization (a ∷ b ∷ []) ε
approximateFactorization-quadratic a b ε = PT.map factor
  (approximateSquareRoot discriminant ε)
  where
  midpoint discriminant : ℂ
  midpoint = half ·ℂ b
  discriminant = (midpoint ·ℂ midpoint) -ℂ a

  factor : (Σ[ w ∈ ℂ ] ((w ·ℂ w) ∼ℂ[ ε ] discriminant)) →
    Σ[ roots ∈ Vec ℂ 2 ] CoefficientCloseness (a ∷ b ∷ []) ε (linearFactors roots)
  factor (w , close) = roots ,
    subst (CoefficientCloseness (a ∷ b ∷ []) ε)
      (sym (C.quadraticFactors b half w twice-half))
      (quadraticCloseness a b constant ε
        (sym∼ℂ constant a ε
          (subst (constant ∼ℂ[ ε ]_) (C.subtractTwice (midpoint ·ℂ midpoint) a)
            (subtractℂ-presClosenessL (midpoint ·ℂ midpoint) (w ·ℂ w) discriminant ε close))))
    where
    roots : Vec ℂ 2
    roots = ((-ℂ midpoint) +ℂ w) ∷ ((-ℂ midpoint) -ℂ w) ∷ []
    constant : ℂ
    constant = (midpoint ·ℂ midpoint) -ℂ (w ·ℂ w)

approximateFundamentalTheorem-degreeTwo : (p : MonicPolynomial 2) (ε : ℚ₊) →
  ApproximateFactorization p ε
approximateFundamentalTheorem-degreeTwo (a ∷ b ∷ []) = approximateFactorization-quadratic a b

exactFactorization-smallQuadratic : (c : ℂ) → normℂ c ≤ℝ quadraticConstantBound →
  ExactFactorization (quadraticPolynomial c)
exactFactorization-smallQuadratic c small = exactFactorization-quadraticRoot
  (quadraticPolynomial c) (smallQuadraticRoot c small) (smallQuadraticRoot-equation c small)
