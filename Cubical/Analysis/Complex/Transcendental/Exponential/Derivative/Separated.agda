module Cubical.Analysis.Complex.Transcendental.Exponential.Derivative.Separated where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.SmallError
open import Cubical.Analysis.Complex.Calculus.Derivative.Coordinates
import Cubical.Analysis.Complex.Transcendental.Exponential.Derivative.Algebra as Algebra

private module A = Algebra.SeparatedAlgebra ℝCommRing

-- Keep the analytic argument independent of the construction of the real
-- functions. In particular, it never unfolds their power-series limits.
opaque
  separatedExponential : (e c s : ℝ → ℝ) → ℂ → ℂ
  separatedExponential e c s z = fromℝ (e (re z)) ·ℂ (c (im z) , s (im z))

  separatedExponential-value : ∀ e c s z →
    separatedExponential e c s z ≡ fromℝ (e (re z)) ·ℂ (c (im z) , s (im z))
  separatedExponential-value e c s z = refl

-- The three real remainders are little-o of the complex displacement.
-- The remaining cross term is small by continuity of the angular factor.
-- Only finitely many locally truncated radii are combined at each point.
opaque
  unfolding separatedExponential
  separatedExponentialHasSelfDerivative : ∀ e c s →
    IsDerivative e e → IsDerivative c (λ t → - s t) → IsDerivative s c →
    IsComplexDerivative (separatedExponential e c s) (separatedExponential e c s)
  separatedExponentialHasSelfDerivative e c s ed cd sd z =
    smallComplexErrorCong source z h
      (λ w → (G w ·ℂ er w +ℂ H ·ℂ angularError w) +ℂ H ·ℂ cross w)
      (complexDerivativeErrorAlong (idfun ℂ) (separatedExponential e c s)
        (separatedExponential e c s z) z)
      (λ w → sym (A.remainder (e (re z)) (e (re w)) (c (im z)) (c (im w))
        (s (im z)) (s (im w)) (re z) (re w) (im z) (im w)))
      (smallComplexErrorAdd source z h
        (λ w → G w ·ℂ er w +ℂ H ·ℂ angularError w) (λ w → H ·ℂ cross w)
        (smallComplexErrorAdd source z h (λ w → G w ·ℂ er w) (λ w → H ·ℂ angularError w)
          (smallComplexErrorMulContinuous source z h G er (continuous z)
            (realDerivativeRealCoordinateErrorSmallAt e (e (re z)) z (ed (re z))))
          (smallComplexErrorMulConstant source z h H angularError
            (smallComplexErrorAdd source z h cr (λ w → iℂ ·ℂ sr w)
              (realDerivativeImaginaryCoordinateErrorSmallAt c (- s (im z)) z (cd (im z)))
              (smallComplexErrorMulConstant source z h iℂ sr
                (realDerivativeImaginaryCoordinateErrorSmallAt s (c (im z)) z (sd (im z)))))))
        (smallComplexErrorMulConstant source z h H cross
          (smallComplexErrorLargerDisplacement z dx h cross (realDisplacementNormBound z)
            (smallComplexErrorContinuousFactor source z dx G (continuous z)))))
    where
    source : PremetricStr ℓ-zero ℂ
    source = ℂPremetricSpace .snd
    h dx G er cr sr angularError cross : ℂ → ℂ
    h w = w -ℂ z
    dx w = fromℝ (re w - re z)
    G w = c (im w) , s (im w)
    er = realCoordinateRemainder re e (e (re z)) z
    cr = realCoordinateRemainder im c (- s (im z)) z
    sr = realCoordinateRemainder im s (c (im z)) z
    angularError w = cr w +ℂ iℂ ·ℂ sr w
    cross w = (G w -ℂ G z) ·ℂ dx w
    H : ℂ
    H = fromℝ (e (re z))
    continuous : isContinuous source G source
    continuous = pairℂ-isContinuous source (λ w → c (im w)) (λ w → s (im w))
      (snd ((c , derivativeIsContinuous c (λ t → - s t) cd) ∘C (im , imℂ-isContinuous)))
      (snd ((s , derivativeIsContinuous s c sd) ∘C (im , imℂ-isContinuous)))
