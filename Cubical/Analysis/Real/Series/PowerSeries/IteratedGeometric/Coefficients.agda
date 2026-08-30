module Cubical.Analysis.Real.Series.PowerSeries.IteratedGeometric.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_)
  renaming
    ( _choose_ to _chooseℕ_
    ; _+_ to _+ℕ_
    ; _·_ to _·ℕ_
    )
import Cubical.Data.Nat.Order as ℕOrder

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant


-- Natural-valued finite sums are kept separate from real-valued series sums.
-- They expose the discrete simplex recurrence without involving completion
-- normalization.
naturalPartialSum : (ℕ → ℕ) → ℕ → ℕ
naturalPartialSum terms zero = zero
naturalPartialSum terms (suc n) =
  naturalPartialSum terms n ℕ.+ terms n


naturalPartialSum-pointwise : ∀ a b →
  (∀ n → a n ≡ b n) →
  ∀ n → naturalPartialSum a n ≡ naturalPartialSum b n
naturalPartialSum-pointwise a b pointwise zero = refl
naturalPartialSum-pointwise a b pointwise (suc n) =
  cong₂ ℕ._+_
    (naturalPartialSum-pointwise a b pointwise n)
    (pointwise n)


naturalPartialSum-bound : ∀ terms bound n →
  (∀ k → k ℕOrder.< n → terms k ℕOrder.≤ bound) →
  naturalPartialSum terms n ℕOrder.≤ n ℕ.· bound
naturalPartialSum-bound terms bound zero before =
  ℕOrder.≤-refl
naturalPartialSum-bound terms bound (suc n) before =
  subst
    (naturalPartialSum terms (suc n) ℕOrder.≤_)
    (ℕ.+-comm (n ℕ.· bound) bound)
    (ℕOrder.≤-+-≤
      (naturalPartialSum-bound terms bound n
        (λ k k<n → before k
          (ℕOrder.<-trans k<n ℕOrder.<-suc)))
      (before n ℕOrder.<-suc))


naturalPower-mono : ∀ {m n} →
  m ℕOrder.≤ n →
  ∀ exponent → ℕ._^_ m exponent ℕOrder.≤ ℕ._^_ n exponent
naturalPower-mono m≤n zero = ℕOrder.≤-refl
naturalPower-mono m≤n (suc exponent) =
  ℕOrder.≤monotone· m≤n (naturalPower-mono m≤n exponent)


-- Iterated prefix sums of the constant-one sequence: order zero is one,
-- and each successor order takes one more discrete antiderivative.
simplexCoefficient : ℕ → ℕ → ℕ
simplexCoefficient zero n = suc zero
simplexCoefficient (suc order) n =
  naturalPartialSum (simplexCoefficient order) (suc n)


simplexCoefficient-zeroIndex : ∀ order →
  simplexCoefficient order zero ≡ suc zero
simplexCoefficient-zeroIndex zero = refl
simplexCoefficient-zeroIndex (suc order) =
  simplexCoefficient-zeroIndex order


simplexCoefficient-sucIndex : ∀ order n →
  simplexCoefficient (suc order) (suc n)
    ≡
  simplexCoefficient (suc order) n
    ℕ.+ simplexCoefficient order (suc n)
simplexCoefficient-sucIndex order n = refl


simplexCoefficient-oneOrder : ∀ n →
  simplexCoefficient (suc zero) n ≡ suc n
simplexCoefficient-oneOrder zero = refl
simplexCoefficient-oneOrder (suc n) =
  simplexCoefficient-sucIndex zero n
  ∙ cong (λ value → value ℕ.+ suc zero)
      (simplexCoefficient-oneOrder n)
  ∙ ℕ.+-suc (suc n) zero
  ∙ cong suc (ℕ.+-zero (suc n))


simplexCoefficient-oneIndex : ∀ order →
  simplexCoefficient order (suc zero) ≡ suc order
simplexCoefficient-oneIndex zero = refl
simplexCoefficient-oneIndex (suc order) =
  simplexCoefficient-sucIndex order zero
  ∙ cong₂ ℕ._+_
      (simplexCoefficient-zeroIndex (suc order))
      (simplexCoefficient-oneIndex order)


private
  derivative-first-rearrange : ∀ n A B →
    suc (suc n) ·ℕ (A +ℕ B)
      ≡
    (suc n ·ℕ A +ℕ A)
      +ℕ suc (suc n) ·ℕ B
  derivative-first-rearrange n A B =
    sym (ℕ.·-distribˡ (suc (suc n)) A B)
    ∙ cong (λ value → value ℕ.+ suc (suc n) ℕ.· B)
        (ℕ.+-comm A (suc n ℕ.· A))

  derivative-second-rearrange : ∀ order A C →
    (suc (suc order) ·ℕ C +ℕ A)
      +ℕ suc order ·ℕ A
      ≡
    suc (suc order) ·ℕ (C +ℕ A)
  derivative-second-rearrange order A C =
    sym
      (ℕ.+-assoc
        (suc (suc order) ℕ.· C)
        A
        (suc order ℕ.· A))
    ∙ ℕ.·-distribˡ (suc (suc order)) C A


simplexCoefficient-derivative-scale : ∀ order n →
  suc n ℕ.· simplexCoefficient order (suc n)
    ≡
  suc order ℕ.· simplexCoefficient (suc order) n
simplexCoefficient-derivative-scale zero n =
  ℕ.·-identityʳ (suc n)
  ∙ sym (simplexCoefficient-oneOrder n)
  ∙ sym
      (ℕ.·-identityˡ
        (simplexCoefficient (suc zero) n))
simplexCoefficient-derivative-scale (suc order) zero =
  ℕ.·-identityˡ
    (simplexCoefficient (suc order) (suc zero))
  ∙ simplexCoefficient-oneIndex (suc order)
  ∙ sym (ℕ.·-identityʳ (suc (suc order)))
  ∙ cong (λ value → suc (suc order) ℕ.· value)
      (sym (simplexCoefficient-zeroIndex (suc (suc order))))
simplexCoefficient-derivative-scale (suc order) (suc n) =
  cong (λ value → suc (suc n) ℕ.· value)
    (simplexCoefficient-sucIndex order (suc n))
  ∙ derivative-first-rearrange n A B
  ∙ cong₂ ℕ._+_
      (cong (λ value → value ℕ.+ A)
        (simplexCoefficient-derivative-scale (suc order) n))
      (simplexCoefficient-derivative-scale order (suc n))
  ∙ derivative-second-rearrange order A C
  ∙ cong (λ value → suc (suc order) ℕ.· value)
      (sym (simplexCoefficient-sucIndex (suc order) n))
  where
  A : ℕ
  A = simplexCoefficient (suc order) (suc n)

  B : ℕ
  B = simplexCoefficient order (suc (suc n))

  C : ℕ
  C = simplexCoefficient (suc (suc order)) n


realNatural-naturalPartialSum : ∀ terms n →
  partialSum (realNatural ∘ terms) n
    ≡ realNatural (naturalPartialSum terms n)
realNatural-naturalPartialSum terms zero = refl
realNatural-naturalPartialSum terms (suc n) =
  cong (_+ realNatural (terms n))
    (realNatural-naturalPartialSum terms n)
  ∙ sym
      (realNatural-add
        (naturalPartialSum terms n) (terms n))


-- The structural definition: multiply by one more geometric coefficient
-- sequence at every successor order.
iteratedGeometricCoefficients : ℕ → RealSequence
iteratedGeometricCoefficients zero = geometricCoefficients
iteratedGeometricCoefficients (suc order) =
  cauchyProduct geometricCoefficients
    (iteratedGeometricCoefficients order)


iteratedGeometricCoefficients-base :
  iteratedGeometricCoefficients zero ≡ geometricCoefficients
iteratedGeometricCoefficients-base = refl


iteratedGeometricCoefficients-successor : ∀ order →
  iteratedGeometricCoefficients (suc order)
    ≡
  cauchyProduct geometricCoefficients
    (iteratedGeometricCoefficients order)
iteratedGeometricCoefficients-successor order = refl


cauchyProduct-geometricCoefficients-left : ∀ coefficients n →
  cauchyProduct geometricCoefficients coefficients n
    ≡ partialSum coefficients (suc n)
cauchyProduct-geometricCoefficients-left coefficients n =
  cauchyProduct-comm geometricCoefficients coefficients n
  ∙ partialSum-pointwise
      (λ k → coefficients k · geometricCoefficients (n ∸ k))
      coefficients
      (λ k → mulIdR (coefficients k))
      (suc n)


iteratedGeometricCoefficients-simplex : ∀ order n →
  iteratedGeometricCoefficients order n
    ≡ realNatural (simplexCoefficient order n)
iteratedGeometricCoefficients-simplex zero n =
  sym realNatural-one
iteratedGeometricCoefficients-simplex (suc order) n =
  cauchyProduct-geometricCoefficients-left
    (iteratedGeometricCoefficients order) n
  ∙ partialSum-pointwise
      (iteratedGeometricCoefficients order)
      (realNatural ∘ simplexCoefficient order)
      (iteratedGeometricCoefficients-simplex order)
      (suc n)
  ∙ realNatural-naturalPartialSum
      (simplexCoefficient order) (suc n)


iteratedGeometricCoefficients-zeroIndex : ∀ order →
  iteratedGeometricCoefficients order zero ≡ 1ℝ
iteratedGeometricCoefficients-zeroIndex order =
  iteratedGeometricCoefficients-simplex order zero
  ∙ cong realNatural (simplexCoefficient-zeroIndex order)
  ∙ realNatural-one


iteratedGeometricCoefficients-oneOrder-pointwise : ∀ n →
  iteratedGeometricCoefficients (suc zero) n
    ≡ realNatural (suc n)
iteratedGeometricCoefficients-oneOrder-pointwise n =
  iteratedGeometricCoefficients-simplex (suc zero) n
  ∙ cong realNatural (simplexCoefficient-oneOrder n)


iteratedGeometricCoefficients-oneOrder :
  iteratedGeometricCoefficients (suc zero)
    ≡ (λ n → realNatural (suc n))
iteratedGeometricCoefficients-oneOrder =
  funExt iteratedGeometricCoefficients-oneOrder-pointwise


formalDerivative-geometricCoefficients-pointwise : ∀ n →
  formalDerivative geometricCoefficients n
    ≡ iteratedGeometricCoefficients (suc zero) n
formalDerivative-geometricCoefficients-pointwise n =
  mulIdR (realNatural (suc n))
  ∙ sym (iteratedGeometricCoefficients-oneOrder-pointwise n)


formalDerivative-geometricCoefficients :
  formalDerivative geometricCoefficients
    ≡ iteratedGeometricCoefficients (suc zero)
formalDerivative-geometricCoefficients =
  funExt formalDerivative-geometricCoefficients-pointwise


formalDerivative-iteratedGeometric-pointwise : ∀ order n →
  formalDerivative (iteratedGeometricCoefficients order) n
    ≡
  realNatural (suc order)
    · iteratedGeometricCoefficients (suc order) n
formalDerivative-iteratedGeometric-pointwise order n =
  cong (realNatural (suc n) ·_)
    (iteratedGeometricCoefficients-simplex order (suc n))
  ∙ sym
      (realNatural-mul
        (suc n) (simplexCoefficient order (suc n)))
  ∙ cong realNatural
      (simplexCoefficient-derivative-scale order n)
  ∙ realNatural-mul
      (suc order) (simplexCoefficient (suc order) n)
  ∙ cong (realNatural (suc order) ·_)
      (sym
        (iteratedGeometricCoefficients-simplex
          (suc order) n))


formalDerivative-iteratedGeometric : ∀ order →
  formalDerivative (iteratedGeometricCoefficients order)
    ≡
  scaleSeries (realNatural (suc order))
    (iteratedGeometricCoefficients (suc order))
formalDerivative-iteratedGeometric order =
  funExt (formalDerivative-iteratedGeometric-pointwise order)


iteratedGeometricCoefficients-sucIndex : ∀ order n →
  iteratedGeometricCoefficients (suc order) (suc n)
    ≡
  iteratedGeometricCoefficients (suc order) n
    + iteratedGeometricCoefficients order (suc n)
iteratedGeometricCoefficients-sucIndex order n =
  iteratedGeometricCoefficients-simplex (suc order) (suc n)
  ∙ cong realNatural (simplexCoefficient-sucIndex order n)
  ∙ realNatural-add
      (simplexCoefficient (suc order) n)
      (simplexCoefficient order (suc n))
  ∙ cong₂ _+_
      (sym (iteratedGeometricCoefficients-simplex
        (suc order) n))
      (sym (iteratedGeometricCoefficients-simplex
        order (suc n)))


choose-above-offset : ∀ n offset →
  _chooseℕ_ n (suc (offset ℕ.+ n)) ≡ zero
choose-above-offset zero offset = refl
choose-above-offset (suc n) offset =
  cong (λ k → _chooseℕ_ (suc n) (suc k))
    (ℕ.+-suc offset n)
  ∙ cong₂ ℕ._+_
      (choose-above-offset n (suc offset))
      (choose-above-offset n offset)


choose-diagonal : ∀ n →
  _chooseℕ_ n n ≡ suc zero
choose-diagonal zero = refl
choose-diagonal (suc n) =
  cong₂ ℕ._+_
    (choose-above-offset n zero)
    (choose-diagonal n)


naturalPartialSum-binomial : ∀ order n →
  naturalPartialSum
      (λ k → _chooseℕ_ (k ℕ.+ order) order)
      (suc n)
    ≡
  _chooseℕ_ (n ℕ.+ suc order) (suc order)
naturalPartialSum-binomial order zero =
  choose-diagonal order
  ∙ sym (choose-diagonal (suc order))
naturalPartialSum-binomial order (suc n) =
  cong₂ ℕ._+_
    (naturalPartialSum-binomial order n)
    (cong (λ k → _chooseℕ_ k order)
      (sym (ℕ.+-suc n order)))


simplexCoefficient-binomial : ∀ order n →
  simplexCoefficient order n
    ≡ _chooseℕ_ (n ℕ.+ order) order
simplexCoefficient-binomial zero n = refl
simplexCoefficient-binomial (suc order) n =
  naturalPartialSum-pointwise
    (simplexCoefficient order)
    (λ k → _chooseℕ_ (k ℕ.+ order) order)
    (simplexCoefficient-binomial order)
    (suc n)
  ∙ naturalPartialSum-binomial order n


iteratedGeometricCoefficients-binomial : ∀ order n →
  iteratedGeometricCoefficients order n
    ≡
  realNatural (_chooseℕ_ (n ℕ.+ order) order)
iteratedGeometricCoefficients-binomial order n =
  iteratedGeometricCoefficients-simplex order n
  ∙ cong realNatural (simplexCoefficient-binomial order n)


simplexCoefficient-growth : ∀ order n →
  simplexCoefficient order n
    ℕOrder.≤ ℕ._^_ (suc n) order
simplexCoefficient-growth zero n = ℕOrder.≤-refl
simplexCoefficient-growth (suc order) n =
  naturalPartialSum-bound
    (simplexCoefficient order)
    (ℕ._^_ (suc n) order)
    (suc n)
    (λ k k<sucn →
      ℕOrder.≤-trans
        (simplexCoefficient-growth order k)
        (naturalPower-mono k<sucn order))


iteratedGeometricCoefficients-nonnegative : ∀ order →
  NonnegativeCoefficients
    (iteratedGeometricCoefficients order)
iteratedGeometricCoefficients-nonnegative order n =
  subst
    (0ℝ ≤ℝ_)
    (sym (iteratedGeometricCoefficients-simplex order n))
    (realNatural-nonnegative (simplexCoefficient order n))


iteratedGeometricCoefficients-growth : ∀ order n →
  iteratedGeometricCoefficients order n
    ≤ℝ
  realNatural (ℕ._^_ (suc n) order)
iteratedGeometricCoefficients-growth order n =
  subst
    (_≤ℝ realNatural (ℕ._^_ (suc n) order))
    (sym (iteratedGeometricCoefficients-simplex order n))
    (realNatural-mono (simplexCoefficient-growth order n))


iteratedGeometricCoefficients-polynomialMajorant : ∀ order →
  CoefficientMajorizedBy
    (iteratedGeometricCoefficients order)
    (λ n → realNatural (ℕ._^_ (suc n) order))
iteratedGeometricCoefficients-polynomialMajorant order n =
  subst
    (_≤ℝ realNatural (ℕ._^_ (suc n) order))
    (sym
      (absOfNonnegative
        (iteratedGeometricCoefficients order n)
        (iteratedGeometricCoefficients-nonnegative order n)))
    (iteratedGeometricCoefficients-growth order n)
