module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Tactics.NatSolver

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _∸_)
  renaming
    ( _choose_ to _chooseℕ_
    ; _+_ to _+ℕ_
    ; _·_ to _·ℕ_
    )
import Cubical.Data.Nat.Order as ℕOrder

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (nonnegative→abs-self)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LinearGrowth
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.IteratedGeometric


-- Natural-valued finite sums are kept separate from real-valued partial
-- sums.  This makes the coefficient combinatorics independent of analysis.

naturalPartialSum : (ℕ → ℕ) → ℕ → ℕ
naturalPartialSum terms zero =
  zero
naturalPartialSum terms (suc n) =
  naturalPartialSum terms n ℕ.+ terms n


naturalPartialSum-pointwise :
  ∀ a b →
  (∀ n → a n ≡ b n) →
  ∀ n →
  naturalPartialSum a n ≡ naturalPartialSum b n
naturalPartialSum-pointwise a b pointwise zero =
  refl
naturalPartialSum-pointwise a b pointwise (suc n) =
  cong₂ ℕ._+_
    (naturalPartialSum-pointwise a b pointwise n)
    (pointwise n)


naturalPartialSum-bound :
  ∀ terms bound n →
  (∀ k → k ℕOrder.< n →
    terms k ℕOrder.≤ bound) →
  naturalPartialSum terms n ℕOrder.≤ n ℕ.· bound
naturalPartialSum-bound terms bound zero before =
  ℕOrder.≤-refl
naturalPartialSum-bound terms bound (suc n) before =
  subst
    (naturalPartialSum terms (suc n) ℕOrder.≤_)
    (ℕ.+-comm (n ℕ.· bound) bound)
    (ℕOrder.≤-+-≤
      (naturalPartialSum-bound
        terms bound n
        (λ k k<n →
          before k (ℕOrder.<-trans k<n ℕOrder.<-suc)))
      (before n ℕOrder.<-suc))


naturalPower-mono : ∀ {m n} →
  m ℕOrder.≤ n →
  ∀ exponent →
  ℕ._^_ m exponent ℕOrder.≤ ℕ._^_ n exponent
naturalPower-mono m≤n zero =
  ℕOrder.≤-refl
naturalPower-mono m≤n (suc exponent) =
  ℕOrder.≤monotone·
    m≤n (naturalPower-mono m≤n exponent)


-- At fixed order these are simplex numbers.  The recursive presentation is
-- the one seen directly by repeated convolution; a binomial closed form is
-- derived below rather than built into the analytic construction.

simplexCoefficient : ℕ → ℕ → ℕ
simplexCoefficient zero n =
  suc zero
simplexCoefficient (suc order) n =
  naturalPartialSum (simplexCoefficient order) (suc n)


simplexCoefficient-zeroIndex : ∀ order →
  simplexCoefficient order zero ≡ suc zero
simplexCoefficient-zeroIndex zero =
  refl
simplexCoefficient-zeroIndex (suc order) =
  simplexCoefficient-zeroIndex order


simplexCoefficient-sucIndex : ∀ order n →
  simplexCoefficient (suc order) (suc n) ≡
  simplexCoefficient (suc order) n ℕ.+
    simplexCoefficient order (suc n)
simplexCoefficient-sucIndex order n =
  refl


simplexCoefficient-oneOrder : ∀ n →
  simplexCoefficient (suc zero) n ≡ suc n
simplexCoefficient-oneOrder zero =
  refl
simplexCoefficient-oneOrder (suc n) =
  simplexCoefficient-sucIndex zero n
  ∙ cong (ℕ._+ suc zero) (simplexCoefficient-oneOrder n)
  ∙ ℕ.+-suc (suc n) zero
  ∙ cong suc (ℕ.+-zero (suc n))


simplexCoefficient-oneIndex : ∀ order →
  simplexCoefficient order (suc zero) ≡ suc order
simplexCoefficient-oneIndex zero =
  refl
simplexCoefficient-oneIndex (suc order) =
  simplexCoefficient-sucIndex order zero
  ∙ cong₂ ℕ._+_
      (simplexCoefficient-zeroIndex (suc order))
      (simplexCoefficient-oneIndex order)


private
  derivative-first-rearrange : ∀ n A B →
    suc (suc n) ·ℕ (A +ℕ B) ≡
    (suc n ·ℕ A +ℕ A) +ℕ
      suc (suc n) ·ℕ B
  derivative-first-rearrange n A B =
    solveℕ!

  derivative-second-rearrange : ∀ order A C →
    (suc (suc order) ·ℕ C +ℕ A) +ℕ
      suc order ·ℕ A ≡
    suc (suc order) ·ℕ (C +ℕ A)
  derivative-second-rearrange order A C =
    solveℕ!


simplexCoefficient-derivative-scale : ∀ order n →
  suc n ℕ.· simplexCoefficient order (suc n) ≡
  suc order ℕ.· simplexCoefficient (suc order) n
simplexCoefficient-derivative-scale zero n =
  ℕ.·-identityʳ (suc n)
  ∙ sym (simplexCoefficient-oneOrder n)
  ∙ sym (ℕ.·-identityˡ (simplexCoefficient (suc zero) n))
simplexCoefficient-derivative-scale (suc order) zero =
  ℕ.·-identityˡ (simplexCoefficient (suc order) (suc zero))
  ∙ simplexCoefficient-oneIndex (suc order)
  ∙ sym (ℕ.·-identityʳ (suc (suc order)))
  ∙ cong
      (suc (suc order) ℕ.·_)
      (sym (simplexCoefficient-zeroIndex (suc (suc order))))
simplexCoefficient-derivative-scale (suc order) (suc n) =
  cong
      (suc (suc n) ℕ.·_)
      (simplexCoefficient-sucIndex order (suc n))
  ∙ derivative-first-rearrange n A B
  ∙ cong₂ ℕ._+_
      (cong (ℕ._+ A)
        (simplexCoefficient-derivative-scale (suc order) n))
      (simplexCoefficient-derivative-scale order (suc n))
  ∙ derivative-second-rearrange order A C
  ∙ cong
      (suc (suc order) ℕ.·_)
      (sym (simplexCoefficient-sucIndex (suc order) n))
  where
  A : ℕ
  A = simplexCoefficient (suc order) (suc n)

  B : ℕ
  B = simplexCoefficient order (suc (suc n))

  C : ℕ
  C = simplexCoefficient (suc (suc order)) n


realNatural-naturalPartialSum : ∀ terms n →
  partialSum (realNatural ∘ terms) n ≡
  realNatural (naturalPartialSum terms n)
realNatural-naturalPartialSum terms zero =
  refl
realNatural-naturalPartialSum terms (suc n) =
  cong₂ Add._+_
    (realNatural-naturalPartialSum terms n) refl
  ∙ sym
      (realNatural-add
        (naturalPartialSum terms n) (terms n))


iteratedGeometricCoefficients-simplex : ∀ order n →
  iteratedGeometricCoefficients order n ≡
  realNatural (simplexCoefficient order n)
iteratedGeometricCoefficients-simplex zero n =
  sym realNatural-one
iteratedGeometricCoefficients-simplex (suc order) n =
  cauchyProduct-unitCoefficients-left
    (iteratedGeometricCoefficients order) n
  ∙ partialSum-pointwise
      (iteratedGeometricCoefficients order)
      (realNatural ∘ simplexCoefficient order)
      (iteratedGeometricCoefficients-simplex order)
      (suc n)
  ∙ realNatural-naturalPartialSum
      (simplexCoefficient order) (suc n)


choose-above-offset : ∀ n offset →
  _chooseℕ_ n (suc (offset ℕ.+ n)) ≡ zero
choose-above-offset zero offset =
  refl
choose-above-offset (suc n) offset =
  cong
      (_chooseℕ_ (suc n) ∘ suc)
      (ℕ.+-suc offset n)
  ∙ cong₂ ℕ._+_
      (choose-above-offset n (suc offset))
      (choose-above-offset n offset)


choose-diagonal : ∀ n →
  _chooseℕ_ n n ≡ suc zero
choose-diagonal zero =
  refl
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
    (cong
      (λ k → _chooseℕ_ k order)
      (sym (ℕ.+-suc n order)))


simplexCoefficient-binomial : ∀ order n →
  simplexCoefficient order n ≡
  _chooseℕ_ (n ℕ.+ order) order
simplexCoefficient-binomial zero n =
  refl
simplexCoefficient-binomial (suc order) n =
  naturalPartialSum-pointwise
    (simplexCoefficient order)
    (λ k → _chooseℕ_ (k ℕ.+ order) order)
    (simplexCoefficient-binomial order)
    (suc n)
  ∙ naturalPartialSum-binomial order n


simplexCoefficient-growth : ∀ order n →
  simplexCoefficient order n ℕOrder.≤
  ℕ._^_ (suc n) order
simplexCoefficient-growth zero n =
  ℕOrder.≤-refl
simplexCoefficient-growth (suc order) n =
  naturalPartialSum-bound
    (simplexCoefficient order)
    (ℕ._^_ (suc n) order)
    (suc n)
    (λ k k<sucn →
      ℕOrder.≤-trans
        (simplexCoefficient-growth order k)
        (naturalPower-mono k<sucn order))


iteratedGeometricCoefficients-binomial : ∀ order n →
  iteratedGeometricCoefficients order n ≡
  realNatural (_chooseℕ_ (n ℕ.+ order) order)
iteratedGeometricCoefficients-binomial order n =
  iteratedGeometricCoefficients-simplex order n
  ∙ cong realNatural (simplexCoefficient-binomial order n)


iteratedGeometricCoefficients-nonnegative : ∀ order →
  NonnegativeCoefficients (iteratedGeometricCoefficients order)
iteratedGeometricCoefficients-nonnegative order n =
  subst
    (λ value → zeroℝ ≤ℝ value)
    (sym (iteratedGeometricCoefficients-simplex order n))
    (realNatural-nonnegative (simplexCoefficient order n))


iteratedGeometricCoefficients-growth : ∀ order n →
  iteratedGeometricCoefficients order n ≤ℝ
  realNatural (ℕ._^_ (suc n) order)
iteratedGeometricCoefficients-growth order n =
  subst
    (λ value →
      value ≤ℝ realNatural (ℕ._^_ (suc n) order))
    (sym (iteratedGeometricCoefficients-simplex order n))
    (realNatural-mono (simplexCoefficient-growth order n))


iteratedGeometricCoefficients-polynomialMajorant : ∀ order →
  CoefficientMajorizedBy
    (iteratedGeometricCoefficients order)
    (λ n → realNatural (ℕ._^_ (suc n) order))
iteratedGeometricCoefficients-polynomialMajorant order n =
  subst
    (λ value →
      value ≤ℝ realNatural (ℕ._^_ (suc n) order))
    (sym
      (nonnegative→abs-self
        (iteratedGeometricCoefficients order n)
        (iteratedGeometricCoefficients-nonnegative order n)))
    (iteratedGeometricCoefficients-growth order n)


opaque
  iteratedGeometricCoefficients-nonnegative-sealed : ∀ order →
    NonnegativeCoefficients (iteratedGeometricCoefficients order)
  iteratedGeometricCoefficients-nonnegative-sealed =
    iteratedGeometricCoefficients-nonnegative
