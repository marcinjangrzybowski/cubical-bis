module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Addition.Cauchy where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
  renaming (_≤_ to _≤ℕ_)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Base

open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Operations
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


addCauchy : (a b : ComplexSequence) →
  IsCauchySequenceℂ a → IsCauchySequenceℂ b →
  IsCauchySequenceℂ (λ n → a n +ℂ b n)
addCauchy a b (N , a-cauchy) (M , b-cauchy) =
  (λ ε → ℕ.max (N (ε /2₊)) (M (ε /2₊))) ,
  λ ε i j max≤i max≤j →
    PremetricStr.subst≈ (snd ℂPremetricSpace)
      (a i +ℂ b i) (a j +ℂ b j)
      {ε = (ε /2₊) +₊ (ε /2₊)} {ε' = ε}
      (1/2∈ℚ./2+/2≡id (fst ε))
      (addℂ-pres≈
        (a i) (a j) (b i) (b j)
        (ε /2₊) (ε /2₊)
        (a-cauchy (ε /2₊) i j
          (ℕ.≤-trans
            (ℕ.left-≤-max {N (ε /2₊)} {M (ε /2₊)})
            max≤i)
          (ℕ.≤-trans
            (ℕ.left-≤-max {N (ε /2₊)} {M (ε /2₊)})
            max≤j))
        (b-cauchy (ε /2₊) i j
          (ℕ.≤-trans
            (ℕ.right-≤-max {M (ε /2₊)} {N (ε /2₊)})
            max≤i)
          (ℕ.≤-trans
            (ℕ.right-≤-max {M (ε /2₊)} {N (ε /2₊)})
            max≤j)))
