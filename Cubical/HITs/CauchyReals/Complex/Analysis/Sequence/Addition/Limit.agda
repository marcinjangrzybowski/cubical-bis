module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Addition.Limit where

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

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Operations
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


addConverges :
  (a b : ComplexSequence) → (l m : ℂ) →
  ConvergesToℂ a l → ConvergesToℂ b m →
  ConvergesToℂ (λ n → a n +ℂ b n) (l +ℂ m)
addConverges a b l m (N , a→l) (M , b→m) =
  (λ ε → ℕ.max (N (ε /2₊)) (M (ε /2₊))) ,
  λ ε n max≤n →
    PremetricStr.subst≈ (snd ℂPremetricSpace)
      (a n +ℂ b n) (l +ℂ m)
      {ε = (ε /2₊) +₊ (ε /2₊)} {ε' = ε}
      (1/2∈ℚ./2+/2≡id (fst ε))
      (addℂ-pres≈
        (a n) l (b n) m
        (ε /2₊) (ε /2₊)
        (a→l (ε /2₊) n
          (ℕ.≤-trans
            (ℕ.left-≤-max {N (ε /2₊)} {M (ε /2₊)})
            max≤n))
        (b→m (ε /2₊) n
          (ℕ.≤-trans
            (ℕ.right-≤-max {M (ε /2₊)} {N (ε /2₊)})
            max≤n)))
