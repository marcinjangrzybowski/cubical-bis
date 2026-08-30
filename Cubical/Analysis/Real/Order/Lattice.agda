module Cubical.Analysis.Real.Order.Lattice where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Pseudolattice.Base
  using (Pseudolattice; makePseudolatticeFromPoset)

open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol)
open import Cubical.Analysis.Real.Algebra.Lattice using (maxℝ; minℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (negPres≤)


minGreatestLowerBound : ∀ x y z →
  z ≤ℝ x → z ≤ℝ y → z ≤ℝ minℝ x y
minGreatestLowerBound x y z z≤x z≤y =
  subst (λ u → u ≤ℝ minℝ x y) (negInvol z)
    (negPres≤
      (maxℝ (- x) (- y)) (- z)
      (maxLeastUpperBound (- x) (- y) (- z)
        (negPres≤ z x z≤x)
        (negPres≤ z y z≤y)))

ℝ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℝ≤Pseudolattice = makePseudolatticeFromPoset
  ℝPoset minℝ maxℝ
  (λ {a b} → min≤left a b)
  (λ {a b} → min≤right a b)
  (λ {a b x} → minGreatestLowerBound a b x)
  (λ {a b} → left≤max a b)
  (λ {a b} → right≤max a b)
  (λ {a b x} → maxLeastUpperBound a b x)
