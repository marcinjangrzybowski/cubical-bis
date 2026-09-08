module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.ComparisonObligations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base using (Pointed)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupIso)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
import Cubical.Homotopy.Group.Base as Synthetic
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.LoopGroup using (module Loops)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Comparison using (module Comparison)

-- Abstract parameters keep record checking independent of the large
-- definitions of real loop spaces and synthetic group operations.
-- This statement is not postulated to have an inhabitant.
record RepresentativeData {ℓL ℓH ℓT}
  (Loop : Type ℓL) (Homotopy : Loop → Loop → Type ℓH)
  (concatenate : Loop → Loop → Loop) (Target : Group ℓT)
  : Type (ℓ-max ℓL (ℓ-max ℓH ℓT)) where
  field
    realize : Loop → fst Target

    respects : (p q : Loop) → Homotopy p q → realize p ≡ realize q

    preserves : (p q : Loop) →
      realize (concatenate p q) ≡
      GroupStr._·_ (snd Target) (realize p) (realize q)

    -- Injectivity after quotienting the real homotopies.
    complete : (p q : Loop) → realize p ≡ realize q → ∥ Homotopy p q ∥₁

    -- Surjectivity without choosing representatives globally.
    represents : (a : fst Target) → ∥ Σ[ p ∈ Loop ] realize p ≡ a ∥₁

module _ {ℓ ℓ' ℓA} (n : ℕ)
  (X : PointedPremetricSpace ℓ ℓ') (A : Pointed ℓA) where
  private
    module R = Loops (fst (realΩ^ n X)) (snd (realΩ^ n X))
    base = snd (realΩ^ n X)

  RepresentativeComparisonData :
    Type (ℓ-max (ℓ-max (loopLevel n ℓ ℓ') ℓ') ℓA)
  RepresentativeComparisonData = RepresentativeData R.Loop
    (R.PathHomotopy {x = base} {y = base})
    (R.concatPath {x = base} {y = base} {z = base}) (Synthetic.πGr n A)

  -- Reuse the checked quotient argument; the missing data is an input.
  opaque
    comparisonFromData : RepresentativeComparisonData →
      GroupIso (realπGr n X) (Synthetic.πGr n A)
    comparisonFromData missing = proof.comparisonIso
      where
      open RepresentativeData missing
      module C = Comparison {ℓ = ℓ} {ℓ' = ℓ'} {ℓA = ℓA} n X A
      module proof = C.FromRepresentatives realize respects preserves complete represents
