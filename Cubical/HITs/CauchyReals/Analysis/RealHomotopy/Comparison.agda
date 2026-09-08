module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base using (Pointed)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding using (injEmbedding)
open import Cubical.Functions.Surjection
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.SetTruncation as ST
import Cubical.Homotopy.Group.Base as Synthetic
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.LoopGroup
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups

-- A precise sufficient criterion, not an assumed comparison theorem.
-- The analytic realization and approximation obligations remain explicit.
module Comparison {ℓ ℓ' ℓA} (n : ℕ)
  (X : PointedPremetricSpace ℓ ℓ') (A : Pointed ℓA) where
  private
    module R = Loops (fst (realΩ^ n X)) (snd (realΩ^ n X))
    Target = Synthetic.πGr n A
    module T = GroupStr (snd Target)

  module FromRepresentatives
    (realize : R.Loop → fst Target)
    (respects : (p q : R.Loop) → R.PathHomotopy p q → realize p ≡ realize q)
    (preserves : (p q : R.Loop) →
      realize (R.concatPath p q) ≡ T._·_ (realize p) (realize q))
    (complete : (p q : R.Loop) → realize p ≡ realize q → R.Homotopic p q)
    (represents : (a : fst Target) → ∥ Σ[ p ∈ R.Loop ] realize p ≡ a ∥₁) where

    opaque
      comparisonMap : R.LoopClass → fst Target
      comparisonMap = SQ.rec ST.squash₂ realize
        (λ p q → PT.rec (ST.squash₂ _ _) (respects p q))

      private
        injective : (p q : R.LoopClass) → comparisonMap p ≡ comparisonMap q → p ≡ q
        injective = SQ.elimProp2 (λ p q → isPropΠ (λ _ → SQ.squash/ p q))
          (λ p q same → SQ.eq/ {R = R.Homotopic} p q (complete p q same))

        surjective : isSurjection comparisonMap
        surjective a = PT.map (λ (p , same) → R.pathClass p , same) (represents a)

      representativeComparisonEquiv : GroupEquiv R.loopGroup Target
      representativeComparisonEquiv =
        (comparisonMap , isEmbedding×isSurjection→isEquiv
          (injEmbedding ST.squash₂ (λ {p} {q} → injective p q) , surjective)) ,
        makeIsGroupHom (SQ.elimProp2 (λ _ _ → ST.squash₂ _ _) preserves)

      comparisonIso : GroupIso (realπGr n X) Target
      comparisonIso = compGroupIso
        (invGroupIso (realπGr-loopGroup n X)) (GroupEquiv→GroupIso representativeComparisonEquiv)

      comparisonEquiv : GroupEquiv (realπGr n X) Target
      comparisonEquiv = GroupIso→GroupEquiv comparisonIso
