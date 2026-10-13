module Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma.Properties
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Basic
open import Cubical.Analysis.Complex.Calculus.Derivative.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniqueness

-- An intrinsic function on an open subspace need not have a supplied
-- ambient extension. Subtract its two estimates instead: their difference
-- is the zero function, which has a canonical ambient extension.
module _ (P : ℙ ℂ) (openP : IsOpenPredicate (ℂPremetricSpace .snd) P) where
  private
    domain : PremetricSpace ℓ-zero ℓ-zero
    domain = PremetricSubspace ℂPremetricSpace P

  opaque
    openSubspaceComplexDerivativeValueUniqueAt : ∀ (f : fst domain → ℂ) point a b →
      IsComplexDerivativeAlongAt (snd domain) fst f a point →
      IsComplexDerivativeAlongAt (snd domain) fst f b point → a ≡ b
    openSubspaceComplexDerivativeValueUniqueAt f point a b first second =
      ℂRing.equalByDifference a b
        (complexDerivativeValueUniqueAt (λ _ → 0ℂ) (fst point) (a -ℂ b) 0ℂ
          (openSubspaceComplexDerivativeValueAtWithExtension P openP (λ y → f y -ℂ f y)
            (λ _ → 0ℂ) (a -ℂ b) (fst point) (snd point) difference
            (λ y → sym (+ℂInvR (f y))))
          (constantHasComplexDerivative 0ℂ (fst point)))
      where
      difference : IsComplexDerivativeAlongAt (snd domain) fst (λ y → f y -ℂ f y) (a -ℂ b) point
      difference = addHasComplexDerivativeAlongAt (snd domain) fst f (λ y → -ℂ f y) a (-ℂ b) point first
        (negHasComplexDerivativeAlongAt (snd domain) fst f b point second)

    openSubspaceComplexDerivativeFunctionUnique : ∀ f d e →
      IsComplexDerivativeAlong (snd domain) fst f d →
      IsComplexDerivativeAlong (snd domain) fst f e → d ≡ e
    openSubspaceComplexDerivativeFunctionUnique f d e first second = funExt λ point →
      openSubspaceComplexDerivativeValueUniqueAt f point (d point) (e point) (first point) (second point)

  -- The openness hypothesis is essential. No corresponding uniqueness is
  -- claimed for arbitrary subspaces or constant parameter coordinates.
  isPropOpenSubspaceHasComplexDerivativeAt : ∀ f point →
    isProp (Σ[ d ∈ ℂ ] IsComplexDerivativeAlongAt (snd domain) fst f d point)
  isPropOpenSubspaceHasComplexDerivativeAt f point (a , first) (b , second) = ΣPathPProp
    (λ d → isPropIsComplexDerivativeAlongAt (snd domain) fst f d point)
    (openSubspaceComplexDerivativeValueUniqueAt f point a b first second)
