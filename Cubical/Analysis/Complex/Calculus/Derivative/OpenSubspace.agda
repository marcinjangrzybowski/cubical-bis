module Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (min₊; min₊≤L; min₊≤R)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Base

restrictComplexDerivativeToSubspace : ∀ (P : ℙ ℂ) (function derivative : ℂ → ℂ) →
  IsComplexDerivative function derivative →
  IsComplexDerivativeAlong (PremetricSubspace ℂPremetricSpace P .snd) fst (function ∘ fst) (derivative ∘ fst)
restrictComplexDerivativeToSubspace P function derivative = pullbackComplexDerivativeAlong
  (PremetricSubspace ℂPremetricSpace P .snd) (ℂPremetricSpace .snd)
  (idfun ℂ) function derivative fst (snd (NE→C (subspaceInclusionNE ℂPremetricSpace P)))

-- Openness turns a relative estimate into an ambient complex derivative.
-- The ambient function only needs to agree with the supplied relative one;
-- no extension is constructed and no global neighbourhood is chosen.
opaque
  openSubspaceComplexDerivativeAlongValueAtWithExtension : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℂ) (P : ℙ A) →
    IsOpenPredicate source P →
    (relativeFunction : Σ A (_∈ P) → ℂ) (function : A → ℂ) →
    ∀ value x (member : x ∈ P) →
    IsComplexDerivativeAlongAt (PremetricSubspaceStr P source) (coordinate ∘ fst) relativeFunction value (x , member) →
    (∀ point → function (fst point) ≡ relativeFunction point) →
    IsComplexDerivativeAlongAt source coordinate function value x
  openSubspaceComplexDerivativeAlongValueAtWithExtension source coordinate P openP relativeFunction function value x member
    differentiable agrees ε = do
    (δ , estimate) ← differentiable ε
    (ρ , stays) ← openP x member
    return (min₊ δ ρ , λ y close →
      let
        near = PremetricStr.isMonotone≈≤ source x y (min₊ δ ρ) δ (min₊≤L δ ρ) close
        inside = stays y (PremetricStr.isMonotone≈≤ source x y (min₊ δ ρ) ρ (min₊≤R δ ρ) close)
        point = y , inside
      in subst (λ error → normℂ error ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))
        (sym (cong₂ (λ fy fx → (fy -ℂ fx) -ℂ value ·ℂ (coordinate y -ℂ coordinate x))
          (agrees point) (agrees (x , member))))
        (estimate point near))

openSubspaceComplexDerivativeValueAtWithExtension : ∀ (P : ℙ ℂ) →
  IsOpenPredicate (ℂPremetricSpace .snd) P →
  (relativeFunction : fst (PremetricSubspace ℂPremetricSpace P) → ℂ) →
  (function : ℂ → ℂ) → ∀ value x (member : x ∈ P) →
  IsComplexDerivativeAlongAt (PremetricSubspace ℂPremetricSpace P .snd) fst relativeFunction value (x , member) →
  (∀ point → function (fst point) ≡ relativeFunction point) →
  IsComplexDerivativeAt function value x
openSubspaceComplexDerivativeValueAtWithExtension =
  openSubspaceComplexDerivativeAlongValueAtWithExtension (ℂPremetricSpace .snd) (idfun ℂ)

openSubspaceComplexDerivativeAtWithExtension : ∀ (P : ℙ ℂ) →
  IsOpenPredicate (ℂPremetricSpace .snd) P →
  (relativeFunction relativeDerivative : fst (PremetricSubspace ℂPremetricSpace P) → ℂ) →
  (function : ℂ → ℂ) →
  IsComplexDerivativeAlong (PremetricSubspace ℂPremetricSpace P .snd) fst relativeFunction relativeDerivative →
  (∀ point → function (fst point) ≡ relativeFunction point) →
  ∀ x (member : x ∈ P) → IsComplexDerivativeAt function (relativeDerivative (x , member)) x
openSubspaceComplexDerivativeAtWithExtension P openP relativeFunction relativeDerivative function
  differentiable agrees x member = openSubspaceComplexDerivativeValueAtWithExtension
    P openP relativeFunction function (relativeDerivative (x , member)) x member
    (differentiable (x , member)) agrees

openSubspaceComplexDerivativeAt : ∀ (P : ℙ ℂ) → IsOpenPredicate (ℂPremetricSpace .snd) P →
  (function derivative : ℂ → ℂ) →
  IsComplexDerivativeAlong (PremetricSubspace ℂPremetricSpace P .snd) fst (function ∘ fst) (derivative ∘ fst) →
  ∀ x → x ∈ P → IsComplexDerivativeAt function (derivative x) x
openSubspaceComplexDerivativeAt P openP function derivative differentiable =
  openSubspaceComplexDerivativeAtWithExtension P openP (function ∘ fst) (derivative ∘ fst)
    function differentiable (λ _ → refl)
