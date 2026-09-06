module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.Relation.Premetric.Base
open import Cubical.Categories.Category.Base using (Category; isIso)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Associativity

module FundamentalGroupoid {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Laws X public

  homotopic-equivalence : ∀ x y → BinaryRelation.isEquivRel (Homotopic {x} {y})
  homotopic-equivalence x y = BinaryRelation.equivRel
    (λ p → ∣ homotopy-refl p ∣₁)
    (λ p q → PT.map homotopy-sym)
    (λ p q r → PT.map2 homotopy-trans)

  PathClass : fst X → fst X → Type (ℓ-max ℓ ℓ')
  PathClass x y = UCPath x y SQ./ Homotopic

  pathClass : ∀ {x y} → UCPath x y → PathClass x y
  pathClass = SQ.[_]

  homotopy-class≡ : ∀ {x y} {p q : UCPath x y} → PathHomotopy p q → pathClass p ≡ pathClass q
  homotopy-class≡ h = SQ.eq/ _ _ ∣ h ∣₁

  -- Equality of classes is exactly (mere) endpoint-fixed UC homotopy.
  -- In particular, the quotient does not impose extra identifications.
  class≡≃homotopic : ∀ {x y} (p q : UCPath x y) →
    (pathClass p ≡ pathClass q) ≃ Homotopic p q
  class≡≃homotopic {x} {y} p q = isoToEquiv
    (SQ.isEquivRel→effectiveIso (λ _ _ → squash₁) (homotopic-equivalence x y) p q)

  identityClass : ∀ x → PathClass x x
  identityClass x = pathClass (constantPath x)

  composeClass : ∀ {x y z} → PathClass x y → PathClass y z → PathClass x z
  composeClass = SQ.rec2 SQ.squash/ (λ p q → pathClass (concatPath p q))
    (λ p p' q → PT.rec (SQ.squash/ _ _)
      (λ h → homotopy-class≡ (concat-homotopy h (homotopy-refl q))))
    (λ p q q' → PT.rec (SQ.squash/ _ _)
      (λ h → homotopy-class≡ (concat-homotopy (homotopy-refl p) h)))

  inverseClass : ∀ {x y} → PathClass x y → PathClass y x
  inverseClass = SQ.rec SQ.squash/ (λ p → pathClass (reversePath p))
    (λ p q → PT.rec (SQ.squash/ _ _) (λ h → homotopy-class≡ (reverse-homotopy h)))

  composeClass-unit-left : ∀ {x y} (f : PathClass x y) → composeClass (identityClass x) f ≡ f
  composeClass-unit-left = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ p → homotopy-class≡ (concat-unit-left p))

  composeClass-unit-right : ∀ {x y} (f : PathClass x y) → composeClass f (identityClass y) ≡ f
  composeClass-unit-right = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ p → homotopy-class≡ (concat-unit-right p))

  composeClass-assoc : ∀ {x y z w} (f : PathClass x y) (g : PathClass y z) (h : PathClass z w) →
    composeClass (composeClass f g) h ≡ composeClass f (composeClass g h)
  composeClass-assoc = SQ.elimProp3 (λ _ _ _ → SQ.squash/ _ _)
    (λ p q r → homotopy-class≡ (concat-assoc p q r))

  composeClass-inverse-left : ∀ {x y} (f : PathClass x y) →
    composeClass (inverseClass f) f ≡ identityClass y
  composeClass-inverse-left = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ p → homotopy-class≡ (concat-inverse-left p))

  composeClass-inverse-right : ∀ {x y} (f : PathClass x y) →
    composeClass f (inverseClass f) ≡ identityClass x
  composeClass-inverse-right = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ p → homotopy-class≡ (concat-inverse-right p))

  pathGroupoid : Category ℓ (ℓ-max ℓ ℓ')
  Category.ob pathGroupoid = fst X
  Category.Hom[_,_] pathGroupoid = PathClass
  Category.id pathGroupoid {x} = identityClass x
  Category._⋆_ pathGroupoid = composeClass
  Category.⋆IdL pathGroupoid = composeClass-unit-left
  Category.⋆IdR pathGroupoid = composeClass-unit-right
  Category.⋆Assoc pathGroupoid = composeClass-assoc
  Category.isSetHom pathGroupoid = SQ.squash/

  -- A category together with this proof is a groupoid.
  pathGroupoid-invertible : ∀ {x y} (f : PathClass x y) → isIso pathGroupoid f
  isIso.inv (pathGroupoid-invertible f) = inverseClass f
  isIso.sec (pathGroupoid-invertible f) = composeClass-inverse-left f
  isIso.ret (pathGroupoid-invertible f) = composeClass-inverse-right f
