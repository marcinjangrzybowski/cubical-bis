module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CornerCarriedMaps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base using (fiber)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCorners
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CornerWeakening
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarriedMaps

module AtCornerMaps (n : ℕ) (v : Corner (suc n)) where
  open AtCorner n v

  fiberTransition : (s t : CornerCarrier) (y : fst (boundary∙ n v)) →
    fiber (fst (toBoundary s)) y → fiber (fst (toBoundary t)) y
  fiberTransition s t = fiberAction {p = toBoundary s} {q = toBoundary t} (transition s t)

  fiberTransition-identity : (s : CornerCarrier) (y : fst (boundary∙ n v))
    (z : fiber (fst (toBoundary s)) y) → fiberTransition s s y z ≡ z
  fiberTransition-identity s y z =
    cong (λ w → fiberAction {p = toBoundary s} {q = toBoundary s} w y z)
      (transition-identity s) ∙ fiberAction-identity (toBoundary s) y z

  fiberTransition-composition : (s t u : CornerCarrier) (y : fst (boundary∙ n v))
    (z : fiber (fst (toBoundary s)) y) →
    fiberTransition t u y (fiberTransition s t y z) ≡ fiberTransition s u y z
  fiberTransition-composition s t u y z =
    sym (fiberAction-composition {p = toBoundary s} {q = toBoundary t} {r = toBoundary u}
      (transition t u) (transition s t) y z) ∙
    cong (λ w → fiberAction {p = toBoundary s} {q = toBoundary u} w y z)
      (transition-composition s t u)

  module _ {ℓD} {D : Type ℓD} (f : D → fst (boundary∙ n v)) where
    weakenCarried : (s t : CornerCarrier) →
      CarriedMap (fst (toBoundary s)) f → CarriedMap (fst (toBoundary t)) f
    weakenCarried s t = mapCarried (fst (toBoundary s)) (fst (toBoundary t)) (fiberTransition s t) f

    weakenCarried-identity : (s : CornerCarrier) (c : CarriedMap (fst (toBoundary s)) f) →
      weakenCarried s s c ≡ c
    weakenCarried-identity s c = funExt λ x → fiberTransition-identity s (f x) (c x)

    weakenCarried-composition : (s t u : CornerCarrier) (c : CarriedMap (fst (toBoundary s)) f) →
      weakenCarried t u (weakenCarried s t c) ≡ weakenCarried s u c
    weakenCarried-composition s t u c = funExt λ x → fiberTransition-composition s t u (f x) (c x)

    -- Restriction to an entire boundary or any face is ordinary
    -- precomposition. This commutation is definitional in all dimensions.
    weakenCarried-restrict : ∀ {ℓB} {B : Type ℓB} (i : B → D)
      (s t : CornerCarrier) (c : CarriedMap (fst (toBoundary s)) f) →
      (λ x → weakenCarried s t c (i x)) ≡
      mapCarried (fst (toBoundary s)) (fst (toBoundary t)) (fiberTransition s t)
        (λ x → f (i x)) (λ x → c (i x))
    weakenCarried-restrict i s t c = refl

    weakenExtension : ∀ {ℓB} {B : Type ℓB} (i : B → D) (s t : CornerCarrier)
      (b : (z : B) → fiber (fst (toBoundary s)) (f (i z))) →
      RelativeSections i (λ x → fiber (fst (toBoundary s)) (f x)) b →
      RelativeSections i (λ x → fiber (fst (toBoundary t)) (f x))
        (λ z → fiberTransition s t (f (i z)) (b z))
    weakenExtension i s t b = mapRelativeSections i
      (λ x → fiber (fst (toBoundary s)) (f x))
      (λ x → fiber (fst (toBoundary t)) (f x))
      (λ x → fiberTransition s t (f x)) b
