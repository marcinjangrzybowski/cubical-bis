module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.PointedCarrierMaps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_)
open import Cubical.Foundations.Pointed.Properties
  using (_∘∙_; id∙; ∘∙-idˡ; ∘∙-assoc)
open import Cubical.Data.Sigma

private
  variable
    ℓX ℓY ℓZ ℓS : Level
    X : Pointed ℓX
    Y : Pointed ℓY
    Z : Pointed ℓZ
    S : Pointed ℓS

-- Evaluation at the chosen point is an equivalence when its domain is
-- contractible. The pointed mapping type is its fiber. No truncation
-- or contractibility of the TARGET is required.
pointed-maps-contractible : isContr (fst X) → isContr (X →∙ Y)
pointed-maps-contractible {X = X} {Y = Y} c =
  equiv-proof (snd (Π-contractDom {B = λ _ → fst Y}
    (snd X , isContr→isProp c (snd X)))) (snd Y)

PointedOver : (X →∙ S) → (Y →∙ S) → Type _
PointedOver p q = Σ[ w ∈ (_ →∙ _) ] q ∘∙ w ≡ p

pointed-over-contractible : (p : X →∙ S) (q : Y →∙ S) →
  isContr (fst X) → isContr (PointedOver p q)
pointed-over-contractible p q c = isContrΣ (pointed-maps-contractible c)
  (λ w → isContr→isContrPath (pointed-maps-contractible c) (q ∘∙ w) p)

identityOver : (p : X →∙ S) → PointedOver p p
identityOver {X = X} p = id∙ X , ∘∙-idˡ p

composeOver : {p : X →∙ S} {q : Y →∙ S} {r : Z →∙ S} →
  PointedOver q r → PointedOver p q → PointedOver p r
composeOver {r = r} (g , β) (f , α) = (g ∘∙ f) ,
  sym (∘∙-assoc r g f) ∙ cong (λ k → k ∘∙ f) β ∙ α

-- Forgetting the basepoint structure still retains the whole commuting
-- homotopy in S. Equality of PointedOver values preserves this data.
overMap : {p : X →∙ S} {q : Y →∙ S} → PointedOver p q → fst X → fst Y
overMap w = fst (fst w)

overMap-commutes : {p : X →∙ S} {q : Y →∙ S} (w : PointedOver p q) →
  (λ x → fst q (overMap {p = p} {q = q} w x)) ≡ fst p
overMap-commutes w = cong fst (snd w)
