module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open CategoryStructures using (_∘UC_; idᵘᶜ)

module Paths {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  private
    module P = PremetricStr (snd X)

  -- The domain is the closed real interval, with its subspace premetric.
  UCPath : fst X → fst X → Type (ℓ-max ℓ ℓ')
  UCPath x y = Σ[ p ∈ UC[ Interval , X ] ] (fst p 𝟘 ≡ x) × (fst p 𝟙 ≡ y)

  at : ∀ {x y} → UCPath x y → 𝕀 → fst X
  at p = fst (fst p)

  path-ext : ∀ {x y} {p q : UCPath x y} → (∀ t → at p t ≡ at q t) → p ≡ q
  path-ext same = Σ≡Prop (λ p → isProp× (P.isSetM _ _) (P.isSetM _ _))
    (Σ≡Prop (λ _ → squash₁) (funExt same))

  isSetUCPath : ∀ x y → isSet (UCPath x y)
  isSetUCPath x y = isSetΣ (isSetΣ (isSetΠ (λ _ → P.isSetM)) (λ _ → isProp→isSet squash₁))
    (λ _ → isProp→isSet (isProp× (P.isSetM _ _) (P.isSetM _ _)))

  constantPath : (x : fst X) → UCPath x x
  constantPath x = constantUC x , refl , refl

  reversePath : ∀ {x y} → UCPath x y → UCPath y x
  reversePath p = fst p ∘UC reverseTimeUC ,
    (cong (at p) reverseTime-0 ∙ snd (snd p)) ,
    (cong (at p) reverseTime-1 ∙ fst (snd p))

  reversePath-involutive : ∀ {x y} (p : UCPath x y) → reversePath (reversePath p) ≡ p
  reversePath-involutive p = path-ext (λ t → cong (at p) (reverseTime-involutive t))

  -- Homotopies are jointly uniformly continuous, relative to both endpoints.
  record PathHomotopy {x y} (p q : UCPath x y) : Type (ℓ-max ℓ ℓ') where
    field
      deformation : UC[ IntervalSquare , X ]
      at-start : ∀ t → fst deformation (𝟘 , t) ≡ at p t
      at-end : ∀ t → fst deformation (𝟙 , t) ≡ at q t
      fixes-start : ∀ s → fst deformation (s , 𝟘) ≡ x
      fixes-end : ∀ s → fst deformation (s , 𝟙) ≡ y

  Homotopic : ∀ {x y} → UCPath x y → UCPath x y → Type (ℓ-max ℓ ℓ')
  Homotopic p q = ∥ PathHomotopy p q ∥₁

  homotopy-refl : ∀ {x y} (p : UCPath x y) → PathHomotopy p p
  PathHomotopy.deformation (homotopy-refl p) = fst p ∘UC productSndUC
  PathHomotopy.at-start (homotopy-refl p) t = refl
  PathHomotopy.at-end (homotopy-refl p) t = refl
  PathHomotopy.fixes-start (homotopy-refl p) s = fst (snd p)
  PathHomotopy.fixes-end (homotopy-refl p) s = snd (snd p)

  homotopy-sym : ∀ {x y} {p q : UCPath x y} → PathHomotopy p q → PathHomotopy q p
  PathHomotopy.deformation (homotopy-sym h) = PathHomotopy.deformation h ∘UC
    pairUC (reverseTimeUC ∘UC productFstUC) productSndUC
  PathHomotopy.at-start (homotopy-sym h) t =
    cong (λ s → fst (PathHomotopy.deformation h) (s , t)) reverseTime-0 ∙ PathHomotopy.at-end h t
  PathHomotopy.at-end (homotopy-sym h) t =
    cong (λ s → fst (PathHomotopy.deformation h) (s , t)) reverseTime-1 ∙ PathHomotopy.at-start h t
  PathHomotopy.fixes-start (homotopy-sym h) s = PathHomotopy.fixes-start h (reverseTime s)
  PathHomotopy.fixes-end (homotopy-sym h) s = PathHomotopy.fixes-end h (reverseTime s)

  reparametrize : ∀ {x y} (p : UCPath x y) (ρ : UC[ Interval , Interval ]) →
    fst ρ 𝟘 ≡ 𝟘 → fst ρ 𝟙 ≡ 𝟙 → UCPath x y
  reparametrize p ρ at0 at1 = fst p ∘UC ρ ,
    (cong (at p) at0 ∙ fst (snd p)) , (cong (at p) at1 ∙ snd (snd p))

  reparametrize-homotopy : ∀ {x y} (p : UCPath x y) (ρ : UC[ Interval , Interval ])
    (at0 : fst ρ 𝟘 ≡ 𝟘) (at1 : fst ρ 𝟙 ≡ 𝟙) →
    PathHomotopy p (reparametrize p ρ at0 at1)
  reparametrize-homotopy p ρ at0 at1 = homotopy
    where
    left right : UC[ IntervalSquare , Interval ]
    left = productSndUC
    right = ρ ∘UC productSndUC
    homotopy : PathHomotopy p (reparametrize p ρ at0 at1)
    PathHomotopy.deformation homotopy = fst p ∘UC blendUC productFstUC left right
    PathHomotopy.at-start homotopy t = cong (at p) (blend-0 productFstUC left right (𝟘 , t) refl)
    PathHomotopy.at-end homotopy t = cong (at p) (blend-1 productFstUC left right (𝟙 , t) refl)
    PathHomotopy.fixes-start homotopy s =
      cong (at p) (blend-same productFstUC left right (s , 𝟘) (sym at0)) ∙ fst (snd p)
    PathHomotopy.fixes-end homotopy s =
      cong (at p) (blend-same productFstUC left right (s , 𝟙) (sym at1)) ∙ snd (snd p)
