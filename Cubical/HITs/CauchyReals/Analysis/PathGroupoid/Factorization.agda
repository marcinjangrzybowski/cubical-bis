module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Factorization where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Composition
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Pasting
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open CategoryStructures using (_∘UC_; idᵘᶜ)

module Clocks = Composition Interval

identityClock : Clocks.UCPath 𝟘 𝟙
identityClock = idᵘᶜ , refl , refl

module Factorization {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Composition X public

  -- Two traversals of one real-parameter curve are homotopic whenever
  -- their clocks have the same endpoints. Interpolation takes place in
  -- the interval; no interpolation operation on X is needed.
  factor-homotopy : ∀ {x y i j} (F : UC[ Interval , X ])
    (a b : Clocks.UCPath i j) (p q : UCPath x y) →
    (∀ t → at p t ≡ fst F (Clocks.at a t)) →
    (∀ t → at q t ≡ fst F (Clocks.at b t)) → PathHomotopy p q
  factor-homotopy F a b p q pa qb = result
    where
    open PathHomotopy
    left right : UC[ IntervalSquare , Interval ]
    left = fst a ∘UC productSndUC
    right = fst b ∘UC productSndUC
    result : PathHomotopy p q
    deformation result = F ∘UC blendUC productFstUC left right
    at-start result t = cong (fst F) (blend-0 productFstUC left right (𝟘 , t) refl) ∙ sym (pa t)
    at-end result t = cong (fst F) (blend-1 productFstUC left right (𝟙 , t) refl) ∙ sym (qb t)
    fixes-start result s = cong (fst F) (blend-same productFstUC left right (s , 𝟘)
      (fst (snd a) ∙ sym (fst (snd b)))) ∙ sym (pa 𝟘) ∙ fst (snd p)
    fixes-end result s = cong (fst F) (blend-same productFstUC left right (s , 𝟙)
      (snd (snd a) ∙ sym (snd (snd b)))) ∙ sym (pa 𝟙) ∙ snd (snd p)

  concat-factor : ∀ {x y z i j k} (F : UC[ Interval , X ])
    (a : Clocks.UCPath i j) (b : Clocks.UCPath j k)
    (p : UCPath x y) (q : UCPath y z) →
    (∀ t → at p t ≡ fst F (Clocks.at a t)) →
    (∀ t → at q t ≡ fst F (Clocks.at b t)) →
    ∀ t → at (concatPath p q) t ≡ fst F (Clocks.at (Clocks.concatPath a b) t)
  concat-factor F a b p q pa qb t = concat-eq p q t _
    (λ upper → pa (fst early t) ∙ cong (fst F) (sym (Clocks.concat-left a b t upper)))
    (λ lower → qb (fst late t) ∙ cong (fst F) (sym (Clocks.concat-right a b t lower)))

  concat-unit-left : ∀ {x y} (p : UCPath x y) → PathHomotopy (concatPath (constantPath x) p) p
  concat-unit-left {x} p = factor-homotopy (fst p)
    (Clocks.concatPath (Clocks.constantPath 𝟘) identityClock) identityClock
    (concatPath (constantPath x) p) p
    (concat-factor (fst p) (Clocks.constantPath 𝟘) identityClock (constantPath x) p
      (λ _ → sym (fst (snd p))) (λ _ → refl)) (λ _ → refl)

  concat-unit-right : ∀ {x y} (p : UCPath x y) → PathHomotopy (concatPath p (constantPath y)) p
  concat-unit-right {y = y} p = factor-homotopy (fst p)
    (Clocks.concatPath identityClock (Clocks.constantPath 𝟙)) identityClock
    (concatPath p (constantPath y)) p
    (concat-factor (fst p) identityClock (Clocks.constantPath 𝟙) p (constantPath y)
      (λ _ → refl) (λ _ → sym (snd (snd p)))) (λ _ → refl)

  concat-inverse-right : ∀ {x y} (p : UCPath x y) →
    PathHomotopy (concatPath p (reversePath p)) (constantPath x)
  concat-inverse-right {x} p = factor-homotopy (fst p)
    (Clocks.concatPath identityClock (Clocks.reversePath identityClock)) (Clocks.constantPath 𝟘)
    (concatPath p (reversePath p)) (constantPath x)
    (concat-factor (fst p) identityClock (Clocks.reversePath identityClock) p (reversePath p)
      (λ _ → refl) (λ _ → refl)) (λ _ → sym (fst (snd p)))

  concat-inverse-left : ∀ {x y} (p : UCPath x y) →
    PathHomotopy (concatPath (reversePath p) p) (constantPath y)
  concat-inverse-left {y = y} p = factor-homotopy (fst p)
    (Clocks.concatPath (Clocks.reversePath identityClock) identityClock) (Clocks.constantPath 𝟙)
    (concatPath (reversePath p) p) (constantPath y)
    (concat-factor (fst p) (Clocks.reversePath identityClock) identityClock (reversePath p) p
      (λ _ → refl) (λ _ → refl)) (λ _ → sym (snd (snd p)))

  -- Associativity for three paths which already factor through one curve.
  factor-assoc : ∀ {x y z w i j k l} (F : UC[ Interval , X ])
    (a : Clocks.UCPath i j) (b : Clocks.UCPath j k) (c : Clocks.UCPath k l)
    (p : UCPath x y) (q : UCPath y z) (r : UCPath z w) →
    (∀ t → at p t ≡ fst F (Clocks.at a t)) →
    (∀ t → at q t ≡ fst F (Clocks.at b t)) →
    (∀ t → at r t ≡ fst F (Clocks.at c t)) →
    PathHomotopy (concatPath (concatPath p q) r) (concatPath p (concatPath q r))
  factor-assoc F a b c p q r pa qb rc = factor-homotopy F
    (Clocks.concatPath (Clocks.concatPath a b) c) (Clocks.concatPath a (Clocks.concatPath b c))
    (concatPath (concatPath p q) r) (concatPath p (concatPath q r))
    (concat-factor F (Clocks.concatPath a b) c (concatPath p q) r
      (concat-factor F a b p q pa qb) rc)
    (concat-factor F a (Clocks.concatPath b c) p (concatPath q r)
      pa (concat-factor F b c q r qb rc))
