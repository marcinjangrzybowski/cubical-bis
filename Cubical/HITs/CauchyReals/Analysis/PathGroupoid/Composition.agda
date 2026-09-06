module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Pasting
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Unit
open CategoryStructures using (_∘UC_)

module Composition {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Paths X public

  module Join {x y z} (p : UCPath x y) (q : UCPath y z) where
    module P = Paste X UnitPremetricSpace (fst p ∘UC productFstUC) (fst q ∘UC productFstUC)
      (λ _ → snd (snd p) ∙ sym (fst (snd q)))

    path : UCPath x z
    path = (P.pastedUC ∘UC rightInsertionUC Interval UnitPremetricSpace tt) ,
      (P.pasted-0 tt ∙ fst (snd p)) , (P.pasted-1 tt ∙ snd (snd q))

  concatPath : ∀ {x y z} → UCPath x y → UCPath y z → UCPath x z
  concatPath = Join.path

  concat-left : ∀ {x y z} (p : UCPath x y) (q : UCPath y z) t →
    fst t ·ᵣ 3 <ᵣ 2 → at (concatPath p q) t ≡ at p (fst early t)
  concat-left p q t = Join.P.pasted-left p q t tt

  concat-right : ∀ {x y z} (p : UCPath x y) (q : UCPath y z) t →
    1 <ᵣ fst t ·ᵣ 3 → at (concatPath p q) t ≡ at q (fst late t)
  concat-right p q t = Join.P.pasted-right p q t tt

  concat-eq : ∀ {x y z} (p : UCPath x y) (q : UCPath y z) t (v : fst X) →
    (fst t ·ᵣ 3 <ᵣ 2 → at p (fst early t) ≡ v) →
    (1 <ᵣ fst t ·ᵣ 3 → at q (fst late t) ≡ v) → at (concatPath p q) t ≡ v
  concat-eq p q t = Join.P.pasted-eq p q t tt

  concat-waiting : ∀ {x y z} (p : UCPath x y) (q : UCPath y z) (t : 𝕀) →
    rat [ 1 / 3 ] ≤ᵣ fst t → fst t ≤ᵣ rat [ 2 / 3 ] → at (concatPath p q) t ≡ y
  concat-waiting p q t lower upper = concat-eq p q t _
    (λ _ → cong (at p) (early-finished t lower) ∙ snd (snd p))
    (λ _ → cong (at q) (late-not-started t upper) ∙ fst (snd q))

  homotopy-trans : ∀ {x y} {p q r : UCPath x y} →
    PathHomotopy p q → PathHomotopy q r → PathHomotopy p r
  homotopy-trans h k = result
    where
    open PathHomotopy
    module P = Paste X Interval (deformation h) (deformation k)
      (λ t → at-end h t ∙ sym (at-start k t))
    result : PathHomotopy _ _
    deformation result = P.pastedUC
    at-start result t = P.pasted-0 t ∙ at-start h t
    at-end result t = P.pasted-1 t ∙ at-end k t
    fixes-start result s = P.pasted-eq s 𝟘 _
      (λ _ → fixes-start h (fst early s)) (λ _ → fixes-start k (fst late s))
    fixes-end result s = P.pasted-eq s 𝟙 _
      (λ _ → fixes-end h (fst early s)) (λ _ → fixes-end k (fst late s))

  concat-homotopy : ∀ {x y z} {p p' : UCPath x y} {q q' : UCPath y z} →
    PathHomotopy p p' → PathHomotopy q q' →
    PathHomotopy (concatPath p q) (concatPath p' q')
  concat-homotopy {p = p} {p'} {q} {q'} h k = result
    where
    open PathHomotopy
    swap : UC[ IntervalSquare , IntervalSquare ]
    swap = pairUC productSndUC productFstUC
    module P = Paste X Interval (deformation h ∘UC swap) (deformation k ∘UC swap)
      (λ s → fixes-end h s ∙ sym (fixes-start k s))
    result : PathHomotopy (concatPath p q) (concatPath p' q')
    deformation result = P.pastedUC ∘UC swap
    at-start result t = P.pasted-eq t 𝟘 _
      (λ upper → at-start h (fst early t) ∙ sym (concat-left p q t upper))
      (λ lower → at-start k (fst late t) ∙ sym (concat-right p q t lower))
    at-end result t = P.pasted-eq t 𝟙 _
      (λ upper → at-end h (fst early t) ∙ sym (concat-left p' q' t upper))
      (λ lower → at-end k (fst late t) ∙ sym (concat-right p' q' t lower))
    fixes-start result s = P.pasted-0 s ∙ fixes-start h s
    fixes-end result s = P.pasted-1 s ∙ fixes-end k s

  reverse-homotopy : ∀ {x y} {p q : UCPath x y} → PathHomotopy p q →
    PathHomotopy (reversePath p) (reversePath q)
  reverse-homotopy h = result
    where
    open PathHomotopy
    result : PathHomotopy _ _
    deformation result = deformation h ∘UC pairUC productFstUC (reverseTimeUC ∘UC productSndUC)
    at-start result t = at-start h (reverseTime t)
    at-end result t = at-end h (reverseTime t)
    fixes-start result s = cong (λ t → fst (deformation h) (s , t)) reverseTime-0 ∙ fixes-end h s
    fixes-end result s = cong (λ t → fst (deformation h) (s , t)) reverseTime-1 ∙ fixes-start h s
