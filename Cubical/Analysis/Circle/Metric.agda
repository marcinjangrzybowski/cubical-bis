module Cubical.Analysis.Circle.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Rationals.Base as ℚ using ([_/_])
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Circle.Base

private module R = PremetricStr (snd ℝPremetricSpace)

quarter : ℚ₊
quarter = [ 1 / 4 ]₊

turnRadius : ℚ₊
turnRadius = [ 1 / 1 ]₊

sub-close-zero : ∀ x y ε → x ∼[ ε ] y → (x - y) ∼[ ε ] 0ℝ
sub-close-zero x y ε close =
  subst (λ z → (x - y) ∼[ ε ] z) (subSelf y)
    (add-pres∼₁ x y (- y) ε close)

cover-injective-near : ∀ x y → x ∼[ turnRadius ] y → cover x ≡ cover y → x ≡ y
cover-injective-near x y close equal =
  sym (subAddCancel x y) ∙ cong (_+ y) difference-zero ∙ addIdL y
  where
  witness = cover-effective x y equal
  k-zero : fst witness ≡ ℤ.pos 0
  k-zero = integer-separated (fst witness) (ℤ.pos 0)
    (subst (λ z → z ∼[ turnRadius ] 0ℝ) (snd witness) (sub-close-zero x y turnRadius close))
  difference-zero : x - y ≡ 0ℝ
  difference-zero = snd witness ∙ cong integer k-zero

-- A displacement is a short real translation, not a selected representative
-- of either quotient point.  The metric forgets this witness by truncation.
Displacement : Circle → ℚ₊ → Circle → Type
Displacement p ε q = Σ[ t ∈ ℝ ] (t ∼[ ε ] 0ℝ) × (p +ᶜ cover t ≡ q)

infix 4 _≈ᶜ[_]_
_≈ᶜ[_]_ : Circle → ℚ₊ → Circle → Type
p ≈ᶜ[ ε ] q = ∥ Displacement p ε q ∥₁

displacement-unique : ∀ p q ε δ → ε +₊ δ ≤₊ turnRadius →
  (u : Displacement p ε q) (v : Displacement p δ q) → fst u ≡ fst v
displacement-unique p q ε δ bound (s , s-small , s-step) (t , t-small , t-step) =
  cover-injective-near s t
    (R.isMonotone≈≤ s t (ε +₊ δ) turnRadius bound
      (triangle∼ s 0ℝ t ε δ s-small (sym∼ t 0ℝ δ t-small)))
    (CircleGroup.·CancelL p (s-step ∙ sym t-step))

private
  quarters≤turnRadius : quarter +₊ quarter ≤₊ turnRadius
  quarters≤turnRadius = ℚ.inj (ℤ.pos≤pos tt)

isPropShortDisplacement : ∀ p q → isProp (Displacement p quarter q)
isPropShortDisplacement p q u v = Σ≡Prop
  (λ t → isProp× (R.isProp≈ t 0ℝ quarter) (isSetCircle _ _))
  (displacement-unique p q quarter quarter quarters≤turnRadius u v)

shortDisplacement : ∀ p q → p ≈ᶜ[ quarter ] q → Displacement p quarter q
shortDisplacement p q = PT.rec (isPropShortDisplacement p q) (λ x → x)

private
  circle-separated : ∀ p q → (∀ ε → p ≈ᶜ[ ε ] q) → p ≡ q
  circle-separated p q close =
    sym (circle-add-zero p) ∙ cong (p +ᶜ_) (cong cover (sym (eqℝ t 0ℝ t-zero)))
    ∙ snd (snd chosen)
    where
    chosen = shortDisplacement p q (close quarter)
    t = fst chosen
    t-zero : ∀ ε → t ∼[ ε ] 0ℝ
    t-zero ε = PT.rec (R.isProp≈ t 0ℝ ε) small (close (min₊ ε quarter))
      where
      small : Displacement p (min₊ ε quarter) q → t ∼[ ε ] 0ℝ
      small (u , u-small , u-step) =
        subst (λ z → z ∼[ ε ] 0ℝ) (sym same)
          (R.isMonotone≈≤ u 0ℝ (min₊ ε quarter) ε (min₊≤L ε quarter) u-small)
        where
        same : t ≡ u
        same = displacement-unique p q quarter quarter quarters≤turnRadius chosen
          (u , R.isMonotone≈≤ u 0ℝ (min₊ ε quarter) quarter
            (min₊≤R ε quarter) u-small , u-step)

  circle-refl : ∀ p ε → p ≈ᶜ[ ε ] p
  circle-refl p ε = ∣ 0ℝ , refl∼ 0ℝ ε , circle-add-zero p ∣₁

  circle-sym : ∀ p q ε → p ≈ᶜ[ ε ] q → q ≈ᶜ[ ε ] p
  circle-sym p q ε = PT.map λ (t , small , step) →
    - t ,
    subst (λ z → (- t) ∼[ ε ] z) negZero
      (IsNonExpanding.pres≈ neg-isNonExpanding t 0ℝ ε small) ,
    (cong (_+ᶜ cover (- t)) (sym step)
    ∙ sym (circle-add-assoc p (cover t) (cover (- t)))
    ∙ cong (p +ᶜ_) (sym (cover-add t (- t)) ∙ cong cover (addInvR t))
    ∙ circle-add-zero p)

  circle-triangle : ∀ p q r ε δ → p ≈ᶜ[ ε ] q → q ≈ᶜ[ δ ] r → p ≈ᶜ[ ε +₊ δ ] r
  circle-triangle p q r ε δ = PT.map2 λ (s , small-s , step-s) (t , small-t , step-t) →
    s + t ,
    subst (λ z → (s + t) ∼[ ε +₊ δ ] z) (addIdL 0ℝ)
      (add-pres∼ s 0ℝ t 0ℝ ε δ small-s small-t) ,
    (cong (p +ᶜ_) (cover-add s t)
    ∙ circle-add-assoc p (cover s) (cover t)
    ∙ cong (_+ᶜ cover t) step-s ∙ step-t)

  circle-rounded : ∀ p q ε → p ≈ᶜ[ ε ] q → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (p ≈ᶜ[ δ ] q)
  circle-rounded p q ε = PT.rec squash₁ λ (t , small , step) →
    PT.map (λ (δ , bound , smaller) → δ , bound , ∣ t , smaller , step ∣₁)
      (R.isRounded≈ t 0ℝ ε small)

CirclePremetricSpace : PremetricSpace ℓ-zero ℓ-zero
CirclePremetricSpace = premetricspace Circle _≈ᶜ[_]_
  (ispremetric isSetCircle (λ _ _ _ → squash₁) circle-refl circle-sym
    circle-separated circle-triangle circle-rounded)

coverNE : NE[ ℝPremetricSpace , CirclePremetricSpace ]
fst coverNE = cover
snd coverNE .IsNonExpanding.pres≈ x y ε close =
  ∣ y - x , sub-close-zero y x ε (sym∼ x y ε close) ,
    sym (cover-add x (y - x))
    ∙ cong cover (addComm x (y - x) ∙ subAddCancel y x) ∣₁

coverUC : UC[ ℝPremetricSpace , CirclePremetricSpace ]
coverUC = NE→UC coverNE
