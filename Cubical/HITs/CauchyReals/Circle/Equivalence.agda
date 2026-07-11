module Cubical.HITs.CauchyReals.Circle.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Data.Nat as ℕ hiding (_·_;_+_;_choose_)
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ using ([_/_])
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_ ; ^ⁿ-even)

open import Cubical.HITs.CauchyReals.RationalsImports using (ℚ₊ ; fromNatℚ₊)
open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.PiNumber

open import Cubical.HITs.CauchyReals.TrigBase using
  ( sin
  ; cos
  ; sin·sin+cos·cos=1
  ; cos-even
  ; sin-odd
  )
open import Cubical.HITs.CauchyReals.TrigonometricIdentities

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.CauchyReals.Circle

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

cDistInj : ∀ x y → cDist x y ≡ 0 → x ≡ y
cDistInj = SQ.ElimProp2.go w
 where
 w : ElimProp2 (λ z z₁ → cDist z z₁ ≡ 0 → z ≡ z₁)
 w .ElimProp2.isPropB _ _ = isPropΠ λ _ → isSetCircle _ _
 w .ElimProp2.f a a' 1-cosΔ=0 =
   let w = cos=1⇒ (a -ᵣ a') (cong cos (·ᵣAssoc _ _ _)
            ∙ sym (𝐑'.equalByDifference _ _ 1-cosΔ=0))
    in eq/ a a' (map-snd
         (λ p → ℝ! ∙ p) w)

cDist≡ℝ²-dist : ∀ x y → 2 ·ᵣ cDist x y ≡
      (sinFromCircle x -ᵣ sinFromCircle y) ^ⁿ 2
   +ᵣ ((cosFromCircle x -ᵣ cosFromCircle y) ^ⁿ 2)
cDist≡ℝ²-dist = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = isSetℝ _ _
 w .ElimProp2.f x y =
     𝐑'.·DistR- _ _ _
   ∙ cong₂ _-ᵣ_
     (sym (x+x≡2x _)
      ∙ cong₂ _+ᵣ_ (sym (sin·sin+cos·cos=1 (x ·ᵣ (2 ·ᵣ π-number))))
                   (sym (sin·sin+cos·cos=1 (y ·ᵣ (2 ·ᵣ π-number)))))
     (cong (2 ·ᵣ_) (cong cos (sym (·ᵣAssoc _ _ _)
          ∙ 𝐑'.·DistL- _ _ _) ∙
           cosOfSum _ _ ∙ cong₂ _-ᵣ_
             (cong₂ _·ᵣ_ refl (sym (cos-even _)) )
             (cong₂ _·ᵣ_ refl (sym (sin-odd _))))
       ∙ sym (x+x≡2x _))
   ∙ ℝ!
   ∙ cong₂ _+ᵣ_
    (sym (x^²=x·x _))
    (sym (x^²=x·x _))

Circle→[cos,sin]-inj : ∀ x y →
                ((cosFromCircle x ≡ cosFromCircle y)
                × (sinFromCircle x ≡ sinFromCircle y))
                 → x ≡ y
Circle→[cos,sin]-inj x y (cosx≡cosy , sinx≡siny) =
  cDistInj x y (
       (sym (𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _)
        ∙ decℚ≡ᵣ?)) ∙ sym (·ᵣAssoc _ _ _))
    ∙∙ cong (rat [ 1 / 2 ] ·ᵣ_) (cDist≡ℝ²-dist x y ∙
   cong₂ _+ᵣ_
    (cong (_^ⁿ 2) (𝐑'.+InvR' _ _ sinx≡siny) ∙ 0^ⁿ 1)
    (cong (_^ⁿ 2) (𝐑'.+InvR' _ _ cosx≡cosy) ∙ 0^ⁿ 1)
   ∙ +ᵣ-rat 0 0) ∙∙ (sym (rat·ᵣrat _ _)
        ∙ decℚ≡ᵣ?))

isEquivCircle→distCircle : isEquiv Circle→distCircle
isEquivCircle→distCircle =
  isEmbedding×isSurjection→isEquiv
    (injEmbedding isSetDistCircle
      (λ {x} {y} p →
         Circle→[cos,sin]-inj x y
           (PathPΣ (cong fst p)))
    , Circle→[cos,sin]-surj)

Circle≃distCircle : Circle ≃ distCircle
Circle≃distCircle = Circle→distCircle , isEquivCircle→distCircle

CircleOverlap→Circle-inj : ∀ ε → ∀ x y →
   CircleOverlap[ ε ]→Circle x ≡  CircleOverlap[ ε ]→Circle y
   → x ≡ y
CircleOverlap→Circle-inj ε = SQ.ElimProp2.go w
 where
 w : ElimProp2
      (λ z z₁ →
         CircleOverlap[ ε ]→Circle z ≡ CircleOverlap[ ε ]→Circle z₁ →
         z ≡ z₁)
 w .ElimProp2.isPropB _ _ = isPropΠ λ _ → squash/ _ _
 w .ElimProp2.f x y x₁ = eq/ _ _
   (SQ.effective isPropCircle-rel isEquivRelCircleRel _ _ x₁)

opaque
 CircleOverlap→[cos,sin]-surj : ∀ ε → isSurjection
   (Circle→distCircle ∘ CircleOverlap[ ε ]→Circle)
 CircleOverlap→[cos,sin]-surj ε ((x , y) , x²+y²≡1) =
   PT.map (λ (φ , φ∈ , cosφ≡x , sinφ≡y) →
     [ (φ ／ᵣ₊ (2 ₊·ᵣ π-number₊) +ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ 2))) ,
       subst2 _<ᵣ_
         (cong₂ _+ᵣ_ (-ᵣ· _ _ ∙ cong -ᵣ_
          (·ᵣComm _ _ ∙ [x/₊y]·yᵣ _ _))
           refl ∙ 𝐑'.+InvL' _ _ refl)
         (cong₂ _+ᵣ_ (cong₂ _·ᵣ_ refl (cong fst (sym (invℝ₊· _ _)))) refl
           )
         (<ᵣ-+o _ _ (fst (invℝ₊ (ℚ₊→ℝ₊ 2)))
           (<ᵣ-·ᵣo _ _ (invℝ₊ 2 ₊·ᵣ invℝ₊ π-number₊) (fst φ∈)))
      , isTrans<≡ᵣ _ _ _
         (<ᵣ-+o _ _ (fst (invℝ₊ (ℚ₊→ℝ₊ 2)))
           (<ᵣ-·ᵣo _ _ (invℝ₊ (2 ₊·ᵣ π-number₊)) (snd φ∈)))
           (cong₂ _+ᵣ_ (·DistR+ _ _ _ ∙ +ᵣComm _ _) refl  ∙
            sym (+ᵣAssoc _ _ _)
             ∙
             cong₂ _+ᵣ_ ([x·yᵣ]/₊y _ _)
              (cong₂ _+ᵣ_ (·ᵣComm _ _ ∙
                cong₂ _·ᵣ_ (cong fst (invℝ₊· 2 π-number₊)) refl
                ∙ [x/₊y]·yᵣ _ _ ∙ invℝ₊-rat 2) (invℝ₊-rat 2)
                ∙ +ᵣ-rat _ _ ∙ decℚ≡ᵣ?)
             ∙ +ᵣComm _ _)
           ]/
     ,
       Σ≡Prop (λ _ → isSetℝ _ _)
       (cong₂ _,_

        ((cong cos (·DistR+ _ _ _ ∙
          cong₂ _+ᵣ_ ([x/₊y]·yᵣ _ _) (cong₂ _·ᵣ_ refl (·ᵣComm _ _)
            ∙ ·ᵣComm _ _ ∙ [x·yᵣ]/₊y _ _)) ∙ cos[x]=-cos[x+π] _)
         ∙ cong -ᵣ_ cosφ≡x ∙ -ᵣInvol _)
        ((cong sin (·DistR+ _ _ _ ∙
          cong₂ _+ᵣ_ ([x/₊y]·yᵣ _ _) (cong₂ _·ᵣ_ refl (·ᵣComm _ _)
            ∙ ·ᵣComm _ _ ∙ [x·yᵣ]/₊y _ _)) ∙ sin[x]=-sin[x+π] _)
         ∙ cong -ᵣ_ sinφ≡y ∙ -ᵣInvol _)
        ))
     (distCircle→angle (ε ₊·ᵣ (2 ₊·ᵣ π-number₊)) (-ᵣ x) (-ᵣ y)
     (cong₂ _+ᵣ_ (sym (^ⁿ-even 1 x)) (sym (^ⁿ-even 1 y))  ∙
       cong₂ _+ᵣ_ (x^²=x·x _) (x^²=x·x _) ∙ x²+y²≡1))

 isEquiv[Circle→distCircle∘CircleOverlap[ε]→Circle] : ∀ ε
     → isEquiv (Circle→distCircle ∘ CircleOverlap[ ε ]→Circle)
 isEquiv[Circle→distCircle∘CircleOverlap[ε]→Circle] ε =
   isEmbedding×isSurjection→isEquiv
   (snd (compEmbedding (Circle→distCircle , injEmbedding isSetDistCircle
      (λ {x} {y} p →
         Circle→[cos,sin]-inj x y
           (PathPΣ (cong fst p))))
           (_ , injEmbedding squash/
            (CircleOverlap→Circle-inj ε _ _)))
     , CircleOverlap→[cos,sin]-surj ε)

CircleOverlap≃distCircle : ∀ ε → CircleOverlap[ ε ] ≃ distCircle
CircleOverlap≃distCircle ε = Circle→distCircle ∘ CircleOverlap[ ε ]→Circle
  , isEquiv[Circle→distCircle∘CircleOverlap[ε]→Circle] ε
