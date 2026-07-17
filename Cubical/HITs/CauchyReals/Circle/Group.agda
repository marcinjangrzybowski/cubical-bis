module Cubical.HITs.CauchyReals.Circle.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_;_choose_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_ ; ^ⁿ-even)


open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; fromNatℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds using (abs<→ointerval)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base using (interpℝ)
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base using (invℚ₊ ; isEquiv-₊^ⁿ)

open import Cubical.Algebra.Ring.BigOps

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.PNorm
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  ( sin
  ; cos
  ; sin·sin+cos·cos=1
  ; cos·cos=1-sin·sin
  ; cos0=1
  ; sin0=0
  ; cos-even
  ; sin-odd
  )
open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic using
  ( ∣x∣<π/2→0<cos[x] )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base using
  ( arcSin⟨⟩
  ; arcSin⟨⟩∈
  )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Inverse using
  ( sin∘arcSin⟨⟩
  ; arcSin⟨⟩∘sin
  )
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Equivalence public

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

fromWeldedInterval : ∀ {ℓ} (A : Type ℓ) → Type ℓ
fromWeldedInterval A =
 Σ (∀ x → x ∈ intervalℙ 0 1 → A)
   λ f → f 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ f 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)

circle0 : distCircle
circle0  = (1 , 0) ,
  cong₂ _+ᵣ_ (sym (rat·ᵣrat _ _)) (sym (rat·ᵣrat _ _))
                                    ∙ +ᵣ-rat _ _


opaque

 injCircle0≡circle0 : Circle→distCircle (injCircle 0) ≡ circle0
 injCircle0≡circle0 = distCircle≡
   (cong cos (𝐑'.0LeftAnnihilates _) ∙ cos0=1)
   (cong sin (𝐑'.0LeftAnnihilates _) ∙ sin0=0)

 circle+ : distCircle → distCircle → distCircle
 circle+ ((a , b) , p) ((c , d) , q) =
   ((a ·ᵣ c -ᵣ b ·ᵣ d) , a ·ᵣ d +ᵣ b ·ᵣ c) ,
     ℝ!
       ∙ cong₂ _·ᵣ_
       (p)
       (q) ∙ sym (rat·ᵣrat 1 1)

 circle+-X : ∀ x y →
  fst (fst (circle+ x y))
   ≡ (x .fst .fst ·ᵣ y .fst .fst -ᵣ x .fst .snd ·ᵣ y .fst .snd)
 circle+-X x y = refl

 circle+-Y : ∀ x y →
  snd (fst (circle+ x y))
   ≡ (x .fst .fst ·ᵣ y .fst .snd +ᵣ x .fst .snd ·ᵣ y .fst .fst)
 circle+-Y x y = refl

 circleNeg : distCircle → distCircle
 circleNeg ((x , y) , p) =
  (x , -ᵣ y) , cong₂ _+ᵣ_ refl (-ᵣ·-ᵣ _ _) ∙ p

ℝS¹AbGroupStr : AbGroupStr distCircle
ℝS¹AbGroupStr .AbGroupStr.0g = circle0
ℝS¹AbGroupStr .AbGroupStr._+_  = circle+
ℝS¹AbGroupStr .AbGroupStr.-_  = circleNeg
ℝS¹AbGroupStr .AbGroupStr.isAbGroup = IsAbGroupℝS¹
  where
  opaque
   unfolding circle+ circleNeg
   IsAbGroupℝS¹ : IsAbGroup
     circle0
     circle+
     circleNeg
   IsAbGroupℝS¹ =
      makeIsAbGroup isSetDistCircle
      (λ _ _ _ → distCircle≡ ℝ! ℝ!)
      (λ _ → distCircle≡ (cong₂ _+ᵣ_ (·IdR _) (cong -ᵣ_ (𝐑'.0RightAnnihilates _))
          ∙ 𝐑'.+IdR' _ _ (-ᵣ-rat 0))
        (cong₂ _+ᵣ_ (𝐑'.0RightAnnihilates _ ) (·IdR _)
          ∙ +IdL _))
      (λ (_ , p) → distCircle≡ (ℝ! ∙ p) ℝ!)
      λ _ _ → distCircle≡ ℝ! ℝ!


ℝS¹AbGroup : AbGroup ℓ-zero
ℝS¹AbGroup = _ , ℝS¹AbGroupStr


interpℝ0 : ∀ a b → interpℝ a b 0 ≡ a
interpℝ0 a b = ℝ!

interpℝ1 : ∀ a b → interpℝ a b 1 ≡ b
interpℝ1 a b = cong₂ _+ᵣ_ refl (Rℝ.·IdL _) ∙ ℝ!

pathFromToCircle∃ : (x₀ x₁ : Circle) →
              ∃[ p ∈ (∀ x → x ∈ intervalℙ 0 1 → Circle) ]
                (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₀)
                 × (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ x₁)
pathFromToCircle∃ = SQ.ElimProp2.go w
 where
 w : ElimProp2 _
 w .ElimProp2.isPropB _ _ = squash₁
 w .ElimProp2.f x y = ∣ (λ t _ → injCircle (interpℝ x y t)) ,
   cong injCircle (interpℝ0 x y) , cong injCircle (interpℝ1 x y) ∣₁


module ℝS¹ where
 open AbGroupStr ℝS¹AbGroupStr public
 open GroupTheory (AbGroup→Group ℝS¹AbGroup) public


rotationIso : distCircle → Iso distCircle distCircle
rotationIso x .Iso.fun = ℝS¹._+ x
rotationIso x .Iso.inv = ℝS¹._- x
rotationIso x .Iso.sec a =
  sym (ℝS¹.+Assoc _ _ _) ∙ cong (a ℝS¹.+_) (ℝS¹.+InvL _) ∙ ℝS¹.+IdR _
rotationIso x .Iso.ret a =
  sym (ℝS¹.+Assoc _ _ _) ∙ cong (a ℝS¹.+_) (ℝS¹.+InvR _) ∙ ℝS¹.+IdR _

rotationEquiv : distCircle → distCircle ≃ distCircle
rotationEquiv x = isoToEquiv (rotationIso x)

opaque
 unfolding circle+ circleNeg
 rotationEquivPresDist : ∀ x y z →
    cartDist² (fst x) (fst y) ≡ cartDist² (fst (x ℝS¹.+ z)) (fst (y ℝS¹.+ z))
 rotationEquivPresDist x y z =
    sym (𝐑'.·IdR' _ _ (snd z)) ∙ ℝ!


fromInterval→ℝ-uC : Type
fromInterval→ℝ-uC = Σ _ (IsUContinuousℙ (intervalℙ 0 1))


rotateToOrigin : ∀ D (x : distCircle) → Iso
       (Σ distCircle λ x' → cartDist² (fst x) (fst x') <ᵣ D)
       (Σ distCircle λ x' → cartDist² (fst circle0) (fst x') <ᵣ D)
rotateToOrigin D x@((X , Y) , _) = w
 where


 w : Iso (Σ distCircle (λ x' → cartDist² (fst x) (fst x') <ᵣ D))
         (Σ distCircle (λ x' → cartDist² (fst circle0) (fst x') <ᵣ D))
 w .Iso.fun (p@((X' , Y') , _) , d) = p ℝS¹.- x ,
  isTrans≡<ᵣ _ _ _ (cong₂ cartDist² (cong fst (sym (ℝS¹.+InvR x)) ) refl
    ∙ sym (rotationEquivPresDist x p (ℝS¹.- x))) d

 w .Iso.inv (p@((X' , Y') , _) , d) = p ℝS¹.+ x ,
   isTrans≡<ᵣ _ _ _ ((cong₂ cartDist² (cong fst (sym (ℝS¹.+IdL _)) ) refl
    ∙ sym (rotationEquivPresDist circle0 p x))) d
 w .Iso.sec _ = Σ≡Prop (λ _ → isProp<ᵣ _ _)
                 (sym (ℝS¹.+Assoc _ x (ℝS¹.- x))
                   ∙ cong (_ ℝS¹.+_) (ℝS¹.+InvR _) ∙ ℝS¹.+IdR _)
 w .Iso.ret _ = Σ≡Prop (λ _ → isProp<ᵣ _ _)
                 (sym (ℝS¹.+Assoc _ (ℝS¹.- x) x)
                   ∙ cong (_ ℝS¹.+_) (ℝS¹.+InvL _) ∙ ℝS¹.+IdR _)
