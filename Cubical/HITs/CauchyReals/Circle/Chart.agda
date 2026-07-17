module Cubical.HITs.CauchyReals.Circle.Chart where

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
open import Cubical.HITs.CauchyReals.Circle.Group public

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

private
 fourℚ₊ : ℚ₊
 fourℚ₊ = 4

openHalfCircleIso : Iso
                     (Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))
                     (Σ distCircle λ ((x , _) , _) → 0 <ᵣ x)
openHalfCircleIso = w
 where
 f : ∀ x →  x ∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ]) →
      rat [ pos 0 / 1+ 0 ] <ᵣ
      cos
       (x ·ᵣ (rat [ pos 2 , (1+ 0) ]/ ·ᵣ
        (rat [ pos 2 , (1+ 0) ]/ ·ᵣ π-number/2)))
 f x x∈ = ∣x∣<π/2→0<cos[x] _
    (subst2 (λ a b →
      x ·ᵣ a
      ∈ ointervalℙ (-ᵣ b) b )
      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _) )
      ( (·ᵣAssoc _ _ _) ∙ 𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      (scale-sym-ointervalℙ (rat [ 1 / 4  ]) (4 ₊·ᵣ π-number/2₊) x x∈))

 inv∈ : ∀ x y → cartNorm² (x , y) ≡ rat [ pos 1 / 1+ 0 ]
       → 0 <ᵣ x → ∀ y∈ →  arcSin⟨⟩ y y∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4)) ∈
      ointervalℙ (-ᵣ rat [ 1 / 4 ]) (rat [ 1 / 4 ])
 inv∈ x y p 0<y y∈ =
   subst {x =
            fst π-number/2₊ ·ᵣ
            fst (invℝ₊
              ((π-number/2 , π-number/2₊ .snd) ₊·ᵣ
               (ℚ₊→ℝ₊ fourℚ₊)))}
       {y = fst (ℚ₊→ℝ₊ (invℚ₊ fourℚ₊))}
      (λ b →
      arcSin⟨⟩ y y∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4))
      ∈ ointervalℙ (-ᵣ b) b )
        (cong₂ _·ᵣ_ refl (cong fst (invℝ₊· _ _))
        ∙ ·ᵣAssoc _ _ _ ∙
          cong₂ _·ᵣ_ (x·invℝ₊[x] π-number/2₊ ) (invℝ₊-rat fourℚ₊) ∙ Rℝ.·IdL _)
         (scale-sym-ointervalℙ (fst π-number/2₊) (invℝ₊ (π-number/2₊ ₊·ᵣ 4 ))
         (arcSin⟨⟩ y y∈) (arcSin⟨⟩∈ y y∈))

 w : Iso _ _
 w .Iso.fun (t , t∈) = Circle→distCircle (injCircle t) , f t t∈
 w .Iso.inv (((x , y) , p) , 0<x) =
  arcSin⟨⟩ y y∈ ·ᵣ fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4)) ,
    inv∈ x y p 0<x y∈
  where
   y∈ : y ∈ ointervalℙ -1 1
   y∈ = subst (λ b → y ∈ ointervalℙ b 1)
     (-ᵣ-rat 1)
      (abs<→ointerval y 1
        (x²<1→∣x∣<1 _ (isTrans<≡ᵣ _ _ _
          (isTrans≡<ᵣ _ _ _
            (x^²=x·x y ∙ sym (+IdR _))
            (<ᵣ-o+ _ _ (y ·ᵣ y) (snd ((x , 0<x) ₊·ᵣ (x , 0<x))))
            )
          (+ᵣComm _ _ ∙ p))))


 w .Iso.sec (((x , y) , p) , 0<x) = Σ≡Prop (λ _ → isProp<ᵣ _ _)
   (distCircle≡ (
      cong fst (invEq (congEquiv {x = _ , f _ (inv∈ x y p 0<x _)}
       {_ , 0<x} (_ , isEquiv-₊^ⁿ 2))
       (ℝ₊≡ $ (x^²=x·x _ ∙
         cos·cos=1-sin·sin φ) ∙∙  cong (_-ᵣ_ 1)
        (cong₂ _·ᵣ_ p-sin p-sin)

        ∙ sym (cong (_-ᵣ (y ·ᵣ y))
         ( (p))) ∙  (𝐑'.plusMinus _ _)
         ∙∙ sym (x^²=x·x x) ))) p-sin)
  where
   φ = _
   p-sin : sin φ ≡ _
   p-sin = (cong sin (cong₂ _·ᵣ_ refl (
     (·ᵣAssoc _ _ _ ∙ cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)) refl)
    ∙ ·ᵣComm _ _ )
     ∙ [x/₊y]·yᵣ _ (π-number/2₊ ₊·ᵣ 4)) ∙
           sin∘arcSin⟨⟩ _ _)
 w .Iso.ret (t , t∈) =
  Σ≡Prop
      (∈-isProp (ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))

       (cong₂ _·ᵣ_ (arcSin⟨⟩∘sin _ _
        ((subst2 (λ a b →
      t ·ᵣ a
      ∈ ointervalℙ (-ᵣ b) b )
      (cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _) )
      ( (·ᵣAssoc _ _ _) ∙ 𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      (scale-sym-ointervalℙ (rat [ 1 / 4  ]) (4 ₊·ᵣ π-number/2₊) t t∈))))
        (cong (fst ∘ invℝ₊) (ℝ₊≡ {y = 2 ₊·ᵣ (2 ₊·ᵣ π-number/2₊)}
         (·ᵣComm _ _
         ∙ cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl ∙ sym (·ᵣAssoc _ _ _))))
         ∙ [x·yᵣ]/₊y _ _)


isEquivInjCircleRestr : isEquiv
 {A = (Σ _ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ])))}
 {B = Σ (ℝ / circle-rel) λ x → 0 <ᵣ (
                          fst (fst (equivFun Circle≃distCircle x)))}
  (λ (x , x∈) → injCircle x , _)
isEquivInjCircleRestr =
  isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ (x , x∈) → injCircle x , _)
    (Σ-cong-equiv-fst Circle≃distCircle)
     (isoToIsEquiv openHalfCircleIso)
