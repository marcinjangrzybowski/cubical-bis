module Cubical.HITs.CauchyReals.Circle.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ using ([_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.RationalsImports using (ℚ₊ ; <≤ℚ! ; [_/_]₊)
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

cartNorm² : ℝ × ℝ → ℝ
cartNorm² (x , y) = x ·ᵣ x +ᵣ y ·ᵣ y

cartDist² : ℝ × ℝ → ℝ × ℝ → ℝ
cartDist² (x , y) (x' , y') = cartNorm² (x -ᵣ x' , y -ᵣ y')

cartDis²Comm : ∀ p p' → cartDist² p p' ≡ cartDist² p' p
cartDis²Comm p p' = ℝ!

distCircle : Type
distCircle = Σ (ℝ × ℝ) λ xy → cartNorm² xy ≡ 1

distCircle≡ : ∀ {x y : distCircle}
  → (fst (fst x)) ≡ fst (fst y)
  → (snd (fst x)) ≡ snd (fst y)
  → x ≡ y
distCircle≡ x=x' y=y' =
 Σ≡Prop (λ _ → isSetℝ  _ _) (cong₂ _,_ x=x' y=y')

isSetDistCircle : isSet distCircle
isSetDistCircle =
  isSetΣ (isSet× isSetℝ isSetℝ) (isProp→isSet ∘ λ _ → isSetℝ _ _ )

√½ : ℝ₊
√½ = root 2 (ℚ₊→ℝ₊ ([ 1 / 2 ]₊))

√½<3/4 : fst √½ <ᵣ rat [ 3 / 4 ]
√½<3/4 = isTrans<≡ᵣ _ _ _
  (ₙ√-StrictMonotone {y = ℚ₊→ℝ₊ ([ 9 / 16 ] , <≤ℚ!)} 2
    decℚ<ᵣ?) (cong fst (cong (root 2)
      (ℝ₊≡ (sym (cong fst (^ℤ-rat ([ 3 / 4 ] , <≤ℚ!) 2)) ) )
     ∙ Iso.ret (nth-pow-root-iso 2)
      (ℚ₊→ℝ₊ ([ 3 / 4 ] , <≤ℚ!))))

0<x²→0<abs[x] : ∀ x → 0 <ᵣ x ^ⁿ 2 → 0 <ᵣ absᵣ x
0<x²→0<abs[x] x 0<x² =
  PT.rec (isProp<ᵣ _ _)
    (⊎.rec
      (⊥.rec ∘
        (λ ∣a∣< →
          let z = isTrans≡<ᵣ _ _ _ (abs[x^²ⁿ] 1 x ∙ absᵣ^ⁿ x 2)
                  (isTrans<≡ᵣ _ _ _ (^ⁿ-StrictMonotone 2 (ℕ.≤-solver 1 2)
                   (0≤absᵣ _) (<ᵣWeaken≤ᵣ _ _
                     (snd (root 2 ((x ^ⁿ 2) , 0<x²)))) ∣a∣<)
                      (cong fst (Iso.sec (nth-pow-root-iso 2) (_ , 0<x²))))
           in isIrrefl<ᵣ _ z))
      (idfun _))
    (Dichotomyℝ' 0 (absᵣ x) _ (snd (root 2 (_ , 0<x²))))
