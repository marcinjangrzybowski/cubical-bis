module Cubical.HITs.CauchyReals.Circle.Angle.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order using
  (^ⁿ-StrictMonotone; ^ⁿMonotone⁻¹-with0)
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core using (^ℤ-rat)
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Circle.Base public

private
  module 𝐑' = Rℝ

from-√½< : ∀ x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1
 → fst √½ <ᵣ absᵣ x → absᵣ (-ᵣ y) ≤ᵣ rat [ 3 / 4 ]
from-√½< x y x²+y²=1 √½<∣x∣ =
 let z : y ^ⁿ 2 ≡ 1 -ᵣ x ^ⁿ 2
     z = sym (𝐑'.plusMinus _ _)
           ∙ cong (_-ᵣ (x ^ⁿ 2)) (+ᵣComm _ _ ∙ x²+y²=1)

     zz : (fst √½) ^ⁿ 2 <ᵣ x ^ⁿ 2
     zz = isTrans<≡ᵣ _ _ _ (^ⁿ-StrictMonotone 2
           (ℕ.≤-solver 1 2)
           (<ᵣWeaken≤ᵣ _ _ (snd √½) )
           (0≤absᵣ _) √½<∣x∣)
            (sym (abs[x^²ⁿ] 1 x ∙ absᵣ^ⁿ x 2))

     1-√½²≡1/2 : 1 -ᵣ ((fst √½) ^ⁿ 2) ≡ rat [ 1 / 2 ]
     1-√½²≡1/2 =
       cong (1 +ᵣ_) (cong -ᵣ_
         (^ⁿ∘root 2 (ℚ₊→ℝ₊ ([ 1 / 2 ]₊))))
       ∙  (-ᵣ-rat₂ _ _) ∙ decℚ≡ᵣ?

     zzz : (y ^ⁿ 2) <ᵣ rat [ 1 / 2 ]
     zzz = isTrans<≡ᵣ _ _ (rat [ 1 / 2 ]) (isTrans≡<ᵣ _ _ _ z
             (<ᵣ-o+ _ _ 1 (-ᵣ<ᵣ _ _ zz)))
              1-√½²≡1/2

     1/2≤3/4² : rat [ 1 / 2 ] ≤ᵣ rat [ 3 / 4 ] ^ⁿ 2
     1/2≤3/4² =
       isTrans≤≡ᵣ _ _ _ decℚ≤ᵣ?
         (sym (cong fst (^ℤ-rat ([ 3 / 4 ] , <≤ℚ!) 2)))

     ∣y∣²≤3/4² : absᵣ y ^ⁿ 2 ≤ᵣ rat [ 3 / 4 ] ^ⁿ 2
     ∣y∣²≤3/4² =
       isTrans≡≤ᵣ _ _ _
         (sym (abs[x^²ⁿ] 1 y ∙ absᵣ^ⁿ y 2))
         (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ zzz) 1/2≤3/4²)

 in isTrans≡≤ᵣ _ _ _
    (sym (-absᵣ _))
     (^ⁿMonotone⁻¹-with0 2 (ℕ.≤-solver 1 2)
       (0≤absᵣ _) decℚ<ᵣ?
        ∣y∣²≤3/4²)
