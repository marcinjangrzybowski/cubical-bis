module Cubical.Analysis.Circle.Winding.Dyadic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; [_/_])
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

private
  module O = OrderedCommRingTheory ℚOrderedCommRing
  module S = OrderedCommRingStr (snd ℚOrderedCommRing)
  module R = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)
  module H = 1/2∈ℚ

unit-order : 0 ℚ.≤ 1
unit-order = O.0≤1

mid : ℚ → ℚ → ℚ
mid = H.mean

mid-left : ∀ a b → a ℚ.≤ b → a ℚ.≤ mid a b
mid-left a b a≤b = subst (ℚ._≤ mid a b) (H.meanIdem a)
  (S.·MonoR≤ (a ℚ.+ a) (a ℚ.+ b) [ 1 / 2 ] H.0≤1/2
    (ℚ.≤-o+ a b a a≤b))

mid-right : ∀ a b → a ℚ.≤ b → mid a b ℚ.≤ b
mid-right a b a≤b = subst (mid a b ℚ.≤_) (H.meanIdem b)
  (S.·MonoR≤ (a ℚ.+ b) (b ℚ.+ b) [ 1 / 2 ] H.0≤1/2
    (ℚ.≤-+o a b b a≤b))

private
  left-width : ∀ a b → mid a b ℚ.- a ≡ (b ℚ.- a) ℚ.· [ 1 / 2 ]
  left-width a b =
    cong (λ z → mid a b ℚ.- z) (sym (H.meanIdem a))
    ∙ sym (R.·DistL- (a ℚ.+ b) (a ℚ.+ a) [ 1 / 2 ])
    ∙ cong (ℚ._· [ 1 / 2 ]) (sym (R.translatedDifference a b a))

  right-width : ∀ a b → b ℚ.- mid a b ≡ (b ℚ.- a) ℚ.· [ 1 / 2 ]
  right-width a b =
    cong (ℚ._- mid a b) (sym (H.meanIdem b))
    ∙ sym (R.·DistL- (b ℚ.+ b) (a ℚ.+ b) [ 1 / 2 ])
    ∙ cong (ℚ._· [ 1 / 2 ])
      (cong (λ z → (b ℚ.+ b) ℚ.- z) (ℚ.+Comm a b)
      ∙ sym (R.translatedDifference b b a))

mesh : ℕ → ℚ → ℚ → ℚ
mesh n a b = (b ℚ.- a) ℚ.· ([ 1 / 2 ] ℚ.^ⁿ n)

mesh-left : ∀ n a b → mesh n a (mid a b) ≡ mesh (suc n) a b
mesh-left n a b = cong (ℚ._· ([ 1 / 2 ] ℚ.^ⁿ n)) (left-width a b)
  ∙ sym (ℚ.·Assoc (b ℚ.- a) [ 1 / 2 ] ([ 1 / 2 ] ℚ.^ⁿ n))

mesh-right : ∀ n a b → mesh n (mid a b) b ≡ mesh (suc n) a b
mesh-right n a b = cong (ℚ._· ([ 1 / 2 ] ℚ.^ⁿ n)) (right-width a b)
  ∙ sym (ℚ.·Assoc (b ℚ.- a) [ 1 / 2 ] ([ 1 / 2 ] ℚ.^ⁿ n))

interval-distance : ∀ a b x y → a ℚ.≤ x → x ℚ.≤ b →
  a ℚ.≤ y → y ℚ.≤ b → O.abs (x ℚ.- y) ℚ.≤ b ℚ.- a
interval-distance a b x y a≤x x≤b a≤y y≤b =
  ℚ.absFrom≤×≤ (b ℚ.- a) (x ℚ.- y)
    (subst (ℚ._≤ (x ℚ.- y))
      (cong ((ℚ.- b) ℚ.+_) (sym (R.-Idempotent a))
      ∙ R.-Dist b (ℚ.- a)) lower-bound)
    (O.+Mono≤ x b (ℚ.- y) (ℚ.- a) x≤b (O.-Flip≤ a y a≤y))
  where
  lower-bound : (ℚ.- b) ℚ.+ a ℚ.≤ x ℚ.- y
  lower-bound = subst (ℚ._≤ (x ℚ.- y)) (ℚ.+Comm a (ℚ.- b))
    (O.+Mono≤ a x (ℚ.- b) (ℚ.- y) a≤x (O.-Flip≤ y b y≤b))
