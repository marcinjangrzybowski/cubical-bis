module Cubical.HITs.CauchyReals.Circle.Winding.Subdivision where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
import Cubical.HITs.CauchyReals.Foundation.Rationals as QR
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

opaque
  unit-order : (0 ℚ.≤ 1)
  unit-order = <≤ℚ!

mid : ℚ → ℚ → ℚ
mid a b = (a ℚ.+ b) ℚ.· [ 1 / 2 ]

mid-left : ∀ a b → a ℚ.≤ b → a ℚ.≤ mid a b
mid-left a b a≤b = <≤ℚ![ a≤b ]

mid-right : ∀ a b → a ℚ.≤ b → mid a b ℚ.≤ b
mid-right a b a≤b = <≤ℚ![ a≤b ]

mesh : ℕ → ℚ → ℚ → ℚ
mesh n a b = (b ℚ.- a) ℚ.· ([ 1 / 2 ] ℚ.^ⁿ n)

mesh-left : ∀ n a b → mesh n a (mid a b) ≡ mesh (suc n) a b
mesh-left n a b = algebra a b ([ 1 / 2 ] ℚ.^ⁿ n)
  where
  algebra : ∀ a b w → (mid a b ℚ.- a) ℚ.· w ≡
    (b ℚ.- a) ℚ.· ([ 1 / 2 ] ℚ.· w)
  algebra a b w = ℚ!

mesh-right : ∀ n a b → mesh n (mid a b) b ≡ mesh (suc n) a b
mesh-right n a b = algebra a b ([ 1 / 2 ] ℚ.^ⁿ n)
  where
  algebra : ∀ a b w → (b ℚ.- mid a b) ℚ.· w ≡
    (b ℚ.- a) ℚ.· ([ 1 / 2 ] ℚ.· w)
  algebra a b w = ℚ!

module Subdivision (f : ℚ → distCircle) where

  -- A leaf is small when its entire image fits in each endpoint chart.
  -- This condition makes refinement invariance a local calculation.
  Small : ℚ → ℚ → Type
  Small a b = ∀ x y → a ℚ.≤ x → x ℚ.≤ b →
    a ℚ.≤ y → y ℚ.≤ b → Near (f x) (f y)

  small-left : ∀ a b → a ℚ.≤ b → Small a b → Small a (mid a b)
  small-left a b a≤b small x y a≤x x≤m a≤y y≤m =
    small x y a≤x (ℚ.isTrans≤ _ _ _ x≤m (mid-right a b a≤b))
      a≤y (ℚ.isTrans≤ _ _ _ y≤m (mid-right a b a≤b))

  small-right : ∀ a b → a ℚ.≤ b → Small a b → Small (mid a b) b
  small-right a b a≤b small x y m≤x x≤b m≤y y≤b =
    small x y (ℚ.isTrans≤ _ _ _ (mid-left a b a≤b) m≤x) x≤b
      (ℚ.isTrans≤ _ _ _ (mid-left a b a≤b) m≤y) y≤b

  Fine : ℕ → ℚ → ℚ → Type
  Fine zero a b = Small a b
  Fine (suc n) a b = Fine n a (mid a b) × Fine n (mid a b) b

  fine-small : ∀ n a b → a ℚ.≤ b → Small a b → Fine n a b
  fine-small zero a b a≤b small = small
  fine-small (suc n) a b a≤b small =
    fine-small n a (mid a b) (mid-left a b a≤b) (small-left a b a≤b small) ,
    fine-small n (mid a b) b (mid-right a b a≤b) (small-right a b a≤b small)

  fine-from-mesh : ∀ n a b → a ℚ.≤ b → (δ : ℚ₊) →
    (∀ x y → QR.abs (x ℚ.- y) ℚ.< fst δ → Near (f x) (f y)) →
    mesh n a b ℚ.< fst δ → Fine n a b
  fine-from-mesh zero a b a≤b δ close bound x y a≤x x≤b a≤y y≤b =
    close x y (ℚ.isTrans≤< _ (b ℚ.- a) _
      (ℚ.absFrom≤×≤ (b ℚ.- a) (x ℚ.- y)
        <≤ℚ![ a≤x ][ y≤b ] <≤ℚ![ a≤y ][ x≤b ])
      (subst (ℚ._< fst δ) (ℚ.·IdR (b ℚ.- a)) bound))
  fine-from-mesh (suc n) a b a≤b δ close bound =
    fine-from-mesh n a (mid a b) (mid-left a b a≤b) δ close
      (subst (ℚ._< fst δ) (sym (mesh-left n a b)) bound) ,
    fine-from-mesh n (mid a b) b (mid-right a b a≤b) δ close
      (subst (ℚ._< fst δ) (sym (mesh-right n a b)) bound)

  fine-exists : (δ : ℚ₊) →
    (∀ x y → QR.abs (x ℚ.- y) ℚ.< fst δ → Near (f x) (f y)) →
    Σ[ n ∈ ℕ ] Fine n 0 1
  fine-exists δ close = fst n ,
    fine-from-mesh (fst n) 0 1 <≤ℚ! δ close
      (subst (ℚ._< fst δ) (sym (ℚ.·IdL _)) (snd n))
    where
    n = ℚ.1/2ⁿ<ε δ

  turns : ∀ n a b → a ℚ.≤ b → Fine n a b → ℝ
  turns zero a b a≤b small =
    shortAngle (f a) (f b) (small a b (ℚ.isRefl≤ a) a≤b a≤b (ℚ.isRefl≤ b))
  turns (suc n) a b a≤b fine =
    turns n a (mid a b) (mid-left a b a≤b) (fst fine) +ᵣ
    turns n (mid a b) b (mid-right a b a≤b) (snd fine)

  turns-small : ∀ n a b a≤b fine → (small : Small a b) →
    turns n a b a≤b fine ≡ turns zero a b a≤b small
  turns-small zero a b a≤b fine small =
    cong (shortAngle (f a) (f b)) (isProp<ᵣ _ _ _ _)
  turns-small (suc n) a b a≤b fine small =
    cong₂ _+ᵣ_
      (turns-small n a (mid a b) (mid-left a b a≤b) (fst fine)
        (small-left a b a≤b small))
      (turns-small n (mid a b) b (mid-right a b a≤b) (snd fine)
        (small-right a b a≤b small))
    ∙ shortAngle-add (f a) (f (mid a b)) (f b) _ _ _

  -- No modulus or subdivision is part of the resulting invariant.
  turns-unique : ∀ n m a b a≤b fine fine' →
    turns n a b a≤b fine ≡ turns m a b a≤b fine'
  turns-unique zero m a b a≤b fine fine' =
    sym (turns-small m a b a≤b fine' fine)
  turns-unique (suc n) zero a b a≤b fine fine' =
    turns-small (suc n) a b a≤b fine fine'
  turns-unique (suc n) (suc m) a b a≤b fine fine' =
    cong₂ _+ᵣ_
      (turns-unique n m a (mid a b) (mid-left a b a≤b) (fst fine) (fst fine'))
      (turns-unique n m (mid a b) b (mid-right a b a≤b) (snd fine) (snd fine'))

  opaque
    turns-cover : ∀ n a b a≤b fine →
      f a ℝS¹.+ cover (turns n a b a≤b fine) ≡ f b
    turns-cover zero a b a≤b fine = shortAngle-step (f a) (f b) _
    turns-cover (suc n) a b a≤b fine =
      cong (f a ℝS¹.+_) (cover-add _ _)
      ∙ ℝS¹.+Assoc _ _ _
      ∙ cong (ℝS¹._+ cover (turns n (mid a b) b (mid-right a b a≤b) (snd fine)))
          (turns-cover n a (mid a b) (mid-left a b a≤b) (fst fine))
      ∙ turns-cover n (mid a b) b (mid-right a b a≤b) (snd fine)
