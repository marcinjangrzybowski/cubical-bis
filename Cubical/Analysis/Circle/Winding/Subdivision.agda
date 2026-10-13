module Cubical.Analysis.Circle.Winding.Subdivision where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Order.Algebra as ℚ
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.PropositionalTruncation using (squash₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing using (module OrderedCommRingTheory)
open PositiveRationals using (ℚ₊)
private module O = OrderedCommRingTheory ℚOrderedCommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Circle.Base
open import Cubical.Analysis.Circle.Winding.Angle
open import Cubical.Analysis.Circle.Winding.Dyadic public

-- The finite refinement argument follows the CauchyReals winding proof;
-- its angles and sums here belong entirely to the native Analysis reals.
module Subdivision (f : ℚ → Circle) where

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
    (∀ x y → O.abs (x ℚ.- y) ℚ.< fst δ → Near (f x) (f y)) →
    mesh n a b ℚ.< fst δ → Fine n a b
  fine-from-mesh zero a b a≤b δ close bound x y a≤x x≤b a≤y y≤b =
    close x y (ℚ.isTrans≤< _ (b ℚ.- a) _
      (interval-distance a b x y a≤x x≤b a≤y y≤b)
      (subst (ℚ._< fst δ) (ℚ.·IdR (b ℚ.- a)) bound))
  fine-from-mesh (suc n) a b a≤b δ close bound =
    fine-from-mesh n a (mid a b) (mid-left a b a≤b) δ close
      (subst (ℚ._< fst δ) (sym (mesh-left n a b)) bound) ,
    fine-from-mesh n (mid a b) b (mid-right a b a≤b) δ close
      (subst (ℚ._< fst δ) (sym (mesh-right n a b)) bound)

  fine-exists : (δ : ℚ₊) →
    (∀ x y → O.abs (x ℚ.- y) ℚ.< fst δ → Near (f x) (f y)) →
    Σ[ n ∈ ℕ ] Fine n 0 1
  fine-exists δ close = fst n ,
    fine-from-mesh (fst n) 0 1 unit-order δ close
      (subst (ℚ._< fst δ) (sym (ℚ.·IdL ([ 1 / 2 ] ℚ.^ⁿ fst n))) (snd n))
    where
    n = ℚ.1/2ⁿ<ε δ

  endpoints : ∀ a b → a ℚ.≤ b → Small a b → Near (f a) (f b)
  endpoints a b a≤b small = small a b (ℚ.isRefl≤ a) a≤b a≤b (ℚ.isRefl≤ b)

  turns : ∀ n a b → a ℚ.≤ b → Fine n a b → ℝ
  turns zero a b a≤b small =
    shortAngle (f a) (f b) (endpoints a b a≤b small)
  turns (suc n) a b a≤b fine =
    turns n a (mid a b) (mid-left a b a≤b) (fst fine) +
    turns n (mid a b) b (mid-right a b a≤b) (snd fine)

  turns-small : ∀ n a b a≤b fine → (small : Small a b) →
    turns n a b a≤b fine ≡ turns zero a b a≤b small
  turns-small zero a b a≤b fine small =
    cong (shortAngle (f a) (f b))
      (squash₁ (endpoints a b a≤b fine) (endpoints a b a≤b small))
  turns-small (suc n) a b a≤b fine small =
    cong₂ _+_
      (turns-small n a (mid a b) (mid-left a b a≤b) (fst fine)
        (small-left a b a≤b small))
      (turns-small n (mid a b) b (mid-right a b a≤b) (snd fine)
        (small-right a b a≤b small))
    ∙ shortAngle-add (f a) (f (mid a b)) (f b)
      (endpoints a (mid a b) (mid-left a b a≤b) (small-left a b a≤b small))
      (endpoints (mid a b) b (mid-right a b a≤b) (small-right a b a≤b small))
      (endpoints a b a≤b small)

  -- No modulus or subdivision is part of the resulting invariant.
  turns-unique : ∀ n m a b a≤b fine fine' →
    turns n a b a≤b fine ≡ turns m a b a≤b fine'
  turns-unique zero m a b a≤b fine fine' =
    sym (turns-small m a b a≤b fine' fine)
  turns-unique (suc n) zero a b a≤b fine fine' =
    turns-small (suc n) a b a≤b fine fine'
  turns-unique (suc n) (suc m) a b a≤b fine fine' =
    cong₂ _+_
      (turns-unique n m a (mid a b) (mid-left a b a≤b) (fst fine) (fst fine'))
      (turns-unique n m (mid a b) b (mid-right a b a≤b) (snd fine) (snd fine'))

  opaque
    turns-cover : ∀ n a b a≤b fine →
      f a +ᶜ cover (turns n a b a≤b fine) ≡ f b
    turns-cover zero a b a≤b fine = shortAngle-step (f a) (f b) (endpoints a b a≤b fine)
    turns-cover (suc n) a b a≤b fine =
      cong (f a +ᶜ_) (cover-add
        (turns n a (mid a b) (mid-left a b a≤b) (fst fine))
        (turns n (mid a b) b (mid-right a b a≤b) (snd fine)))
      ∙ circle-add-assoc (f a)
        (cover (turns n a (mid a b) (mid-left a b a≤b) (fst fine)))
        (cover (turns n (mid a b) b (mid-right a b a≤b) (snd fine)))
      ∙ cong (_+ᶜ cover (turns n (mid a b) b (mid-right a b a≤b) (snd fine)))
          (turns-cover n a (mid a b) (mid-left a b a≤b) (fst fine))
      ∙ turns-cover n (mid a b) b (mid-right a b a≤b) (snd fine)
