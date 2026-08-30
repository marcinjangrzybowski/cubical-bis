module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.NaturalClosedBalls where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast.Base as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous
  as ClosedBallLifting

module L = ClosedBallLifting
module S = L.S
module SP = L.SP
module U = L.U

open PositiveRationals


-- The sequence is 1,2,3,... .  Its cofinality proof below works directly on
-- rational representatives and does not import the floor or solver modules.

naturalRadius : ℕ → ℚ₊
naturalRadius n .fst = [ pos (suc n) , 1 ]
naturalRadius n .snd = ℚ.0<pos n 1

NaturalRadiiCofinal : Type₀
NaturalRadiiCofinal = ∀ (B : ℚ₊) →
  ∃[ n ∈ ℕ ] (fst B ≤ℚ fst (naturalRadius n))

isPropNaturalRadiiCofinal : isProp NaturalRadiiCofinal
isPropNaturalRadiiCofinal = isPropΠ λ _ → squash₁

naturalRadiiCofinal : NaturalRadiiCofinal
naturalRadiiCofinal (q , 0<q) = SQ.elimProp
  {P = λ q → 0 <ℚ q →
    ∃[ n ∈ ℕ ] (q ≤ℚ fst (naturalRadius n))}
  (λ q → isPropΠ λ (_ : 0 <ℚ q) → squash₁)
  onFraction q 0<q
  where
  onFraction : (a : ℤ × ℕ₊₁) →
    0 <ℚ [ a ] →
    ∃[ n ∈ ℕ ] ([ a ] ≤ℚ fst (naturalRadius n))
  onFraction (pos m , 1+ k) _ = ∣ m , ℚ.inj integerBound ∣₁
    where
    m≤product : m ℕ.≤ (suc m ℕ.· suc k)
    m≤product = ℕ.≤-trans ℕ.≤-sucℕ
      (subst (λ z → z ℕ.≤ (suc m ℕ.· suc k))
        (ℕ.·-identityʳ (suc m))
        (ℕ.≤-k· {k = suc m} (ℕ.suc-≤-suc ℕ.zero-≤)))

    integerBound :
      pos m ℤ.· pos 1 ℤ.≤ pos (suc m) ℤ.· pos (suc k)
    integerBound = subst
      (λ z → z ℤ.≤ pos (suc m ℕ.· suc k))
      (cong pos (sym (ℕ.·-identityʳ m)))
      (ℤ.ℕ≤→pos-≤-pos m (suc m ℕ.· suc k) m≤product)
  onFraction (negsuc m , 1+ k) _ =
    ∣ zero , ℚ.inj ℤ.negsuc≤pos ∣₁

IsUniformlyContinuousOnNaturalClosedBalls : (ℚ → ℚ) → Type₀
IsUniformlyContinuousOnNaturalClosedBalls f = ∀ n →
  ∃[ μ ∈ (ℚ₊ → ℚ₊) ]
    L.IsUniformlyContinuousOnClosedBallWith f (naturalRadius n) μ

isPropIsUniformlyContinuousOnNaturalClosedBalls : ∀ f →
  isProp (IsUniformlyContinuousOnNaturalClosedBalls f)
isPropIsUniformlyContinuousOnNaturalClosedBalls f =
  isPropΠ λ _ → squash₁

private
  restrictNaturalClosedBallWith : ∀ f B n μ →
    fst B ≤ℚ fst (naturalRadius n) →
    L.IsUniformlyContinuousOnClosedBallWith f (naturalRadius n) μ →
    L.IsUniformlyContinuousOnClosedBallWith f B μ
  restrictNaturalClosedBallWith f B n μ B≤n uc
    .IsUniformlyContinuousWith.pres≈ x y ε x≈y =
    uc .IsUniformlyContinuousWith.pres≈
      (fst x , ℚ.isTrans≤ _ _ _ (snd x) B≤n)
      (fst y , ℚ.isTrans≤ _ _ _ (snd y) B≤n)
      ε x≈y


onNaturalClosedBalls→onClosedBallsWithCofinality : ∀ f →
  NaturalRadiiCofinal →
  IsUniformlyContinuousOnNaturalClosedBalls f →
  L.IsUniformlyContinuousOnClosedBalls f
onNaturalClosedBalls→onClosedBallsWithCofinality f cofinal natural B =
  PT.rec squash₁ withBound (cofinal B)
  where
  withBound :
    (Σ[ n ∈ ℕ ] (fst B ≤ℚ fst (naturalRadius n))) →
    ∃[ μ ∈ (ℚ₊ → ℚ₊) ]
      L.IsUniformlyContinuousOnClosedBallWith f B μ
  withBound (n , B≤n) = PT.map restrict (natural n)
    where
    restrict :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        L.IsUniformlyContinuousOnClosedBallWith
          f (naturalRadius n) μ) →
      Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        L.IsUniformlyContinuousOnClosedBallWith f B μ
    restrict (μ , uc) = μ ,
      restrictNaturalClosedBallWith f B n μ B≤n uc

onClosedBalls→onNaturalClosedBalls : ∀ f →
  L.IsUniformlyContinuousOnClosedBalls f →
  IsUniformlyContinuousOnNaturalClosedBalls f
onClosedBalls→onNaturalClosedBalls f closed n =
  closed (naturalRadius n)

onNaturalClosedBalls→onClosedBalls : ∀ f →
  IsUniformlyContinuousOnNaturalClosedBalls f →
  L.IsUniformlyContinuousOnClosedBalls f
onNaturalClosedBalls→onClosedBalls f =
  onNaturalClosedBalls→onClosedBallsWithCofinality f naturalRadiiCofinal

onClosedBalls≃onNaturalClosedBalls : ∀ f →
  L.IsUniformlyContinuousOnClosedBalls f ≃
    IsUniformlyContinuousOnNaturalClosedBalls f
onClosedBalls≃onNaturalClosedBalls f = propBiimpl→Equiv
  (L.isPropIsUniformlyContinuousOnClosedBalls f)
  (isPropIsUniformlyContinuousOnNaturalClosedBalls f)
  (onClosedBalls→onNaturalClosedBalls f)
  (onNaturalClosedBalls→onClosedBalls f)


-- Each natural ball could be lifted separately using the clamped global
-- construction.  Joint graph uniqueness says those values agree wherever
-- the balls overlap, so the resulting glued map is exactly this one.

liftUniformlyContinuousOnNaturalClosedBalls : (f : ℚ → ℚ) →
  IsUniformlyContinuousOnNaturalClosedBalls f →
  S.ℭ̂ₛ → S.ℭ̂ₛ
liftUniformlyContinuousOnNaturalClosedBalls f natural =
  L.liftUniformlyContinuousOnClosedBalls f
    (onNaturalClosedBalls→onClosedBalls f natural)

liftUniformlyContinuousOnNaturalClosedBalls-joint :
  ∀ f natural x →
  U.JointlyApproximableFor f x
    (liftUniformlyContinuousOnNaturalClosedBalls f natural x)
liftUniformlyContinuousOnNaturalClosedBalls-joint f natural =
  L.liftUniformlyContinuousOnClosedBalls-joint f
    (onNaturalClosedBalls→onClosedBalls f natural)

liftUniformlyContinuousOnNaturalClosedBalls-ι :
  ∀ f natural q →
  liftUniformlyContinuousOnNaturalClosedBalls f natural (S.ι q) ≡
    S.ι (f q)
liftUniformlyContinuousOnNaturalClosedBalls-ι f natural =
  L.liftUniformlyContinuousOnClosedBalls-ι f
    (onNaturalClosedBalls→onClosedBalls f natural)

liftUniformlyContinuousOnNaturalClosedBalls-ext :
  ∀ (f g : ℚ → ℚ)
    (f-natural : IsUniformlyContinuousOnNaturalClosedBalls f)
    (g-natural : IsUniformlyContinuousOnNaturalClosedBalls g) →
  (∀ q → f q ≡ g q) →
  liftUniformlyContinuousOnNaturalClosedBalls f f-natural ≡
    liftUniformlyContinuousOnNaturalClosedBalls g g-natural
liftUniformlyContinuousOnNaturalClosedBalls-ext
  f g f-natural g-natural f∼g =
  L.liftUniformlyContinuousOnClosedBalls-ext f g
    (onNaturalClosedBalls→onClosedBalls f f-natural)
    (onNaturalClosedBalls→onClosedBalls g g-natural)
    f∼g

liftUniformlyContinuousOnNaturalClosedBalls-isContinuous :
  ∀ f natural →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftUniformlyContinuousOnNaturalClosedBalls f natural)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftUniformlyContinuousOnNaturalClosedBalls-isContinuous
  f natural =
  L.liftUniformlyContinuousOnClosedBalls-isContinuous f
    (onNaturalClosedBalls→onClosedBalls f natural)


-- This is the agreement needed for gluing: once two candidate values have
-- the graph approximation property for the same input, they are equal.

jointlyApproximableOnNaturalClosedBalls-equal : ∀ f natural x y y' →
  U.JointlyApproximableFor f x y →
  U.JointlyApproximableFor f x y' →
  y ≡ y'
jointlyApproximableOnNaturalClosedBalls-equal f natural =
  L.jointlyApproximable-equal f
    (L.onClosedBalls→locallyUniformlyContinuous f
      (onNaturalClosedBalls→onClosedBalls f natural))
