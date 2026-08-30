module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Equality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ ; zero)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Distance
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Limits
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


-- A concrete rational null sequence lets the order-theoretic formulation of
-- "arbitrarily small" interact with the sequential completion constructor.

dyadicRadius : ℕ → ℚ₊
dyadicRadius n = [ 1 / 2 ]₊ ℚ₊^ⁿ n

dyadicReal : ℕ → Real.ℝ
dyadicReal n = Real.ιℚ (fst (dyadicRadius n))

private
  half<one : fst [ 1 / 2 ]₊ ℚ.< 1
  half<one = subst (fst [ 1 / 2 ]₊ ℚ.<_)
    (/2+/2≡id 1) (<₊SumLeft [ 1 / 2 ]₊ [ 1 / 2 ]₊)

  dyadicAntitone : ∀ m n → m ℕ.≤ n →
    fst (dyadicRadius n) ℚ.≤ fst (dyadicRadius m)
  dyadicAntitone m n m≤n =
    powExponentAntitone (fst [ 1 / 2 ]₊)
      (ℚ.<Weaken≤ 0 (fst [ 1 / 2 ]₊) (snd [ 1 / 2 ]₊))
      (ℚ.<Weaken≤ (fst [ 1 / 2 ]₊) 1 half<one)
      m n m≤n

  dyadicDifferenceZero : ∀ n →
    fst (dyadicRadius n) ℚR.- 0 ≡ fst (dyadicRadius n)
  dyadicDifferenceZero n =
    cong (fst (dyadicRadius n) ℚR.+_) ℚR.0Selfinverse
    ∙ ℚR.+IdR (fst (dyadicRadius n))

  dyadic-close-zero : ∀ n ε →
    fst (dyadicRadius n) ℚ.< fst ε →
    dyadicReal n Real.Base.≈ᶜ[ ε ] Real.ιℚ 0
  dyadic-close-zero n ε small =
    Real.Base.ι-ι (fst (dyadicRadius n)) 0 ε
      (subst (ℚ._< fst ε)
        (sym
          (cong abs (dyadicDifferenceZero n) ∙
            0≤→abs≡id (fst (dyadicRadius n))
              (ℚ.<Weaken≤ 0 (fst (dyadicRadius n))
                (snd (dyadicRadius n)))))
        small)


dyadicRealIsCauchySequence : Real.Base.IsCauchySequence dyadicReal
dyadicRealIsCauchySequence ε =
  ∣ N , close ∣₁
  where
  N : ℕ
  N = fst (1/2ⁿ<ε (ε /2₊))

  N-small : fst (dyadicRadius N) ℚ.< fst (ε /2₊)
  N-small = snd (1/2ⁿ<ε (ε /2₊))

  close : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
    dyadicReal m Real.Base.≈ᶜ[ ε ] dyadicReal n
  close m n N≤m N≤n =
    subst (λ ρ → dyadicReal m Real.Base.≈ᶜ[ ρ ] dyadicReal n)
      (ℚ₊≡ (/2+/2≡id (fst ε)))
      (Real.Premetric.tri≈ᶜ (dyadicReal m) (Real.ιℚ 0) (dyadicReal n)
        (ε /2₊) (ε /2₊)
        (dyadic-close-zero m (ε /2₊)
          (ℚ.isTrans≤< _ _ _ (dyadicAntitone N m N≤m) N-small))
        (Real.Base.sym≈ᶜ (dyadicReal n) (Real.ιℚ 0) (ε /2₊)
          (dyadic-close-zero n (ε /2₊)
            (ℚ.isTrans≤< _ _ _ (dyadicAntitone N n N≤n) N-small))))


dyadicReal-limit-zero :
  Real.Base.lim dyadicReal dyadicRealIsCauchySequence ≡ Real.ιℚ 0
dyadicReal-limit-zero =
  cong fst
    (Real.Premetric.CompletionTheory.isPropLimitSeq dyadicReal
      (Real.Base.lim dyadicReal dyadicRealIsCauchySequence
        , Real.Premetric.lim-isLimitSeq dyadicReal dyadicRealIsCauchySequence)
      (Real.ιℚ 0 , zero-is-limit))
  where
  zero-is-limit : Real.Premetric.CompletionTheory.isLimitSeq dyadicReal (Real.ιℚ 0)
  zero-is-limit ε =
    ∣ N , (\ n N≤n →
      dyadic-close-zero n ε
        (ℚ.isTrans≤< _ _ _ (dyadicAntitone N n N≤n) N-small)) ∣₁
    where
    N : ℕ
    N = fst (1/2ⁿ<ε ε)

    N-small : fst (dyadicRadius N) ℚ.< fst ε
    N-small = snd (1/2ⁿ<ε ε)


ArbitrarilyClose : Real.ℝ → Real.ℝ → Type
ArbitrarilyClose x y =
  ∀ (ε : ℚ₊) → x Real.Base.≈ᶜ[ ε ] y

DistanceArbitrarilySmall : Real.ℝ → Real.ℝ → Type
DistanceArbitrarilySmall x y =
  ∀ (ε : ℚ₊) → distance x y Real.Base.≈ᶜ[ ε ] Real.ιℚ 0

OrderDistanceArbitrarilySmall : Real.ℝ → Real.ℝ → Type
OrderDistanceArbitrarilySmall x y =
  ∀ (ε : ℚ₊) → distance x y ≤ℝ Real.ιℚ (fst ε)


isPropArbitrarilyClose : ∀ x y → isProp (ArbitrarilyClose x y)
isPropArbitrarilyClose x y =
  isPropΠ λ ε → Real.Base.isProp≈ᶜ x ε y

isPropDistanceArbitrarilySmall : ∀ x y →
  isProp (DistanceArbitrarilySmall x y)
isPropDistanceArbitrarilySmall x y =
  isPropΠ λ ε → Real.Base.isProp≈ᶜ (distance x y) ε (Real.ιℚ 0)

isPropOrderDistanceArbitrarilySmall : ∀ x y →
  isProp (OrderDistanceArbitrarilySmall x y)
isPropOrderDistanceArbitrarilySmall x y =
  isPropΠ λ ε → isProp≤ℝ (distance x y) (Real.ιℚ (fst ε))


equality→arbitrarilyClose : ∀ {x y} → x ≡ y → ArbitrarilyClose x y
equality→arbitrarilyClose {x} {y} x≡y ε =
  subst (λ z → x Real.Base.≈ᶜ[ ε ] z) x≡y
    (Real.Base.isRefl≈ᶜ x ε)

arbitrarilyClose→equality : ∀ {x y} → ArbitrarilyClose x y → x ≡ y
arbitrarilyClose→equality {x} {y} = Real.Base.eqCompletion x y

equality≃arbitrarilyClose : ∀ x y →
  (x ≡ y) ≃ ArbitrarilyClose x y
equality≃arbitrarilyClose x y =
  propBiimpl→Equiv
    (Real.Base.isSetCompletion x y) (isPropArbitrarilyClose x y)
    equality→arbitrarilyClose arbitrarilyClose→equality


equality→distanceArbitrarilySmall : ∀ {x y} →
  x ≡ y → DistanceArbitrarilySmall x y
equality→distanceArbitrarilySmall {x} {y} x≡y =
  subst (DistanceArbitrarilySmall x) x≡y base
  where
  base : DistanceArbitrarilySmall x x
  base ε =
    subst (Real.Base._≈ᶜ[ ε ] Real.ιℚ 0)
      (sym (distance-refl x))
      (Real.Base.isRefl≈ᶜ (Real.ιℚ 0) ε)

distanceArbitrarilySmall→equality : ∀ {x y} →
  DistanceArbitrarilySmall x y → x ≡ y
distanceArbitrarilySmall→equality {x} {y} distanceSmall =
  distance-eq-zero→eq x y
    (Real.Base.eqCompletion (distance x y) (Real.ιℚ 0) distanceSmall)

equality≃distanceArbitrarilySmall : ∀ x y →
  (x ≡ y) ≃ DistanceArbitrarilySmall x y
equality≃distanceArbitrarilySmall x y =
  propBiimpl→Equiv
    (Real.Base.isSetCompletion x y) (isPropDistanceArbitrarilySmall x y)
    equality→distanceArbitrarilySmall
    distanceArbitrarilySmall→equality


arbitrarilyClose≃distanceArbitrarilySmall : ∀ x y →
  ArbitrarilyClose x y ≃ DistanceArbitrarilySmall x y
arbitrarilyClose≃distanceArbitrarilySmall x y =
  propBiimpl→Equiv
    (isPropArbitrarilyClose x y)
    (isPropDistanceArbitrarilySmall x y)
    (equality→distanceArbitrarilySmall ∘ arbitrarilyClose→equality)
    (equality→arbitrarilyClose ∘ distanceArbitrarilySmall→equality)


equality→orderDistanceArbitrarilySmall : ∀ {x y} →
  x ≡ y → OrderDistanceArbitrarilySmall x y
equality→orderDistanceArbitrarilySmall {x} {y} x≡y =
  subst (OrderDistanceArbitrarilySmall x) x≡y base
  where
  base : OrderDistanceArbitrarilySmall x x
  base ε =
    subst (λ z → z ≤ℝ Real.ιℚ (fst ε))
      (sym (distance-refl x))
      (≤ℚ→≤ℝ 0 (fst ε) (ℚ.<Weaken≤ 0 (fst ε) (snd ε)))


orderDistanceArbitrarilySmall→equality : ∀ {x y} →
  OrderDistanceArbitrarilySmall x y → x ≡ y
orderDistanceArbitrarilySmall→equality {x} {y} distanceSmall =
  distance-eq-zero→eq x y distance-is-zero
  where
  d : Real.ℝ
  d = distance x y

  constantWitness : Real.Base.IsCauchySequence (λ _ → d)
  constantWitness = constantIsCauchySequence d

  limits-ordered :
    Real.Base.lim (λ _ → d) constantWitness ≤ℝ
      Real.Base.lim dyadicReal dyadicRealIsCauchySequence
  limits-ordered =
    lim-preserves≤ (λ _ → d) constantWitness
      dyadicReal dyadicRealIsCauchySequence
      (λ n → distanceSmall (dyadicRadius n))

  d≤0 : d ≤ℝ Real.ιℚ 0
  d≤0 =
    subst2 _≤ℝ_
      (lim-constant d constantWitness)
      dyadicReal-limit-zero
      limits-ordered

  distance-is-zero : d ≡ Real.ιℚ 0
  distance-is-zero =
    ≤ℝ-antisym d (Real.ιℚ 0) d≤0 (zero≤abs (x Group.- y))


equality≃orderDistanceArbitrarilySmall : ∀ x y →
  (x ≡ y) ≃ OrderDistanceArbitrarilySmall x y
equality≃orderDistanceArbitrarilySmall x y =
  propBiimpl→Equiv
    (Real.Base.isSetCompletion x y)
    (isPropOrderDistanceArbitrarilySmall x y)
    (equality→orderDistanceArbitrarilySmall {x} {y})
    (orderDistanceArbitrarilySmall→equality {x} {y})


distanceArbitrarilySmall≃orderDistanceArbitrarilySmall : ∀ x y →
  DistanceArbitrarilySmall x y ≃
    OrderDistanceArbitrarilySmall x y
distanceArbitrarilySmall≃orderDistanceArbitrarilySmall x y =
  propBiimpl→Equiv
    (isPropDistanceArbitrarilySmall x y)
    (isPropOrderDistanceArbitrarilySmall x y)
    (λ small →
      equality→orderDistanceArbitrarilySmall {x} {y}
        (distanceArbitrarilySmall→equality {x} {y} small))
    (λ small →
      equality→distanceArbitrarilySmall {x} {y}
        (orderDistanceArbitrarilySmall→equality {x} {y} small))


arbitrarilyClose≃orderDistanceArbitrarilySmall : ∀ x y →
  ArbitrarilyClose x y ≃ OrderDistanceArbitrarilySmall x y
arbitrarilyClose≃orderDistanceArbitrarilySmall x y =
  propBiimpl→Equiv
    (isPropArbitrarilyClose x y)
    (isPropOrderDistanceArbitrarilySmall x y)
    (λ close →
      equality→orderDistanceArbitrarilySmall {x} {y}
        (arbitrarilyClose→equality {x} {y} close))
    (λ small →
      equality→arbitrarilyClose {x} {y}
        (orderDistanceArbitrarilySmall→equality {x} {y} small))
