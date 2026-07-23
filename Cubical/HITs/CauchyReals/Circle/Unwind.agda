module Cubical.HITs.CauchyReals.Circle.Unwind where

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
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
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
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Equivalence public
open import Cubical.HITs.CauchyReals.Circle.Group public
open import Cubical.HITs.CauchyReals.Circle.Chart public
open import Cubical.HITs.CauchyReals.Circle.Metric public

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

opaque
 unwindDistCirclePathStep : ∀ a b a≤b →
    (f : ClosedIntervalPremetricSpace a b .fst → distCircle)
  → (∀ x → cartDist² (fst (f (a , (≤ᵣ-refl a , a≤b)))) (fst (f x) ) <ᵣ 2)
  → Σ (fst (ClosedIntervalPremetricSpace a b) → ℝ)
    λ g → ∀ x → f x ≡ f (a , (≤ᵣ-refl a , a≤b)) ℝS¹.+
      Circle→distCircle (injCircle (g x))
 unwindDistCirclePathStep a b a≤b f fDist =
   g , g-eq

  where

  CircleRestrDomain : Type
  CircleRestrDomain =
    Σ ℝ (_∈ ointervalℙ (-ᵣ (rat [ 1 / 4 ])) (rat [ 1 / 4 ]))

  CircleRestrCodomain : Type
  CircleRestrCodomain =
    Σ (ℝ / circle-rel) λ z →
      0 <ᵣ fst (fst (equivFun Circle≃distCircle z))

  circleRestrEquiv : CircleRestrDomain ≃ CircleRestrCodomain
  circleRestrEquiv =
    (λ (x , x∈) → injCircle x , _) , isEquivInjCircleRestr

  delta : ClosedIntervalPremetricSpace a b .fst → distCircle
  delta x = f x ℝS¹.+ (ℝS¹.- f (a , ≤ᵣ-refl a , a≤b))

  rotatedPoint : (x : ClosedIntervalPremetricSpace a b .fst) →
    Σ distCircle λ z → cartDist² (fst circle0) (fst z) <ᵣ 2
  rotatedPoint x =
    Iso.fun (rotateToOrigin 2 (f (a , ≤ᵣ-refl a , a≤b)))
      (f x , fDist x)

  upperHalf : (x : ClosedIntervalPremetricSpace a b .fst) →
    0 <ᵣ fst (fst (fst (rotatedPoint x)))
  upperHalf x =
    fst (cartDist≃upperHalf (fst (rotatedPoint x))) (snd (rotatedPoint x))

  deltaPositive : (x : ClosedIntervalPremetricSpace a b .fst) →
    0 <ᵣ fst (fst (equivFun Circle≃distCircle
      (invEq Circle≃distCircle (delta x))))
  deltaPositive x =
    isTrans<≡ᵣ _ _ _ (upperHalf x)
      (cong
        {x = fst (rotatedPoint x)}
        {y = equivFun Circle≃distCircle
          (invEq Circle≃distCircle (delta x))}
        (fst ∘ fst)
        (sym (secEq Circle≃distCircle (delta x))))

  circleRestrPoint : (d : distCircle) →
    0 <ᵣ fst (fst (equivFun Circle≃distCircle
      (invEq Circle≃distCircle d))) →
    CircleRestrCodomain
  circleRestrPoint d d>0 = invEq Circle≃distCircle d , d>0

  concreteRestrPoint : ClosedIntervalPremetricSpace a b .fst →
    CircleRestrCodomain
  concreteRestrPoint x = circleRestrPoint (delta x) (deltaPositive x)

  g : fst (ClosedIntervalPremetricSpace a b) → ℝ
  g x = fst (invEq circleRestrEquiv (concreteRestrPoint x))

  concreteSecSigma : (x : ClosedIntervalPremetricSpace a b .fst) →
    equivFun circleRestrEquiv
      (invEq circleRestrEquiv (concreteRestrPoint x)) ≡
    concreteRestrPoint x
  concreteSecSigma x = secEq circleRestrEquiv (concreteRestrPoint x)

  concreteSecFst : (x : ClosedIntervalPremetricSpace a b .fst) →
    injCircle (fst (invEq circleRestrEquiv (concreteRestrPoint x))) ≡
    invEq Circle≃distCircle (delta x)
  concreteSecFst x = cong fst (concreteSecSigma x)

  concreteAdjoint : (x : ClosedIntervalPremetricSpace a b .fst) →
    Circle→distCircle
      (injCircle (fst (invEq circleRestrEquiv (concreteRestrPoint x)))) ≡
    delta x
  concreteAdjoint x =
    fst (equivAdjointEquiv Circle≃distCircle) (concreteSecFst x)

  concreteAdjointSym : (x : ClosedIntervalPremetricSpace a b .fst) →
    delta x ≡
    Circle→distCircle
      (injCircle (fst (invEq circleRestrEquiv (concreteRestrPoint x))))
  concreteAdjointSym x = sym (concreteAdjoint x)

  concreteTranslated : (x : ClosedIntervalPremetricSpace a b .fst) →
    delta x ℝS¹.+ f (a , ≤ᵣ-refl a , a≤b) ≡
    Circle→distCircle
      (injCircle (fst (invEq circleRestrEquiv (concreteRestrPoint x)))) ℝS¹.+
    f (a , ≤ᵣ-refl a , a≤b)
  concreteTranslated x =
    cong (ℝS¹._+ f (a , ≤ᵣ-refl a , a≤b)) (concreteAdjointSym x)

  g-eq : (x : ClosedIntervalPremetricSpace a b .fst) →
    f x ≡
    f (a , ≤ᵣ-refl a , a≤b) ℝS¹.+ Circle→distCircle (injCircle (g x))
  g-eq x =
      sym (ℝS¹.+IdR _)
    ∙ cong (f x ℝS¹.+_) (sym (ℝS¹.+InvL _))
    ∙ ℝS¹.+Assoc _ (ℝS¹.- f (a , ≤ᵣ-refl a , a≤b)) _
    ∙ concreteTranslated x
    ∙ ℝS¹.+Comm _ _
