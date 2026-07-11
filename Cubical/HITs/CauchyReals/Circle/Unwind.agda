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


open import Cubical.HITs.CauchyReals.RationalsImports using (ℚ₊ ; fromNatℚ₊)
open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative using (interpℝ)
open import Cubical.HITs.CauchyReals.Exponentiation.Core using (_₀₊+₀₊ᵣ_)
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot using (invℚ₊ ; isEquiv-₊^ⁿ)

open import Cubical.Algebra.Ring.BigOps

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
open import Cubical.HITs.CauchyReals.Metric
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigBase using
  ( sin
  ; cos
  ; sin·sin+cos·cos=1
  ; cos·cos=1-sin·sin
  ; cos0=1
  ; sin0=0
  ; cos-even
  ; sin-odd
  )
open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic using
  ( ∣x∣<π/2→0<cos[x] )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base using
  ( arcSin⟨⟩
  ; arcSin⟨⟩∈
  ; abs<→ointerval
  )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Inverse using
  ( sin∘arcSin⟨⟩
  ; arcSin⟨⟩∘sin
  )
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle
open import Cubical.HITs.CauchyReals.Circle.Equivalence public
open import Cubical.HITs.CauchyReals.Circle.Group public
open import Cubical.HITs.CauchyReals.Circle.Chart public
open import Cubical.HITs.CauchyReals.Circle.Metric public

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

opaque
 unwindDistCirclePathStep : ∀ a b a≤b →
    (f : Interval[ a , b ]MetricSpace .fst → distCircle)
  → (∀ x → cartDist² (fst (f (a , (≤ᵣ-refl a , a≤b)))) (fst (f x) ) <ᵣ 2)
  → Σ ((fst (Interval[ a , b ]MetricSpace)) → ℝ)
    λ g → ∀ x → f x ≡ f (a , (≤ᵣ-refl a , a≤b)) ℝS¹.+
      Circle→distCircle (injCircle (g x))
 unwindDistCirclePathStep a b a≤b f fDist =
   g , g-eq

  where

  g : fst Interval[ a , b ]MetricSpace → ℝ
  g x =
   let yyy = Iso.fun (rotateToOrigin 2 ((f (a , ≤ᵣ-refl a , a≤b)))) (f x , fDist x)
       yy = fst (cartDist≃upperHalf (fst yyy)) (snd yyy)
   in fst (invEq (_ , isEquivInjCircleRestr)
    (invEq Circle≃distCircle ((f x) ℝS¹.+ (ℝS¹.- f (a , ≤ᵣ-refl a , a≤b)))
     , isTrans<≡ᵣ _ _ _ yy
        (cong
          {x = (fst
         (Iso.fun (rotateToOrigin 2 (f (a , ≤ᵣ-refl a , a≤b)))
          (f x , fDist x)))}
          {y = (equivFun Circle≃distCircle
             (invEq Circle≃distCircle
              (f x ℝS¹.+ ℝS¹.- f (a , ≤ᵣ-refl a , a≤b))))}
          (fst ∘ fst)
          (sym (secEq Circle≃distCircle
               (f x ℝS¹.+ ℝS¹.- f (a , ≤ᵣ-refl a , a≤b)))))))

  g-eq : (x : Interval[ a , b ]MetricSpace .fst) →
          f x ≡
          f (a , ≤ᵣ-refl a , a≤b) ℝS¹.+ Circle→distCircle (injCircle (g x))
  g-eq x =
     ((  sym (ℝS¹.+IdR _)
       ∙ cong ((f x) ℝS¹.+_) (sym (ℝS¹.+InvL _))
       ∙ (ℝS¹.+Assoc _ (ℝS¹.- (f (a , ≤ᵣ-refl a , a≤b))) _ ))
      ∙ cong (ℝS¹._+ (f (a , ≤ᵣ-refl a , a≤b)))
         (sym (fst (equivAdjointEquiv Circle≃distCircle)
          ( cong fst (secEq (_ , isEquivInjCircleRestr)
           (invEq Circle≃distCircle ((f x) ℝS¹.+ (ℝS¹.- f (a , ≤ᵣ-refl a , a≤b))) ,
             _  ))
             ))) )
       ∙ ℝS¹.+Comm _ _
