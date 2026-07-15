module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Squares where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (seqΣ ; seqΣ' ; _^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using
  ( invℚ
  ; _⁻¹₊
  ; x/y<z→x<y·z
  )

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Convexity

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.CommRing.Properties as CR

module 𝐙' = RingTheory (CR.CommRing→Ring ℤCRing.ℤCommRing )

ℚ≤→<+₊ : ∀ x y (ε : ℚ₊) → x ℚ.≤ y → x ℚ.< y ℚ.+ fst ε
ℚ≤→<+₊ x y ε x≤y =
  subst (λ z → z ℚ.< y ℚ.+ fst ε) (ℚ.+IdR x)
    (ℚ.≤<Monotone+ x y 0 (fst ε) x≤y (snd ε))

private
  2ℝ₊ : ℝ₊
  2ℝ₊ = fromNat 2

  2₊ : ℚ₊
  2₊ = fromNat 2

open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Bernoulli

ℚ0≤x·ᵣx : ∀ x → 0 ℚ.≤ x ℚ.· x
ℚ0≤x·ᵣx = SQ.ElimProp.go w
  where
  w : ElimProp _
  w .ElimProp.isPropB _ = ℚ.isProp≤ _ _
  w .ElimProp.f (pos n , b) = ℚ.≤Monotone·-onNonNeg 0 [ ℤ.pos n , b ] 0 [ ℤ.pos n , b ]
    (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _)
  w .ElimProp.f (ℤ.negsuc n , b) =
    subst {x = [ ℤ.pos (suc n) , b ] ℚ.· [ ℤ.pos (suc n) , b ]}
          {y = [ ℤ.negsuc n , b ] ℚ.· [ ℤ.negsuc n , b ]}
          (0 ℚ.≤_)
          (cong (λ z → [ z / b ·₊₁ b ])
            (sym (ℤ.negsuc·negsuc n n)))
      (ℚ.≤Monotone·-onNonNeg 0 [ ℤ.pos (suc n) , b ] 0 [ ℤ.pos (suc n) , b ]
    (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _) (ℚ.0≤pos _ _))


0≤x·ᵣx : ∀ x → 0 ≤ᵣ x ·ᵣ x
0≤x·ᵣx = ≤Cont (IsContinuousConst 0) (cont₂·ᵣ _ _ IsContinuousId IsContinuousId)
  λ u → isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ _ _
    (ℚ0≤x·ᵣx u)) (rat·ᵣrat u u )
