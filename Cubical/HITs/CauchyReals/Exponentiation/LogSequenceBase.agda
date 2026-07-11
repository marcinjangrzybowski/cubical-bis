{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.LogSequenceBase where

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

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Partition using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.CauchyReals.Exponentiation.Core

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

opaque
 unfolding invℝ

 1≤x-⊔-x⁻¹ : ∀ x → 1 ≤ᵣ fst (maxᵣ₊ x (invℝ₊ x))
 1≤x-⊔-x⁻¹ (x , 0<x) =
  subst (1 ≤ᵣ_)
    (cong (maxᵣ x)
      (cong (fst invℝ' x) (isProp<ᵣ _ _ _ 0<x)
       ∙ sym (cong fst (invℝ₊-impl (x , 0<x)))))
    (<→≤ContPos'pred {0}
      {f₀ = λ _ _ → 1}
      {f₁ = λ y 0<y → maxᵣ y (fst invℝ' y 0<y)}
      (AsContinuousWithPred _ _ (IsContinuousConst 1))
      (contDiagNE₂WP maxR _ _ _
        (AsContinuousWithPred _ _ (IsContinuousId))
          (snd invℝ'))
      (λ u 0<u →
        ⊎.rec
          (λ 1≤u →
            isTrans≤ᵣ _ _ _
              (≤ℚ→≤ᵣ 1 u 1≤u)
              (≤maxᵣ (rat u) (fst invℝ' (rat u) 0<u)))
          (λ u≤1 →
            let u₊ = ℚ<→0< u (<ᵣ→<ℚ 0 u 0<u)
                invBound : 1 ≤ᵣ fst invℝ' (rat u) 0<u
                invBound =
                  isTrans≤≡ᵣ _ _ _
                    (≤ℚ→≤ᵣ 1 (fst ((u , u₊) ⁻¹₊))
                      (ℚ.invℚ₊≤invℚ₊ 1 (u , u₊) u≤1))
                    (sym (invℝ'-rat u u₊ 0<u))
            in isTrans≤≡ᵣ _ _ _
                (isTrans≤ᵣ _ _ _ invBound
                  (≤maxᵣ (fst invℝ' (rat u) 0<u) (rat u)))
                (maxᵣComm (fst invℝ' (rat u) 0<u) (rat u)))
          (ℚ.≤cases 1 u))
      x 0<x)




Lipschitz-·R : ∀ q a → absᵣ a ≤ᵣ rat (fst q) → Lipschitz-ℝ→ℝ q (_·ᵣ a)
Lipschitz-·R q a a<q u v ε u∼v =
   invEq (∼≃abs<ε _ _ _) (
    subst2 _<ᵣ_
     (sym (·absᵣ _ _) ∙ cong absᵣ (Rℝ.·DistL- _ _ _))
     (·ᵣComm _ _ ∙ sym (rat·ᵣrat _ _))
     (isTrans≤<ᵣ _ _ _
       (≤ᵣ-o·ᵣ _ _ _ (0≤absᵣ _) a<q)
       (<ᵣ-·ᵣo _ _ (ℚ₊→ℝ₊ q) (fst (∼≃abs<ε _ _ _) u∼v))))

∃Lipschitz-·R : ∀ a → ∃[ L ∈ ℚ₊ ] Lipschitz-ℝ→ℝ L (_·ᵣ a)
∃Lipschitz-·R a =
  PT.map (λ (q , (<q , _)) →
    (q , (ℚ<→0< _ $ <ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) <q)))
      , Lipschitz-·R _ a (<ᵣWeaken≤ᵣ _ _ <q) )
   (denseℚinℝ _ _
    (isTrans≡<ᵣ _ _ _ (sym (+IdR _)) (<ᵣ-o+ 0 1 (absᵣ a) decℚ<ᵣ?)))
