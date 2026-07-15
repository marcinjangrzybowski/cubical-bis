module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Base where

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
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core

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

one≤max-invℚ₊ : ∀ x → 1 ℚ.≤ ℚ.max (fst x) (fst (x ⁻¹₊))
one≤max-invℚ₊ x =
  ⊎.rec
    (λ 1≤x →
      ℚ.isTrans≤ 1 (fst x) (ℚ.max (fst x) (fst (x ⁻¹₊)))
        1≤x (ℚ.≤max (fst x) (fst (x ⁻¹₊))))
    (λ x<1 →
      ℚ.isTrans≤ 1 (fst (x ⁻¹₊))
        (ℚ.max (fst x) (fst (x ⁻¹₊)))
        (ℚ.invℚ₊≤invℚ₊ 1 x (ℚ.<Weaken≤ (fst x) 1 x<1))
        (ℚ.≤max' (fst x) (fst (x ⁻¹₊))))
    (ℚ.Dichotomyℚ 1 (fst x))

private
  2ℝ₊ : ℝ₊
  2ℝ₊ = fromNat 2

  2₊ : ℚ₊
  2₊ = fromNat 2

  opaque
    positiveMaxInverse : ∀ x → 0 <ᵣ x → ℝ
    positiveMaxInverse x 0<x = maxᵣ x (fst invℝ' x 0<x)

  opaque
    unfolding positiveMaxInverse maxᵣ
    positiveMaxInverse-continuous :
      IsContinuousWithPred posℙ positiveMaxInverse
    positiveMaxInverse-continuous =
      contDiagNE₂WP maxR posℙ
        (λ x _ → x)
        (λ x 0<x → fst invℝ' x 0<x)
        (AsContinuousWithPred posℙ (λ x → x) IsContinuousId)
        (snd invℝ')

opaque
 unfolding invℝ positiveMaxInverse

 1≤x-⊔-x⁻¹ : ∀ x → 1 ≤ᵣ fst (maxᵣ₊ x (invℝ₊ x))
 1≤x-⊔-x⁻¹ (x , 0<x) =
   isTrans≤≡ᵣ
     1
     (positiveMaxInverse x 0<x)
     (fst (maxᵣ₊ (x , 0<x) (invℝ₊ (x , 0<x))))
     abstractBound targetPath
   where
   rationalComparison : ∀ u (0<u : 0 <ᵣ rat u) →
     1 ≤ᵣ positiveMaxInverse (rat u) 0<u
   rationalComparison u 0<u =
     subst (1 ≤ᵣ_)
       (sym (maxᵣ-rat u (fst (u₊ ⁻¹₊)))
       ∙ cong (maxᵣ (rat u))
           (sym (invℝ'-rat u (snd u₊) 0<u)))
       (≤ℚ→≤ᵣ 1 (ℚ.max u (fst (u₊ ⁻¹₊)))
         (one≤max-invℚ₊ u₊))
     where
     u₊ : ℚ₊
     u₊ = u , <ᵣ→<ℚ 0 u 0<u

   abstractBound : 1 ≤ᵣ positiveMaxInverse x 0<x
   abstractBound =
     continuousOpenLowerComparison
       {x₀ = 0}
       {f₀ = λ _ _ → 1}
       {f₁ = positiveMaxInverse}
       (AsContinuousWithPred posℙ (λ _ → 1) (IsContinuousConst 1))
       positiveMaxInverse-continuous
       rationalComparison x 0<x

   targetPath :
     positiveMaxInverse x 0<x ≡
     fst (maxᵣ₊ (x , 0<x) (invℝ₊ (x , 0<x)))
   targetPath =
     cong (maxᵣ x)
       (sym (cong fst (invℝ₊-impl (x , 0<x))))
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
