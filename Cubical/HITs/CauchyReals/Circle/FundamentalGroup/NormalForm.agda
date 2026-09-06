module Cubical.HITs.CauchyReals.Circle.FundamentalGroup.NormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra using (circle-image-injective)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.FiniteLift using (loopIntervalLift)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.IntervalLift using (IntervalLift)
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using (injFromNatℚ)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

integer-real : ℤ → ℝ
integer-real k = rat [ k / 1 ]

integer-closes : ∀ k → injCircle (integer-real k) ≡ basepoint
integer-closes k = SQ.eq/ (integer-real k) 0 (k , ℝ!)

-- The oriented k-fold loop, with exactly the original groupoid operation.
integerLoop : ℤ → Loop
integerLoop k = (injCircleUC ∘UC (scaleUC (integer-real k) ∘UC coordinateUC)) ,
  cong injCircle ℝ! , (cong injCircle ℝ! ∙ integer-closes k)

integerLoop-winding : ∀ k → loopWinding (integerLoop k) ≡ k
integerLoop-winding k = injFromNatℚ _ _ (inj-rat _ _ (windingLoop-lift
  (extendedLoop (integerLoop k)) (extended-closes (integerLoop k)) (fst g)
  (ℝUC→∥IsUContinuous∥ g)
  (lift-step (fst (extendedLoop (integerLoop k))) circle0 (fst g)
    (λ t → sym (cover-β (fst g t)) ∙ sym (ℝS¹.+IdL (cover (fst g t)))))
  ∙ cong₂ _-ᵣ_
    (cong (_·ᵣ integer-real k) (cong fst (clip-fixes 𝟙)))
    (cong (_·ᵣ integer-real k) (cong fst (clip-fixes 𝟘))) ∙ ℝ!))
  where
  g : RealMap
  g = scaleUC (integer-real k) ∘UC (coordinateUC ∘UC clipUC)

-- Bounded real lifts can be interpolated relative to their endpoints.
lift-homotopy : (p : Loop) (k : ℤ) (g : UC[ Interval , ℝPremetricSpace ])
  (B : ℝ₊) → (∀ t → absᵣ (fst g t) ≤ᵣ fst B) →
  fst g 𝟘 ≡ 0 → fst g 𝟙 ≡ integer-real k →
  (∀ t → injCircle (fst g t) ≡ at p t) → PathHomotopy p (integerLoop k)
lift-homotopy p k g B bound at0 at1 covers = result
  where
  open PathHomotopy
  s t : UC[ IntervalSquare , ℝPremetricSpace ]
  s = coordinateUC ∘UC productFstUC
  t = coordinateUC ∘UC productSndUC
  complement : UC[ IntervalSquare , ℝPremetricSpace ]
  complement = coordinateUC ∘UC (reverseTimeUC ∘UC productFstUC)
  interpolation : UC[ IntervalSquare , ℝPremetricSpace ]
  interpolation = addRealUC
    (boundedMultiplyUC complement (g ∘UC productSndUC) 1 B
      (λ st → interval-bound (reverseTime (fst st))) (λ st → bound (snd st)))
    (scaleUC (integer-real k) ∘UC boundedMultiplyUC s t 1 1
      (λ st → interval-bound (fst st)) (λ st → interval-bound (snd st)))

  result : PathHomotopy p (integerLoop k)
  deformation result = injCircleUC ∘UC interpolation
  at-start result u = cong injCircle ℝ! ∙ covers u
  at-end result u = cong injCircle ℝ!
  fixes-start result u = cong injCircle
    (cong (λ z → (1 -ᵣ fst u) ·ᵣ z +ᵣ (fst u ·ᵣ 0) ·ᵣ integer-real k) at0 ∙ ℝ!)
  fixes-end result u = cong injCircle
    (cong (λ z → (1 -ᵣ fst u) ·ᵣ z +ᵣ (fst u ·ᵣ 1) ·ᵣ integer-real k) at1 ∙ ℝ!)
    ∙ integer-closes k

loop-normal-form : (p : Loop) → Homotopic p (integerLoop (loopWinding p))
loop-normal-form p = PT.map normalize (loopIntervalLift (extendedLoop p) (extended-closes p))
  where
  module L = IntervalLift
  normalize : (Σ[ l ∈ IntervalLift (extendedLoop p) 0 1 ]
    fst (L.path l) 1 ≡ integer-real (loopWinding p)) → PathHomotopy p (integerLoop (loopWinding p))
  normalize (l , end) = lift-homotopy p (loopWinding p)
    (L.path l ∘UC coordinateUC) (L.bound l) (λ t → L.bounded l (fst t))
    (L.lower l 0 (≤ᵣ-refl 0)) end covers
    where
    covers : ∀ t → injCircle (fst (L.path l) (fst t)) ≡ at p t
    covers t = circle-image-injective _ _
      (sym (cover-β (fst (L.path l) (fst t)))
        ∙ sym (ℝS¹.+IdL _)
        ∙ cong (ℝS¹._+ cover (fst (L.path l) (fst t)))
            (sym (extended-start p ∙ injCircle0≡circle0))
        ∙ L.covers l (fst t)
        ∙ cong (fst (extendedLoop p))
            (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 (fst t) (snd t)))
        ∙ cong (Circle→distCircle ∘ at p) (clip-fixes t))
