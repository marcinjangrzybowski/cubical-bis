module Cubical.HITs.CauchyReals.Circle.Homotopy.NullHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.AbGroup
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Lifted
open import Cubical.HITs.CauchyReals.Circle.Homotopy.RealPaths
open import Cubical.HITs.CauchyReals.Circle.Homotopy.IntervalLift
open import Cubical.HITs.CauchyReals.Circle.Homotopy.FiniteLift
open import Cubical.HITs.CauchyReals.Circle.Homotopy.ClosedLift
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Overlap
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Descent
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Classification using (NullWindingIsNull)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

private
  module M = AbGroupStr (snd CircleMapAbGroup)

module _ (f : CircleMap) where
  private
    loopPath : CirclePath
    loopPath = Circle→distCircleUC ∘UC (f ∘UC injCircleUC)

    loopPath-β : ∀ t → fst loopPath t ≡ Circle→distCircle (fst f (injCircle t))
    loopPath-β t = refl

    loop : fst loopPath 0 ≡ fst loopPath 1
    loop = cong (Circle→distCircle ∘ fst f) (SQ.eq/ 0 1 (-1 , -ᵣ-rat₂ 0 1))

    period : ∀ t → fst loopPath (t +ᵣ 1) ≡ fst loopPath t
    period t = loopPath-β (t +ᵣ 1)
      ∙ cong (Circle→distCircle ∘ fst f) (SQ.eq/ (t +ᵣ 1) t (1 , ℝ!))
      ∙ sym (loopPath-β t)

  module ContractFromLift (lifted : IntervalLift loopPath 0 1)
    (end : fst (IntervalLift.path lifted) 1 ≡ 0) where

    private
      module W = ClosedLifting loopPath period lifted end
      module D = CircleDescent W.wrapped W.wrapped-periodic

      angle : UC[ CirclePremetricSpace , ℝPremetricSpace ]
      angle = D.descendUC

      angle-covers : ∀ p → fst loopPath 0 ℝS¹.+ cover (fst angle p) ≡ Circle→distCircle (fst f p)
      angle-covers p = PT.rec (isSetDistCircle _ _) compare
        (overlapRepresentative (ℚ₊→ℝ₊ ([ 1 / 2 ]₊)) p)
        where
        compare : (Σ[ r ∈ ℝ ] (r ∈ ointervalℙ 0 (1 +ᵣ rat [ 1 / 2 ])) × (injCircle r ≡ p)) →
          fst loopPath 0 ℝS¹.+ cover (fst angle p) ≡ Circle→distCircle (fst f p)
        compare (r , (rlo , rhi) , represents) =
          cong (λ v → fst loopPath 0 ℝS¹.+ cover v)
            (sym (cong D.descend represents) ∙ D.descend-β r (rlo , rhi))
          ∙ W.wrapped-covers r
            (<ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ -1 0 r decℚ<ᵣ? rlo))
            (<ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ r (1 +ᵣ rat [ 1 / 2 ]) 2 rhi
              (isTrans≡<ᵣ _ _ _ (+ᵣ-rat 1 [ 1 / 2 ]) decℚ<ᵣ?)))
          ∙ loopPath-β r ∙ cong (Circle→distCircle ∘ fst f) represents

      baseMap : CircleMap
      baseMap = constantUC (fst f (injCircle 0))
      liftedMap : CircleMap
      liftedMap = injCircleUC ∘UC angle
      sumMap : CircleMap
      sumMap = addCircleUC baseMap liftedMap

      sum-is-f : sumMap ≡ f
      sum-is-f = maps-by-image sumMap f λ p → addCircle-image baseMap liftedMap p
        ∙ cong (Circle→distCircle (fst f (injCircle 0)) ℝS¹.+_) (sym (cover-β (fst angle p)))
        ∙ cong (ℝS¹._+ cover (fst angle p)) (sym (loopPath-β 0))
        ∙ angle-covers p

      lifted-contracts : Homotopic liftedMap zeroCircleMap
      lifted-contracts = lifted-null liftedMap angle W.wrapped-bound
        (D.descend-bounded W.wrapped-bound W.wrapped-bounded) (λ _ → refl)

    contracts : Homotopic f zeroCircleMap
    contracts = subst2 Homotopic sum-is-f (M.+IdR zeroCircleMap)
      (PT.map2 (homotopy-add baseMap zeroCircleMap liftedMap zeroCircleMap)
        (constant-null (fst f (injCircle 0))) lifted-contracts)

  zero-winding-contracts : windingNumber f ≡ 0 → Homotopic f zeroCircleMap
  zero-winding-contracts zero-winding = PT.rec squash₁
    (λ (lifted , end) → ContractFromLift.contracts lifted end)
    (zeroLoopLift loopPath loop zero-winding)

nullWindingIsNull : NullWindingIsNull
nullWindingIsNull = zero-winding-contracts
