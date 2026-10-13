module Cubical.HITs.CauchyReals.Spheres.DenseRepresentatives where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.JointLoops
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.NestedNearbyHomotopy

-- A metric approximation criterion for ACTUAL real-homotopy classes.
-- Density is an explicit remaining input, not asserted for finite cubes.
module DenseSphereRepresentatives (m : ℕ) (x : RealSphere m) (n : ℕ) where
  module N = NestedNearbyLoops m x n
  open N using (classOf)

  module For {ℓP} (P : fst (N.H.Space (suc n)) → Type ℓP) where

    DenseAt : ℚ₊ → Type _
    DenseAt δ = (p : fst (N.H.Space (suc n))) →
      ∥ Σ[ q ∈ fst (N.H.Space (suc n)) ] P q × N.C.Close (suc n) δ p q ∥₁

    Represents : fst (realπGr n N.H.sphere∙) → Type _
    Represents a = ∥ Σ[ q ∈ fst (N.H.Space (suc n)) ] P q × (classOf q ≡ a) ∥₁

    from-radius : (δ : ℚ₊) →
      ((p q : fst (N.H.Space (suc n))) → N.C.Close (suc n) δ p q → classOf p ≡ classOf q) →
      DenseAt δ → (a : fst (realπGr n N.H.sphere∙)) → Represents a
    from-radius δ same dense a = subst Represents (Iso.sec transportGroup a)
      (onQuotient (Iso.inv transportGroup a))
      where
      transportGroup = fst (realπGr-loopGroup n N.H.sphere∙)

      onQuotient : (b : N.G.LoopClass) → Represents (Iso.fun transportGroup b)
      onQuotient = SQ.elimProp (λ _ → squash₁)
        (λ p → PT.map (λ (q , good , close) → q , good , sym (same p q close)) (dense p))

    -- Eliminate the merely existing radius only into the proposition
    -- of existence of a suitable representative. No global choices occur.
    from-density : ((δ : ℚ₊) → DenseAt δ) →
      (a : fst (realπGr n N.H.sphere∙)) → Represents a
    from-density dense a = PT.rec squash₁
      (λ (δ , same) → from-radius δ same (dense δ) a) N.classRadius

  -- The precise remaining absolute analytic statement. Its predicate
  -- is independently defined by joint UC of raw cube evaluation.
  module J = JointEvaluation N.H.sphere∙

  JointDensity : Type _
  JointDensity = (δ : ℚ₊) → For.DenseAt (J.Joint (suc n)) δ

  joint-representatives : JointDensity →
    (a : fst (realπGr n N.H.sphere∙)) → For.Represents (J.Joint (suc n)) a
  joint-representatives = For.from-density (J.Joint (suc n))

  -- J.asBasedCube turns each resulting witness into a based real cube.
  -- JointDensity has not been assumed as a postulate or proved here.
