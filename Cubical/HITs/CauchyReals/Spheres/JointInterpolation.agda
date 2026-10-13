module Cubical.HITs.CauchyReals.Spheres.JointInterpolation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
  using (Interval; 𝕀)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Cubes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.JointLoops
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.InterpolationControl
open import Cubical.HITs.CauchyReals.Spheres.NestedInterpolation
open CategoryStructures using (_∘UC_)

-- Interpolation of two supplied joint loops is jointly UC in ALL cube
-- coordinates and in interpolation time. This does not uncurry an
-- arbitrary nested loop or select moduli for an infinite family.
module JointSphereInterpolation (m : ℕ) (x : RealSphere m) where
  module H = NestedSphereInterpolation m x
  module J = JointEvaluation H.sphere∙
  private
    module C = SphereInterpolationControl m

  evaluate-related : (n : ℕ) (p q : fst (H.Space n)) → H.Rel n p q →
    (v : RealCube n) → C.Admissible (J.evaluate n p v) (J.evaluate n q v)
  evaluate-related zero p q h v = h
  evaluate-related (suc zero) p q h t = h t
  evaluate-related (suc (suc n)) p q h (t , v) =
    evaluate-related (suc n) _ _ (h t) v

  evaluate-interpolate : (n : ℕ) (t : 𝕀) (p q : fst (H.Space n))
    (h : H.Rel n p q) (v : RealCube n) →
    J.evaluate n (H.interpolate n t p q h) v ≡
    C.interpolate t (J.evaluate n p v) (J.evaluate n q v) (evaluate-related n p q h v)
  evaluate-interpolate zero t p q h v = H.interpolate-zero t p q h
  evaluate-interpolate (suc zero) t p q h v =
    H.interpolate-successor zero t p q h v ∙ H.interpolate-zero t _ _ (h v)
  evaluate-interpolate (suc (suc n)) t p q h (u , v) =
    cong (λ r → J.evaluate (suc n) r v) (H.interpolate-successor (suc n) t p q h u) ∙
    evaluate-interpolate (suc n) t _ _ (h u) v

  module Between (n : ℕ) (p q : fst (H.Space n)) (h : H.Rel n p q)
    (jp : J.Joint n p) (jq : J.Joint n q) where

    private
      paired : UC[ CubeSpace n , C.AdmissiblePairs ]
      fst paired v = (J.evaluate n p v , J.evaluate n q v) , evaluate-related n p q h v
      snd paired = PT.map
        (λ (μ , uc) → μ , isuniformlycontinuouswith (IsUniformlyContinuousWith.pres≈ uc))
        (snd (pairUC (J.evaluate n p , jp) (J.evaluate n q , jq)))

      direct : UC[ PremetricProduct Interval (CubeSpace n) , RealSphereSpace m ]
      direct = C.interpolateUC ∘UC pairUC productFstUC (paired ∘UC productSndUC)

    familyUC : UC[ PremetricProduct Interval (CubeSpace n) , RealSphereSpace m ]
    fst familyUC (t , v) = J.evaluate n (H.interpolate n t p q h) v
    snd familyUC = subst
      (λ f → isUniformlyContinuous (snd (PremetricProduct Interval (CubeSpace n))) f
        (snd (RealSphereSpace m)))
      (funExt (λ (t , v) → sym (evaluate-interpolate n t p q h v))) (snd direct)

    interpolate-joint : (t : 𝕀) → J.Joint n (H.interpolate n t p q h)
    interpolate-joint t = snd (familyUC ∘UC leftInsertionUC Interval (CubeSpace n) t)
