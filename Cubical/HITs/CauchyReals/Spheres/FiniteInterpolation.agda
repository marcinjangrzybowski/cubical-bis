module Cubical.HITs.CauchyReals.Spheres.FiniteInterpolation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric using (ℝPremetricSpace)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Stitching
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Cubes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups using (loopLevel)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteEvaluation
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.InterpolationClocks
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Unit
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.JointInterpolation
open CategoryStructures using (_∘UC_)

-- Finite sample lists carry only actual adjacent admissibility. All
-- pasting overlap equations and jointness proofs are generated here.
module SpherePolygons (m : ℕ) (x : RealSphere m) (n : ℕ) where
  module I = JointSphereInterpolation m x
  module H = I.H
  module J = I.J
  module F = FiniteEvaluation (H.Space n) (RealSphereSpace m)
    UnitPremetricSpace (CubeSpace n) (J.evaluate n)
  module P = F.P

  branch : ℕ → (p q : fst (H.Space n)) → H.Rel n p q → P.Branch
  branch j p q h = H.interpolateUC n ∘UC
    pairUC (clockUC j ∘UC productFstUC) (constantUC ((p , q) , h))

  branch-left : (j : ℕ) (p q : fst (H.Space n)) (h : H.Rel n p q) (z : ℝ) →
    clock j z ≡ 𝟘 → fst (branch j p q h) (z , tt) ≡ p
  branch-left j p q h z at0 = cong (λ t → H.interpolate n t p q h) at0 ∙ H.at-start n p q h

  branch-right : (j : ℕ) (p q : fst (H.Space n)) (h : H.Rel n p q) (z : ℝ) →
    clock j z ≡ 𝟙 → fst (branch j p q h) (z , tt) ≡ q
  branch-right j p q h z at1 = cong (λ t → H.interpolate n t p q h) at1 ∙ H.at-end n p q h

  branch-joint : (j : ℕ) (p q : fst (H.Space n)) (h : H.Rel n p q) →
    J.Joint n p → J.Joint n q → F.JointBranch (branch j p q h)
  branch-joint j p q h jp jq = snd (I.Between.familyUC n p q h jp jq ∘UC
    pairUC (clockUC j ∘UC productFstUC) (productSndUC ∘UC productSndUC))

  Polygon : ℕ → Type (loopLevel n ℓ-zero ℓ-zero)
  endpoint : (k : ℕ) → Polygon k → fst (H.Space n)
  Polygon zero = fst (H.Pairs n)
  Polygon (suc k) = Σ[ c ∈ Polygon k ] Σ[ q ∈ fst (H.Space n) ] H.Rel n (endpoint k c) q
  endpoint zero ((p , q) , h) = q
  endpoint (suc k) (c , q , h) = q

  startpoint : (k : ℕ) → Polygon k → fst (H.Space n)
  startpoint zero ((p , q) , h) = p
  startpoint (suc k) (c , q , h) = startpoint k c

  chain : (k : ℕ) → Polygon k → P.Chain k
  last-end : (k : ℕ) (c : Polygon k) (z : ℝ) → rat (cut k) ≤ᵣ z →
    fst (P.last k (chain k c)) (z , tt) ≡ endpoint k c
  chain zero ((p , q) , h) = branch zero p q h
  chain (suc k) (c , q , h) = chain k c , branch (suc k) (endpoint k c) q h ,
    λ z _ lo hi → last-end k c z (<ᵣWeaken≤ᵣ _ _ lo) ∙
      sym (branch-left (suc k) (endpoint k c) q h z (next-clock-left k z hi))
  last-end zero ((p , q) , h) z above = branch-right zero p q h z (clock-right zero z above)
  last-end (suc k) (c , q , h) z above =
    branch-right (suc k) (endpoint k c) q h z (clock-right (suc k) z above)

  paste-at-start : (k : ℕ) (c : Polygon k) →
    fst (P.paste k (chain k c)) (rat start , tt) ≡ startpoint k c
  paste-at-start zero ((p , q) , h) = branch-left zero p q h _ clock-at-start
  paste-at-start (suc k) (c , q , h) = S.stitched-left _ tt (start-before k) ∙ paste-at-start k c
    where
    module S = Stitch (H.Space n) UnitPremetricSpace (cut k)
      (P.paste k (chain k c)) (branch (suc k) (endpoint k c) q h)
      (λ z _ lo hi → P.last-after k (chain k c) z tt lo ∙ last-end k c z (<ᵣWeaken≤ᵣ _ _ lo) ∙
        sym (branch-left (suc k) (endpoint k c) q h z (next-clock-left k z hi)))

  paste-at-finish : (k : ℕ) (c : Polygon k) →
    fst (P.paste k (chain k c)) (rat (finish k) , tt) ≡ endpoint k c
  paste-at-finish k c = P.last-after k (chain k c) (rat (finish k)) tt
    (<ℚ→<ᵣ (cut k) (finish k) <≤ℚ!) ∙
    last-end k c (rat (finish k)) (≤ℚ→≤ᵣ (cut k) (finish k) <≤ℚ!)

  JointVertices : (k : ℕ) → Polygon k → Type
  JointVertices zero ((p , q) , h) = J.Joint n p × J.Joint n q
  JointVertices (suc k) (c , q , h) = JointVertices k c × J.Joint n q

  endpoint-joint : (k : ℕ) (c : Polygon k) → JointVertices k c → J.Joint n (endpoint k c)
  endpoint-joint zero ((p , q) , h) = snd
  endpoint-joint (suc k) (c , q , h) = snd

  chain-joint : (k : ℕ) (c : Polygon k) → JointVertices k c → F.JointBranches k (chain k c)
  chain-joint zero ((p , q) , h) (jp , jq) = branch-joint zero p q h jp jq
  chain-joint (suc k) (c , q , h) (previous , jq) = chain-joint k c previous ,
    branch-joint (suc k) (endpoint k c) q h (endpoint-joint k c previous) jq

  paste-joint : (k : ℕ) (c : Polygon k) → JointVertices k c → F.JointBranch (P.paste k (chain k c))
  paste-joint k c joint = F.jointPaste k (chain k c) (chain-joint k c joint)

  pathUC : (k : ℕ) → Polygon k → UC[ Interval , H.Space n ]
  pathUC k c = P.paste k (chain k c) ∘UC pairUC (stretchUC k) (constantUC tt)

  path-start : (k : ℕ) (c : Polygon k) → fst (pathUC k c) 𝟘 ≡ startpoint k c
  path-start k c = cong (λ z → fst (P.paste k (chain k c)) (z , tt)) (stretch-start k) ∙
    paste-at-start k c

  path-finish : (k : ℕ) (c : Polygon k) → fst (pathUC k c) 𝟙 ≡ endpoint k c
  path-finish k c = cong (λ z → fst (P.paste k (chain k c)) (z , tt)) (stretch-finish k) ∙
    paste-at-finish k c

  jointPathUC : (k : ℕ) (c : Polygon k) → JointVertices k c →
    UC[ PremetricProduct Interval (CubeSpace n) , RealSphereSpace m ]
  jointPathUC k c joint = evaluated ∘UC
    pairUC (stretchUC k ∘UC productFstUC) (pairUC (constantUC tt) productSndUC)
    where
    evaluated : UC[ PremetricProduct ℝPremetricSpace
      (PremetricProduct UnitPremetricSpace (CubeSpace n)) , RealSphereSpace m ]
    fst evaluated (z , (unit , v)) = J.evaluate n (fst (P.paste k (chain k c)) (z , unit)) v
    snd evaluated = paste-joint k c joint

  loop : (k : ℕ) (c : Polygon k) → startpoint k c ≡ H.base n → endpoint k c ≡ H.base n →
    fst (H.Space (suc n))
  loop k c at0 at1 = pathUC k c , (path-start k c ∙ at0) , (path-finish k c ∙ at1)

  loop-joint : (k : ℕ) (c : Polygon k) (at0 : startpoint k c ≡ H.base n)
    (at1 : endpoint k c ≡ H.base n) → JointVertices k c → J.Joint (suc n) (loop k c at0 at1)
  loop-joint k c at0 at1 joint = J.joint-successor n (loop k c at0 at1) (snd (jointPathUC k c joint))
