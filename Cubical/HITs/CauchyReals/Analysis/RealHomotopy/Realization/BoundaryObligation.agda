module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.BoundaryObligation where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Cubes.Base
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubeMapping

-- Local target of the missing boundary assembler, in dimension n+2.
-- Cells can be the actual UC singular cubes. A is the preceding stage;
-- lower and upper must come from its interpretations of opposite faces.
--
-- The missing path includes the other faces and their higher overlaps.
-- A realization must derive it from the prescribed side-face cells AND
-- prove the face computation laws. This module neither assumes those
-- laws nor claims that any choice of such paths realizes the source.
module BoundaryAssemblyProblem {ℓC ℓA} (n : ℕ)
  (Cells : Type ℓC) (A : Type ℓA)
  (lower upper : Cells → Cube (suc n) A) where

  MissingSideCoherence : Type (ℓ-max ℓC ℓA)
  MissingSideCoherence = (σ : Cells) →
    ∂_ {n = suc n} {A = A} (lower σ) ≡ ∂_ {n = suc n} {A = A} (upper σ)

  boundaryData : MissingSideCoherence → Cells → ∂Cube (suc (suc n)) A
  boundaryData coherence σ = lower σ , upper σ , coherence σ

  -- Once the COMPLETE boundary data exists, producing its attaching
  -- map has already been solved uniformly by CubeMapping.
  attachingMapFromCoherence : MissingSideCoherence →
    Cells → CubeBoundary (suc (suc n)) → A
  attachingMapFromCoherence coherence σ =
    invEq (boundaryMapsEquiv A (suc (suc n))) (boundaryData coherence σ)

  attachingMap-boundary : (coherence : MissingSideCoherence) (σ : Cells) →
    fst (boundaryMapsEquiv A (suc (suc n)))
      (attachingMapFromCoherence coherence σ) ≡ boundaryData coherence σ
  attachingMap-boundary coherence σ =
    secEq (boundaryMapsEquiv A (suc (suc n))) (boundaryData coherence σ)
