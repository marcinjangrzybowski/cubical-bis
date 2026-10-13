module Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Domain.RightHalfPlane
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Transcendental.Logarithm.Derivative
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Base
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Continuity

-- The constructed branch has derivative 1/z at every point of the open
-- right half-plane, measured against the ambient complex coordinate fst.
rightHalfPlaneLogHasDerivative : IsComplexDerivativeAlong (RightHalfPlanePremetricSpace .snd)
  fst rightHalfPlaneLog rightHalfPlaneReciprocal
rightHalfPlaneLogHasDerivative = logarithmBranchHasDerivativeAlong (RightHalfPlanePremetricSpace .snd)
  fst rightHalfPlaneLog rightHalfPlaneReciprocal expℂ-rightHalfPlaneLog
  (λ p → inverseℂ-law' (fst p) (rightHalfPlaneNonzero p)) rightHalfPlaneLogIsContinuous
