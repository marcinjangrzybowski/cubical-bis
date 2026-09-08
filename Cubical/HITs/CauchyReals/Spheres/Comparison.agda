module Cubical.HITs.CauchyReals.Spheres.Comparison where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.Sn.Base using (S₊∙)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Comparison
open import Cubical.HITs.CauchyReals.Spheres.Base

-- Compare degree n+1 real homotopy of the real coordinate m-sphere with
-- degree n+1 synthetic homotopy of the library's synthetic HIT m-sphere.
-- Expose the proof obligations; no general comparison theorem is assumed.
-- The unconditional real/synthetic circle comparison lives separately in
-- RealHomotopy.CircleComparison; Spheres.Circle supplies the pointed
-- isometry from the previous real circle to the coordinate real 1-sphere.
module SphereComparison (n m : ℕ) = Comparison n (RealSphere∙ m) (S₊∙ m)
