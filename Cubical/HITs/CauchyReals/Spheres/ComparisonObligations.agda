module Cubical.HITs.CauchyReals.Spheres.ComparisonObligations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base using (Pointed; _≃∙_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Algebra.Group.Morphisms using (GroupIso)
open import Cubical.Algebra.Group.MorphismProperties
  using (compGroupIso; GroupEquiv→GroupIso)
open import Cubical.HITs.Sn.Base using (S₊∙)
import Cubical.Homotopy.Group.Base as Synthetic
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.ComparisonObligations
open import Cubical.HITs.CauchyReals.Spheres.Base

-- No uniform inhabitant of this sufficient statement has been
-- constructed here. It expands to five representative-level obligations.
SphereComparisonObligation : (n m : ℕ) → Type (loopLevel n ℓ-zero ℓ-zero)
SphereComparisonObligation n m =
  RepresentativeComparisonData n (RealSphere∙ m) (S₊∙ m)

-- Both group indices mean homotopy degree n+1; m is sphere dimension.
sphereComparisonFromObligation : (n m : ℕ) → SphereComparisonObligation n m →
  GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))
sphereComparisonFromObligation n m =
  comparisonFromData n (RealSphere∙ m) (S₊∙ m)

-- The implication is uniform in both independent dimensions. This
-- theorem takes a solution of the obligations; it does not assert one.
sphereComparisonFromAllObligations :
  ((n m : ℕ) → SphereComparisonObligation n m) → (n m : ℕ) →
  GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))
sphereComparisonFromAllObligations solve n m =
  sphereComparisonFromObligation n m (solve n m)

-- The proposed realization route has a separate sphere-recognition
-- obligation. R is a pointed higher type, not the real sphere carrier.
-- Its representative comparison is derived from data, not assumed as
-- a group isomorphism.
sphereComparisonViaRealization : ∀ {ℓR} (n m : ℕ) (R : Pointed ℓR) →
  RepresentativeComparisonData n (RealSphere∙ m) R →
  R ≃∙ S₊∙ m →
  GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))
sphereComparisonViaRealization n m R missing sphere-recognition = compGroupIso
  (comparisonFromData n (RealSphere∙ m) R missing)
  (GroupEquiv→GroupIso (Synthetic.πIso sphere-recognition n))
