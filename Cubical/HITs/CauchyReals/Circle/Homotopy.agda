module Cubical.HITs.CauchyReals.Circle.Homotopy where

-- Winding gives an abelian group isomorphism between uniform real-parameter
-- homotopy classes of circle maps, under pointwise addition, and the integers.
open import Cubical.HITs.CauchyReals.Circle.Winding public
open import Cubical.HITs.CauchyReals.Circle.UniformGroup public using
  (addCircleUC; negCircleUC; constantUC)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base public using
  (CircleMap; CircleCylinder; UniformHomotopy; windingNumber-homotopy)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra public using
  (zeroCircleMap; CircleMapAbGroup; IntegerAbGroup; windingNumber-add; windingHom)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient public
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Integers public
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Lifted public using
  (liftedHomotopy; lifted-null; constant-null)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Small public using
  (strip-null; close-homotopic)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Classification public
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Equivalence public
