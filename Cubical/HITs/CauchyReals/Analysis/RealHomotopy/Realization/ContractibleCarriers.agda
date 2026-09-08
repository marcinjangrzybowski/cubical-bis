module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.ContractibleCarriers where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Cubes.Base
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubeMapping
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.BoundaryObligation

-- Local ingredient for the finite-carrier alternative. The target A
-- here is ONE contractible carrier, not the whole synthetic sphere.
-- A global carrier assignment and compatible inclusion maps remain
-- necessary before applying this across a cubical subdivision.
module _ {ℓ} (A : Type ℓ) (contractible : isContr A) where

  boundary-contractible : (n : ℕ) → isContr (∂Cube n A)
  boundary-contractible n = isOfHLevelRespectEquiv 0
    (boundaryMapsEquiv A n) (isContrΠ (λ _ → contractible))

  -- The boundary AGREEMENT is part of this fiber. Consequently its
  -- uniqueness includes that agreement, not only the underlying map.
  extension-contractible : (n : ℕ) (b : CubeBoundary n → A) →
    isContr (Σ[ f ∈ (CubeDisk n → A) ]
      ((λ z → f (cubeBoundaryMap n z)) ≡ b))
  extension-contractible n b = isContrΣ
    (isContrΠ (λ _ → contractible))
    (λ f → isContr→isContrPath (isContrΠ (λ _ → contractible)) _ b)

  relative-cube-contractible : (n : ℕ) (b : ∂Cube n A) →
    isContr (CubeRel n A b)
  relative-cube-contractible n b =
    subst (λ c → isContr (CubeRel n A c))
      (secEq (boundaryMapsEquiv A n) b)
      (isOfHLevelRespectEquiv 0 (cubeExtensionEquiv A n boundaryMap)
        (extension-contractible n boundaryMap))
    where
    boundaryMap = invEq (boundaryMapsEquiv A n) b

  -- Opposite-face coherence is also uniquely determined inside A.
  -- This does not assert that separately chosen sphere-valued faces
  -- lift to one common contractible carrier.
  side-coherence-contractible : ∀ {ℓC} (n : ℕ) (Cells : Type ℓC)
    (lower upper : Cells → Cube (suc n) A) →
    isContr (BoundaryAssemblyProblem.MissingSideCoherence n Cells A lower upper)
  side-coherence-contractible n Cells lower upper = isContrΠ λ σ →
    isContr→isContrPath (boundary-contractible (suc n)) _ _

-- A propositional subtype cannot serve as a contractible local chart
-- around a point with noncontractible synthetic loop space. Genuine
-- synthetic cell/carrier maps therefore need not be embeddings, and
-- lifting into them carries information beyond a membership proposition.
contractible-subtype-loops : ∀ {ℓ ℓP} {A : Type ℓ}
  (P : A → Type ℓP) (propP : (a : A) → isProp (P a)) →
  isContr (Σ A P) → (a : A) → P a → isContr (a ≡ a)
contractible-subtype-loops P propP contractible a pa = refl , λ p →
  cong (cong fst)
    (isProp→isSet (isContr→isProp contractible)
      (a , pa) (a , pa) refl (Σ≡Prop propP p))
