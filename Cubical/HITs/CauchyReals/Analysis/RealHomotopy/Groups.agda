module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupIso)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Relation.Premetric.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base using (module Paths)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.LoopGroup
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.LoopSpace public

-- The level changes only at the first iteration, but recording it
-- recursively lets the zero-fold loop space remain definitionally X.
loopLevel : ℕ → Level → Level → Level
loopLevel zero ℓ ℓ' = ℓ
loopLevel (suc n) ℓ ℓ' = ℓ-max (loopLevel n ℓ ℓ') ℓ'

realΩ^ : ∀ {ℓ ℓ'} (n : ℕ) → PointedPremetricSpace ℓ ℓ' →
  PointedPremetricSpace (loopLevel n ℓ ℓ') ℓ'
realΩ^ zero X = X
realΩ^ (suc n) X = realΩ (realΩ^ n X)

-- As for synthetic πGr, the argument n indexes the (n+1)st group.
-- Crucially, intermediate loop spaces have NOT been quotiented.
opaque
  realπGr : ∀ {ℓ ℓ'} (n : ℕ) → PointedPremetricSpace ℓ ℓ' →
    Group (ℓ-max (loopLevel n ℓ ℓ') ℓ')
  realπGr n X = Loops.loopGroup (fst (realΩ^ n X)) (snd (realΩ^ n X))

  realπGr-loopGroup : ∀ {ℓ ℓ'} (n : ℕ) (X : PointedPremetricSpace ℓ ℓ') →
    GroupIso (Loops.loopGroup (fst (realΩ^ n X)) (snd (realΩ^ n X))) (realπGr n X)
  realπGr-loopGroup n X = idGroupIso
    {G = Loops.loopGroup (fst (realΩ^ n X)) (snd (realΩ^ n X))}

-- Degree zero is a set of real path components, not in general a group.
module Components {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Paths X using (UCPath)

  RealPathConnected : fst X → fst X → Type (ℓ-max ℓ ℓ')
  RealPathConnected x y = ∥ UCPath x y ∥₁

  realπ₀ : Type (ℓ-max ℓ ℓ')
  realπ₀ = fst X SQ./ RealPathConnected

realπ : ∀ {ℓ ℓ'} (n : ℕ) → PointedPremetricSpace ℓ ℓ' →
  Type (ℓ-max (loopLevel n ℓ ℓ') ℓ')
realπ zero (X , x) = Components.realπ₀ X
realπ (suc n) X = fst (realπGr n X)

-- Unfolding realπGr zero (X , x) gives Loops.loopGroup X x:
-- degree one uses exactly the previously constructed automorphism group.
