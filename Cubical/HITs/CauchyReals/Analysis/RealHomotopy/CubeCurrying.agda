module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.CubeCurrying where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Cubes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Currying

-- Peel off one coordinate of a boundary-fixed cube. The additional
-- common slice modulus states exactly when uncurrying is jointly UC.
module BasedCubeCurrying {ℓ ℓ'} (n : ℕ)
  (X : PremetricSpace ℓ ℓ') (x : fst X) where
  private
    module B = BasedCubes X x
    module L = Paths (B.basedCubeSpace (suc n))
    module C = UniformCurrying Interval (CubeSpace (suc n)) X
    module PX = PremetricStr (snd X)

  CubeLoop : Type (ℓ-max ℓ ℓ')
  CubeLoop = L.UCPath (B.constantCube (suc n)) (B.constantCube (suc n))

  private
    cubeFamily : B.BasedCube (suc (suc n)) → UC[ Interval , B.basedCubeSpace (suc n) ]
    fst (cubeFamily c) t = C.slice (fst c) t ,
      λ v boundary → snd c (t , v) ∣ inr (inr boundary) ∣₁
    snd (cubeFamily c) = PT.map (λ (μ , h) → μ , isuniformlycontinuouswith
      (IsUniformlyContinuousWith.pres≈ h)) (snd (C.curryUC (fst c)))

  curryCubeLoop : B.BasedCube (suc (suc n)) → CubeLoop
  curryCubeLoop c = cubeFamily c ,
    B.cube-ext {n = suc n} {c = fst (cubeFamily c) 𝟘} {d = B.constantCube (suc n)}
      (λ v → snd c (𝟘 , v) ∣ inl refl ∣₁) ,
    B.cube-ext {n = suc n} {c = fst (cubeFamily c) 𝟙} {d = B.constantCube (suc n)}
      (λ v → snd c (𝟙 , v) ∣ inr (inl refl) ∣₁)

  sliceFamily : CubeLoop → UC[ Interval , C.MappingSpace ]
  fst (sliceFamily p) t = fst (L.at p t)
  snd (sliceFamily p) = PT.map (λ (μ , h) → μ , isuniformlycontinuouswith
    (IsUniformlyContinuousWith.pres≈ h)) (snd (fst p))

  EquiuniformCubeLoop : CubeLoop → Type ℓ'
  EquiuniformCubeLoop p = C.EquiuniformSlices (sliceFamily p)

  curryCube-equiuniform : (c : B.BasedCube (suc (suc n))) →
    EquiuniformCubeLoop (curryCubeLoop c)
  curryCube-equiuniform c = C.curry-equiuniform (fst c)

  uncurryCubeLoop : (p : CubeLoop) → EquiuniformCubeLoop p → B.BasedCube (suc (suc n))
  fst (uncurryCubeLoop p equi) = C.uncurryUC (sliceFamily p) equi
  snd (uncurryCubeLoop p equi) (t , v) = PT.rec (PX.isSetM _ _)
    (λ { (inl at0) →
           cong (λ s → B.atCube {n = suc n} (L.at p s) v) at0 ∙
           cong (λ c → B.atCube {n = suc n} c v) (fst (snd p))
       ; (inr (inl at1)) →
           cong (λ s → B.atCube {n = suc n} (L.at p s) v) at1 ∙
           cong (λ c → B.atCube {n = suc n} c v) (snd (snd p))
       ; (inr (inr boundary)) → snd (L.at p t) v boundary })

  basedCubeCurryingIso : Iso (B.BasedCube (suc (suc n)))
    (Σ[ p ∈ CubeLoop ] EquiuniformCubeLoop p)
  Iso.fun basedCubeCurryingIso c = curryCubeLoop c , curryCube-equiuniform c
  Iso.inv basedCubeCurryingIso (p , equi) = uncurryCubeLoop p equi
  Iso.sec basedCubeCurryingIso (p , equi) = Σ≡Prop (λ _ → squash₁)
    (L.path-ext {p = curryCubeLoop (uncurryCubeLoop p equi)} {q = p}
      (λ t → B.cube-ext {n = suc n}
        {c = L.at (curryCubeLoop (uncurryCubeLoop p equi)) t} {d = L.at p t}
        (λ v → refl)))
  Iso.ret basedCubeCurryingIso c = B.cube-ext {n = suc (suc n)}
    {c = uncurryCubeLoop (curryCubeLoop c) (curryCube-equiuniform c)} {d = c}
    (λ v → refl)
