module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Cubes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Unit
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real using (constantUC)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open CategoryStructures using (UC≡)

CubeSpace : ℕ → PremetricSpace ℓ-zero ℓ-zero
CubeSpace zero = UnitPremetricSpace
CubeSpace (suc zero) = Interval
CubeSpace (suc (suc n)) = PremetricProduct Interval (CubeSpace (suc n))

RealCube : ℕ → Type
RealCube n = fst (CubeSpace n)

-- A point is on the boundary if at least one coordinate is an endpoint.
-- Truncation makes this a predicate even where several faces meet.
OnBoundary : (n : ℕ) → RealCube n → Type
OnBoundary zero _ = ⊥
OnBoundary (suc zero) t = ∥ (t ≡ 𝟘) ⊎ (t ≡ 𝟙) ∥₁
OnBoundary (suc (suc n)) (t , ts) =
  ∥ (t ≡ 𝟘) ⊎ ((t ≡ 𝟙) ⊎ OnBoundary (suc n) ts) ∥₁

isPropOnBoundary : (n : ℕ) (v : RealCube n) → isProp (OnBoundary n v)
isPropOnBoundary zero _ = isProp⊥
isPropOnBoundary (suc zero) _ = squash₁
isPropOnBoundary (suc (suc n)) _ = squash₁

CubeBoundarySpace : ℕ → PremetricSpace ℓ-zero ℓ-zero
CubeBoundarySpace n = PremetricSubspace (CubeSpace n)
  (λ v → OnBoundary n v , isPropOnBoundary n v)

module BasedCubes {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') (x : fst X) where
  private
    module PX = PremetricStr (snd X)

  BasedCube : ℕ → Type (ℓ-max ℓ ℓ')
  BasedCube n = Σ[ f ∈ UC[ CubeSpace n , X ] ]
    ((v : RealCube n) → OnBoundary n v → fst f v ≡ x)

  atCube : ∀ {n} → BasedCube n → RealCube n → fst X
  atCube c = fst (fst c)

  cube-ext : ∀ {n} {c d : BasedCube n} →
    (∀ v → atCube {n = n} c v ≡ atCube {n = n} d v) → c ≡ d
  cube-ext same = Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → PX.isSetM _ _)) (UC≡ (funExt same))

  isSetBasedCube : (n : ℕ) → isSet (BasedCube n)
  isSetBasedCube n = isSetΣSndProp
    (isSetΣSndProp (isSet→ PX.isSetM) (λ _ → squash₁))
    (λ _ → isPropΠ2 (λ _ _ → PX.isSetM _ _))

  basedCubeSpace : ℕ → PremetricSpace (ℓ-max ℓ ℓ') ℓ'
  basedCubeSpace n = SubspaceAlongInjection.injectionPremetricSpace
    (→PremetricSpace (RealCube n) X) (isSetBasedCube n) (λ (c : BasedCube n) → atCube {n = n} c)
    (λ c d same → cube-ext {n = n} {c = c} {d = d} (funExt⁻ same))

  constantCube : (n : ℕ) → BasedCube n
  constantCube n = constantUC x , λ _ _ → refl

  -- The one-cube construction recovers the earlier based real paths.
  private
    module P = Paths X

  intervalCubeIsoLoop : Iso (BasedCube (suc zero)) (P.UCPath x x)
  Iso.fun intervalCubeIsoLoop c = fst c ,
    snd c 𝟘 ∣ inl refl ∣₁ , snd c 𝟙 ∣ inr refl ∣₁
  Iso.inv intervalCubeIsoLoop p = fst p , λ t → PT.rec (PX.isSetM _ _)
    (λ { (inl at0) → cong (P.at p) at0 ∙ fst (snd p)
       ; (inr at1) → cong (P.at p) at1 ∙ snd (snd p) })
  Iso.sec intervalCubeIsoLoop p = P.path-ext {p = Iso.fun intervalCubeIsoLoop
    (Iso.inv intervalCubeIsoLoop p)} {q = p} (λ _ → refl)
  Iso.ret intervalCubeIsoLoop c = cube-ext {n = suc zero} {c = Iso.inv intervalCubeIsoLoop
    (Iso.fun intervalCubeIsoLoop c)} {d = c} (λ _ → refl)
