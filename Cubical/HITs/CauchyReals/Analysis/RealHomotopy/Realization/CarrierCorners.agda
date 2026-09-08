module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCorners where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers

Corner : ℕ → Type
Corner zero = Unit
Corner (suc n) = Bool × Corner n

diskCorner : (n : ℕ) → Corner n → CubeDisk n
diskCorner zero _ = tt
diskCorner (suc n) (b , v) = endpoints b , diskCorner n v

boundaryCorner : (n : ℕ) → Corner (suc n) → CubeBoundary (suc n)
boundaryCorner n (b , v) = inl (b , diskCorner n v)

-- All selected signed faces contain this corner.
CompatibleCorner : (n : ℕ) → Selection n → Corner n → Type
CompatibleCorner zero _ _ = Unit
CompatibleCorner (suc n) (a , s) (b , v) =
  ((e : Endpoint a) → endpointLabel a e ≡ b) × CompatibleCorner n s v

carrierCorner : (n : ℕ) (s : Selection n) → HasSelectedFace n s →
  Corner n → Carrier n s
carrierCorner zero s = rec
carrierCorner (suc n) (choose b , s) inhabited (c , v) = inl (tt , diskCorner n v)
carrierCorner (suc n) (omit , s) inhabited (c , v) =
  inr (endpoints c , carrierCorner n s inhabited v)

-- This is an equality in the BOUNDARY, not just after mapping into the
-- contractible disk. Its omit case uses the boundary's actual push path.
carrierCorner-boundary : (n : ℕ) (s : Selection (suc n))
  (inhabited : HasSelectedFace (suc n) s) (v : Corner (suc n)) →
  CompatibleCorner (suc n) s v →
  carrierBoundaryMap (suc n) s (carrierCorner (suc n) s inhabited v) ≡ boundaryCorner n v
carrierCorner-boundary n (choose b , s) inhabited (c , v) compatible =
  cong (λ b → inl (b , diskCorner n v)) (fst compatible tt)
carrierCorner-boundary zero (omit , s) () v compatible
carrierCorner-boundary (suc n) (omit , s) inhabited (c , v) compatible =
  cong {B = λ _ → CubeBoundary (suc (suc n))}
    (λ z → inr (endpoints c , z))
    (carrierCorner-boundary n s inhabited v (snd compatible)) ∙
  sym (push (c , boundaryCorner n v))

module _ (n : ℕ) (v : Corner (suc n)) where
  boundary∙ : Pointed ℓ-zero
  boundary∙ = CubeBoundary (suc n) , boundaryCorner n v

  module _ (s : Selection (suc n)) (inhabited : HasSelectedFace (suc n) s)
    (compatible : CompatibleCorner (suc n) s v) where

    carrier∙ : Pointed ℓ-zero
    carrier∙ = Carrier (suc n) s , carrierCorner (suc n) s inhabited v

    carrierBoundary∙ : carrier∙ →∙ boundary∙
    carrierBoundary∙ = carrierBoundaryMap (suc n) s ,
      carrierCorner-boundary n s inhabited v compatible
