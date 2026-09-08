module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CornerWeakening where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCorners
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.PointedCarrierMaps

-- Fix ONE common corner. This local system compares the original
-- carrierBoundaryMaps, not replacement maps factoring through the disk.
module AtCorner (n : ℕ) (v : Corner (suc n)) where

  CornerCarrier : Type
  CornerCarrier = Σ[ s ∈ Selection (suc n) ]
    HasSelectedFace (suc n) s × CompatibleCorner (suc n) s v

  space : CornerCarrier → Pointed ℓ-zero
  space (s , inhabited , compatible) = carrier∙ n v s inhabited compatible

  toBoundary : (s : CornerCarrier) → space s →∙ boundary∙ n v
  toBoundary (s , inhabited , compatible) = carrierBoundary∙ n v s inhabited compatible

  Transition : CornerCarrier → CornerCarrier → Type
  Transition s t = PointedOver (toBoundary s) (toBoundary t)

  transition-contractible : (s t : CornerCarrier) → isContr (Transition s t)
  transition-contractible (s , inhabited , compatible) t =
    pointed-over-contractible (toBoundary (s , inhabited , compatible)) (toBoundary t)
      (carrier-contractible (suc n) s inhabited)

  transition : (s t : CornerCarrier) → Transition s t
  transition s t = fst (transition-contractible s t)

  composeTransition : (s t u : CornerCarrier) → Transition t u → Transition s t → Transition s u
  composeTransition s t u = composeOver {p = toBoundary s} {q = toBoundary t} {r = toBoundary u}

  transition-identity : (s : CornerCarrier) → transition s s ≡ identityOver (toBoundary s)
  transition-identity s = snd (transition-contractible s s) (identityOver (toBoundary s))

  transition-composition : (s t u : CornerCarrier) →
    composeTransition s t u (transition t u) (transition s t) ≡ transition s u
  transition-composition s t u = sym
    (snd (transition-contractible s u) (composeTransition s t u (transition t u) (transition s t)))

  -- Comparisons themselves have contractible path spaces. Repeating
  -- isContr→isContrPath gives all higher coherences from the SAME proved
  -- invariant; no next-dimensional compatibility is assumed as input.
  comparison-contractible : (s t : CornerCarrier) (f g : Transition s t) → isContr (f ≡ g)
  comparison-contractible s t = isContr→isContrPath (transition-contractible s t)

  weaken : (s t : CornerCarrier) → fst (space s) → fst (space t)
  weaken s t = overMap {p = toBoundary s} {q = toBoundary t} (transition s t)

  weaken-boundary : (s t : CornerCarrier) (x : fst (space s)) →
    fst (toBoundary t) (weaken s t x) ≡ fst (toBoundary s) x
  weaken-boundary s t x = funExt⁻
    (overMap-commutes {p = toBoundary s} {q = toBoundary t} (transition s t)) x

-- No global corner is chosen for a sphere-valued grid. Comparing these
-- local systems for DIFFERENT corners remains a separate obligation.
