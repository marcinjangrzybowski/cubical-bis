module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.PackedLoopFamilies where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝕀)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.MappingLifts
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open CategoryStructures using (_∘UC_)

-- Keep the operator successor abstract while checking it. Concrete
-- sphere metrics need not unfold when this construction is specialized.
module Packed {ℓP ℓP' ℓA ℓA' ℓB ℓB' ℓY ℓY'}
  (P : PremetricSpace ℓP ℓP')
  (A : PointedPremetricSpace ℓA ℓA')
  (B : PointedPremetricSpace ℓB ℓB')
  (Y : PointedPremetricSpace ℓY ℓY')
  (pack : UC[ fst A , fst (realΩ B) ])
  (pack-based : fst pack (snd A) ≡ snd (realΩ B))
  (h : BasedFamily P B Y) where

  private
    module LB = RealLoops (fst B) (snd B)
    module LY = RealLoops (fst Y) (snd Y)

  opaque
    family : BasedFamily P A (realΩ Y)
    family = operator , based
      where
      lifted : BasedFamily P (realΩ B) (realΩ Y)
      lifted = loopBasedFamily P B Y h

      operator : UC[ PremetricProduct P (fst A) , fst (realΩ Y) ]
      operator = fst lifted ∘UC pairUC productFstUC (pack ∘UC productSndUC)

      based : (p : fst P) → fst operator (p , snd A) ≡ snd (realΩ Y)
      based p = cong (λ a → fst (fst lifted) (p , a)) pack-based ∙ snd lifted p

  opaque
    unfolding family

    family-β : (p : fst P) (a : fst (fst A)) (t : 𝕀) →
      LY.at (fst (fst family) (p , a)) t ≡ fst (fst h) (p , LB.at (fst pack a) t)
    family-β p a t = refl
