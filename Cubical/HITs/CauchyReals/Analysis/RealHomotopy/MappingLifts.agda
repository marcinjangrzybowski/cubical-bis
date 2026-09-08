module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.MappingLifts where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real using (constantUC)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝕀)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open CategoryStructures using (_∘UC_; UC≡)

-- A single parameterized operator lifts to the rounded uniform mapping
-- premetric. No common modulus for all input maps is assumed or chosen.
module _ {ℓA ℓA' ℓP ℓP' ℓM ℓM' ℓN ℓN'}
  (A : PremetricSpace ℓA ℓA') (P : PremetricSpace ℓP ℓP')
  (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') where

  liftFamilyUC : UC[ PremetricProduct P M , N ] →
    UC[ PremetricProduct P (MappingSpaces.UC[ A , M ]PrSpace)
      , MappingSpaces.UC[ A , N ]PrSpace ]
  fst (liftFamilyUC h) (p , f) = h ∘UC pairUC (constantUC p) f
  snd (liftFamilyUC h) = PT.map (λ (μ , uc) → (λ ε → μ (ε /2₊)) ,
    isuniformlycontinuouswith (λ (p , f) (q , g) ε (pq , fg) →
      ∣ (ε /2₊ , /2₊<id ε , λ a →
        IsUniformlyContinuousWith.pres≈ uc
          (p , fst f a) (q , fst g a) (ε /2₊)
          (pq , ≈→→pointwise (fst A) M (fst f) (fst g) (μ (ε /2₊)) fg a)) ∣₁)) (snd h)

  liftFamily-β : (h : UC[ PremetricProduct P M , N ])
    (p : fst P) (f : UC[ A , M ]) (a : fst A) →
    fst (fst (liftFamilyUC h) (p , f)) a ≡ fst h (p , fst f a)
  liftFamily-β h p f a = refl

-- The basepoint law is retained together with the operator. This is the
-- fixed invariant used at EVERY successor, rather than new laws at each
-- loop depth.
module _ {ℓP ℓP' ℓM ℓM' ℓN ℓN'}
  (P : PremetricSpace ℓP ℓP')
  (X : PointedPremetricSpace ℓM ℓM')
  (Y : PointedPremetricSpace ℓN ℓN') where

  BasedFamily : Type _
  BasedFamily = Σ[ h ∈ UC[ PremetricProduct P (fst X) , fst Y ] ]
    ((p : fst P) → fst h (p , snd X) ≡ snd Y)

module _ {ℓP ℓP' ℓM ℓM' ℓN ℓN'}
  (P : PremetricSpace ℓP ℓP')
  (X : PointedPremetricSpace ℓM ℓM')
  (Y : PointedPremetricSpace ℓN ℓN')
  (h : UC[ PremetricProduct P (fst X) , fst Y ])
  (based : (p : fst P) → fst h (p , snd X) ≡ snd Y) where
  private
    module LX = RealLoops (fst X) (snd X)
    module LY = RealLoops (fst Y) (snd Y)

  loopFamilyUC : UC[ PremetricProduct P (fst (realΩ X)) , fst (realΩ Y) ]
  fst (fst (loopFamilyUC) (p , q)) = h ∘UC pairUC (constantUC p) (fst q)
  snd (fst (loopFamilyUC) (p , q)) =
    (cong (λ x → fst h (p , x)) (fst (snd q)) ∙ based p) ,
    (cong (λ x → fst h (p , x)) (snd (snd q)) ∙ based p)
  snd loopFamilyUC = PT.map (λ (μ , uc) → (λ ε → μ (ε /2₊)) ,
    isuniformlycontinuouswith (λ (p , f) (q , g) ε (pq , fg) →
      ∣ (ε /2₊ , /2₊<id ε , λ t →
        IsUniformlyContinuousWith.pres≈ uc
          (p , LX.at f t) (q , LX.at g t) (ε /2₊)
          (pq , ≈→→pointwise 𝕀 (fst X) (LX.at f) (LX.at g) (μ (ε /2₊)) fg t)) ∣₁)) (snd h)

  loopFamily-β : (p : fst P) (q : LX.RealLoop) (t : 𝕀) →
    LY.at (fst loopFamilyUC (p , q)) t ≡ fst h (p , LX.at q t)
  loopFamily-β p q t = refl

  loopFamily-based : (p : fst P) →
    fst loopFamilyUC (p , snd (realΩ X)) ≡ snd (realΩ Y)
  loopFamily-based p = LY.path-ext (λ t → based p)

module _ {ℓP ℓP'} (P : PremetricSpace ℓP ℓP') where

  loopBasedFamily : ∀ {ℓM ℓM' ℓN ℓN'}
    (X : PointedPremetricSpace ℓM ℓM') (Y : PointedPremetricSpace ℓN ℓN') →
    BasedFamily P X Y → BasedFamily P (realΩ X) (realΩ Y)
  loopBasedFamily X Y (h , based) =
    loopFamilyUC P X Y h based , loopFamily-based P X Y h based

  iterateBasedFamily : ∀ {ℓM ℓM' ℓN ℓN'} (n : ℕ)
    (X : PointedPremetricSpace ℓM ℓM') (Y : PointedPremetricSpace ℓN ℓN') →
    BasedFamily P X Y → BasedFamily P (realΩ^ n X) (realΩ^ n Y)
  iterateBasedFamily zero X Y h = h
  iterateBasedFamily (suc n) X Y h =
    loopBasedFamily (realΩ^ n X) (realΩ^ n Y) (iterateBasedFamily n X Y h)
