module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Currying where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open 1/2∈ℚ using (/2+/2≡id)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open CategoryStructures using (_∘UC_; UC≡)

-- The parameter spaces include all finite real cubes. The target may live
-- in arbitrary universes and need not be complete.
module UniformCurrying {ℓ ℓ'}
  (A B : PremetricSpace ℓ-zero ℓ-zero) (X : PremetricSpace ℓ ℓ') where
  private
    module PA = PremetricStr (snd A)
    module PB = PremetricStr (snd B)
    module PX = PremetricStr (snd X)

  MappingSpace = MappingSpaces.UC[ B , X ]PrSpace

  slice : UC[ PremetricProduct A B , X ] → fst A → UC[ B , X ]
  slice f a = f ∘UC leftInsertionUC A B a

  curryUC : UC[ PremetricProduct A B , X ] → UC[ A , MappingSpace ]
  fst (curryUC f) = slice f
  snd (curryUC f) = PT.map (λ (μ , c) → (λ ε → μ (ε /2₊)) ,
    isuniformlycontinuouswith (λ a a' ε close →
      ∣ (ε /2₊ , /2₊<id ε , λ b → IsUniformlyContinuousWith.pres≈ c
        (a , b) (a' , b) (ε /2₊) (close , PB.isRefl≈ b (μ (ε /2₊)))) ∣₁)) (snd f)

  -- One common modulus for every slice. This is stronger than merely
  -- knowing separately that each slice has some modulus.
  EquiuniformSlices : UC[ A , MappingSpace ] → Type ℓ'
  EquiuniformSlices g = ∥ Σ[ ν ∈ (ℚ₊ → ℚ₊) ]
    ((a : fst A) (b b' : fst B) (ε : ℚ₊) → b PB.≈[ ν ε ] b' →
      fst (fst g a) b PX.≈[ ε ] fst (fst g a) b') ∥₁

  curry-equiuniform : (f : UC[ PremetricProduct A B , X ]) →
    EquiuniformSlices (curryUC f)
  curry-equiuniform f = PT.map (λ (μ , c) → μ , λ a b b' ε close →
    IsUniformlyContinuousWith.pres≈ c (a , b) (a , b') ε
      (PA.isRefl≈ a (μ ε) , close)) (snd f)

  uncurryUC : (g : UC[ A , MappingSpace ]) → EquiuniformSlices g →
    UC[ PremetricProduct A B , X ]
  fst (uncurryUC g equi) (a , b) = fst (fst g a) b
  snd (uncurryUC g equi) = PT.map2 combine (snd g) equi
    where
    combine :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd A) (fst g) (snd MappingSpace) μ) →
      (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] ((a : fst A) (b b' : fst B) (ε : ℚ₊) →
        b PB.≈[ ν ε ] b' → fst (fst g a) b PX.≈[ ε ] fst (fst g a) b')) →
      Σ[ κ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
        (snd (PremetricProduct A B)) (λ (a , b) → fst (fst g a) b) (snd X) κ
    combine (μ , c) (ν , d) = (λ ε → min₊ (μ (ε /2₊)) (ν (ε /2₊))) ,
      isuniformlycontinuouswith (λ (a , b) (a' , b') ε (aa' , bb') →
        PX.subst≈ _ _ (/2+/2≡id (fst ε))
          (PX.isTriangular≈ _ _ _ (ε /2₊) (ε /2₊)
            (≈→→pointwise (fst B) X (fst (fst g a)) (fst (fst g a')) (ε /2₊)
              (IsUniformlyContinuousWith.pres≈ c a a' (ε /2₊)
                (PA.isMonotone≈≤ a a' _ _ (min₊≤L (μ (ε /2₊)) (ν (ε /2₊))) aa')) b)
            (d a' b b' (ε /2₊)
              (PB.isMonotone≈≤ b b' _ _ (min₊≤R (μ (ε /2₊)) (ν (ε /2₊))) bb'))))

  uncurry-curry : (f : UC[ PremetricProduct A B , X ]) →
    uncurryUC (curryUC f) (curry-equiuniform f) ≡ f
  uncurry-curry f = UC≡ refl

  curry-uncurry : (g : UC[ A , MappingSpace ]) (equi : EquiuniformSlices g) →
    curryUC (uncurryUC g equi) ≡ g
  curry-uncurry g equi = UC≡ (funExt (λ a → UC≡ refl))

  -- A full exponential law with the necessary uniformity data visible.
  -- All truncation eliminations above are finite; no choice is used.
  uniformCurryingIso : Iso UC[ PremetricProduct A B , X ]
    (Σ[ g ∈ UC[ A , MappingSpace ] ] EquiuniformSlices g)
  Iso.fun uniformCurryingIso f = curryUC f , curry-equiuniform f
  Iso.inv uniformCurryingIso (g , equi) = uncurryUC g equi
  Iso.sec uniformCurryingIso (g , equi) = Σ≡Prop (λ _ → squash₁) (curry-uncurry g equi)
  Iso.ret uniformCurryingIso = uncurry-curry
