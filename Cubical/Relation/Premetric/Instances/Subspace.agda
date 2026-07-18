module Cubical.Relation.Premetric.Instances.Subspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings


private
  variable
    ℓ ℓ' ℓM ℓM' ℓN ℓN' : Level


PremetricSubspaceStr : {M : Type ℓ} →
  (P : ℙ M) → PremetricStr ℓ' M → PremetricStr ℓ' (Σ M (_∈ P))
PremetricSubspaceStr P metric = subspace
  where
  module M = PremetricStr metric

  subspace : PremetricStr _ _
  PremetricStr._≈[_]_ subspace x ε y = fst x M.≈[ ε ] fst y
  PremetricStr.isPremetric subspace = isSubspacePremetric
    where
    open IsPremetric

    isSubspacePremetric : IsPremetric (PremetricStr._≈[_]_ subspace)
    isSubspacePremetric .isSetM =
      isSetΣ M.isSetM (isProp→isSet ∘ ∈-isProp P)
    isSubspacePremetric .isProp≈ x y ε = M.isProp≈ (fst x) (fst y) ε
    isSubspacePremetric .isRefl≈ x ε = M.isRefl≈ (fst x) ε
    isSubspacePremetric .isSym≈ x y ε = M.isSym≈ (fst x) (fst y) ε
    isSubspacePremetric .isSeparated≈ x y allClose =
      Σ≡Prop (∈-isProp P) (M.isSeparated≈ (fst x) (fst y) allClose)
    isSubspacePremetric .isTriangular≈ x y z ε δ =
      M.isTriangular≈ (fst x) (fst y) (fst z) ε δ
    isSubspacePremetric .isRounded≈ x y ε = M.isRounded≈ (fst x) (fst y) ε


PremetricSubspace :
  (M : PremetricSpace ℓ ℓ') → ℙ ⟨ M ⟩ → PremetricSpace ℓ ℓ'
PremetricSubspace M P =
  Σ ⟨ M ⟩ (_∈ P) , PremetricSubspaceStr P (snd M)


subspace≈→base≈ :
  (M : PremetricSpace ℓ ℓ') (P : ℙ ⟨ M ⟩) →
  (x y : ⟨ PremetricSubspace M P ⟩) (ε : ℚ₊) →
  PremetricStr._≈[_]_ (snd (PremetricSubspace M P)) x ε y →
  PremetricStr._≈[_]_ (snd M) (fst x) ε (fst y)
subspace≈→base≈ M P x y ε = idfun _


base≈→subspace≈ :
  (M : PremetricSpace ℓ ℓ') (P : ℙ ⟨ M ⟩) →
  (x y : ⟨ PremetricSubspace M P ⟩) (ε : ℚ₊) →
  PremetricStr._≈[_]_ (snd M) (fst x) ε (fst y) →
  PremetricStr._≈[_]_ (snd (PremetricSubspace M P)) x ε y
base≈→subspace≈ M P x y ε = idfun _


subspaceInclusionNE :
  (M : PremetricSpace ℓ ℓ') (P : ℙ ⟨ M ⟩) →
  NE[ PremetricSubspace M P , M ]
fst (subspaceInclusionNE M P) = fst
IsNonExpanding.pres≈ (snd (subspaceInclusionNE M P)) x y ε = idfun _


subspaceInclusionUC :
  (M : PremetricSpace ℓ ℓ') (P : ℙ ⟨ M ⟩) →
  UC[ PremetricSubspace M P , M ]
subspaceInclusionUC M P = NE→UC (subspaceInclusionNE M P)


restrictNE :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  (P : ℙ ⟨ M ⟩) (Q : ℙ ⟨ N ⟩) →
  (f : NE[ M , N ]) →
  (∀ x → x ∈ P → fst f x ∈ Q) →
  NE[ PremetricSubspace M P , PremetricSubspace N Q ]
fst (restrictNE P Q f f∈) (x , x∈) = fst f x , f∈ x x∈
IsNonExpanding.pres≈ (snd (restrictNE P Q f f∈)) x y ε =
  IsNonExpanding.pres≈ (snd f) (fst x) (fst y) ε


restrictUC :
  {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} →
  (P : ℙ ⟨ M ⟩) (Q : ℙ ⟨ N ⟩) →
  (f : UC[ M , N ]) →
  (∀ x → x ∈ P → fst f x ∈ Q) →
  UC[ PremetricSubspace M P , PremetricSubspace N Q ]
fst (restrictUC P Q f f∈) (x , x∈) = fst f x , f∈ x x∈
snd (restrictUC {M = M} {N = N} P Q f f∈) =
  PT.map
    (λ (mu , mu-uc) →
      mu , isuniformlycontinuouswith
        (λ x y ε →
          IsUniformlyContinuousWith.pres≈ mu-uc
            (fst x) (fst y) ε))
    (snd f)
