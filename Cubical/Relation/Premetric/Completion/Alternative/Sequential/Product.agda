open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Product
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (prodIso)

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Product

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as RegularComparisonDefinition
import Cubical.Relation.Premetric.Completion.Properties.Product
  as RegularProductDefinition


private
  MN = PremetricProduct M' N'

module M = SequentialDefinition M'
module N = SequentialDefinition N'
module MNₛ = SequentialDefinition MN
module MP = SequentialPropertiesDefinition M'
module NP = SequentialPropertiesDefinition N'
module MNP = SequentialPropertiesDefinition MN

module MComparison = RegularComparisonDefinition M'
module NComparison = RegularComparisonDefinition N'
module MNComparison = RegularComparisonDefinition MN

module RegularProduct = RegularProductDefinition.CompletionProduct M' N'

open CategoryStructures


private
  regularProductToSequentialProductIso : Iso
    (MComparison.Regular.ℭ × NComparison.Regular.ℭ)
    (M.ℭ̂ₛ × N.ℭ̂ₛ)
  regularProductToSequentialProductIso =
    prodIso MComparison.regularSequentialIso
      NComparison.regularSequentialIso


-- The sequential result is transported through the already established
-- isometric comparison with Completion.Base.  Thus all difficult product
-- reasoning is shared with the regular theorem rather than repeated for a
-- second HIT presentation.

sequentialCompletionProductIso :
  Iso MNₛ.ℭ̂ₛ (M.ℭ̂ₛ × N.ℭ̂ₛ)
sequentialCompletionProductIso =
  compIso MNComparison.sequentialRegularIso
    (compIso RegularProduct.completionProductIso
      regularProductToSequentialProductIso)

sequentialCompletionProductEquiv :
  MNₛ.ℭ̂ₛ ≃ (M.ℭ̂ₛ × N.ℭ̂ₛ)
sequentialCompletionProductEquiv =
  isoToEquiv sequentialCompletionProductIso


completionToProduct : MNₛ.ℭ̂ₛ → M.ℭ̂ₛ × N.ℭ̂ₛ
completionToProduct = sequentialCompletionProductIso .Iso.fun

productToCompletion : M.ℭ̂ₛ × N.ℭ̂ₛ → MNₛ.ℭ̂ₛ
productToCompletion = sequentialCompletionProductIso .Iso.inv


-- Besides being an inverse on underlying types, the product-to-completion
-- map is Lipschitz.  Exposing that structure lets limit arguments use the
-- generic sequential-continuity theorem without unfolding the transported
-- isomorphism.

private
  toRegularMⁿ : NE[ MP.ℭ̂ₛPremetricSpace , MComparison.C.ℭPremetricSpace ]
  toRegularMⁿ = MComparison.toRegular ,
    record { pres≈ = MComparison.toRegular∼ }

  toRegularNⁿ : NE[ NP.ℭ̂ₛPremetricSpace , NComparison.C.ℭPremetricSpace ]
  toRegularNⁿ = NComparison.toRegular ,
    record { pres≈ = NComparison.toRegular∼ }

  productToRegularProductⁿ : NE[
      PremetricProduct MP.ℭ̂ₛPremetricSpace NP.ℭ̂ₛPremetricSpace
    , PremetricProduct MComparison.C.ℭPremetricSpace
        NComparison.C.ℭPremetricSpace ]
  productToRegularProductⁿ =
    pairNE (toRegularMⁿ ∘NE productFstNE)
      (toRegularNⁿ ∘NE productSndNE)

  fromRegularMNⁿ : NE[
      MNComparison.C.ℭPremetricSpace , MNP.ℭ̂ₛPremetricSpace ]
  fromRegularMNⁿ = MNComparison.fromRegular ,
    record { pres≈ = MNComparison.fromRegular∼ }

productToCompletionᴸ : L[
    PremetricProduct MP.ℭ̂ₛPremetricSpace NP.ℭ̂ₛPremetricSpace
  , MNP.ℭ̂ₛPremetricSpace ]
productToCompletionᴸ =
  NE→L fromRegularMNⁿ ∘L
    (RegularProduct.productCompletionsToCompletionᴸ ∘L
      NE→L productToRegularProductⁿ)

opaque
  productToCompletion-presIsLimitSeq : ∀ x l →
    PremetricTheory.isLimitSeq
      (PremetricProduct MP.ℭ̂ₛPremetricSpace NP.ℭ̂ₛPremetricSpace) x l →
    PremetricTheory.isLimitSeq MNP.ℭ̂ₛPremetricSpace
      (productToCompletion ∘ x) (productToCompletion l)
  productToCompletion-presIsLimitSeq =
    L→seqContinuous productToCompletionᴸ

completionFst : MNₛ.ℭ̂ₛ → M.ℭ̂ₛ
completionFst = fst ∘ completionToProduct

completionSnd : MNₛ.ℭ̂ₛ → N.ℭ̂ₛ
completionSnd = snd ∘ completionToProduct


completionToProduct-ι : ∀ m n →
  completionToProduct (MNₛ.ι (m , n)) ≡ (M.ι m , N.ι n)
completionToProduct-ι m n =
    cong
      (regularProductToSequentialProductIso .Iso.fun ∘
        RegularProduct.completionToProduct)
      (MNComparison.toRegular-ι (m , n))
  ∙ cong (regularProductToSequentialProductIso .Iso.fun)
      (RegularProduct.completionToProduct-ι m n)
  ∙ cong₂ _,_
      (MComparison.fromRegular-ι m)
      (NComparison.fromRegular-ι n)


productToCompletion-ι : ∀ m n →
  productToCompletion (M.ι m , N.ι n) ≡ MNₛ.ι (m , n)
productToCompletion-ι m n =
    cong
      (MNComparison.fromRegular ∘
        RegularProduct.productCompletionsToCompletion)
      (cong₂ _,_
        (MComparison.toRegular-ι m)
        (NComparison.toRegular-ι n))
  ∙ cong MNComparison.fromRegular
      (RegularProduct.productCompletionsToCompletion-ι m n)
  ∙ MNComparison.fromRegular-ι (m , n)


completionToProduct-after-productToCompletion : ∀ x →
  completionToProduct (productToCompletion x) ≡ x
completionToProduct-after-productToCompletion =
  sequentialCompletionProductIso .Iso.sec

productToCompletion-after-completionToProduct : ∀ x →
  productToCompletion (completionToProduct x) ≡ x
productToCompletion-after-completionToProduct =
  sequentialCompletionProductIso .Iso.ret
