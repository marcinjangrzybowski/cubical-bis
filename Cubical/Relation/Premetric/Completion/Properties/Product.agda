module Cubical.Relation.Premetric.Completion.Properties.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_)
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.FunctionSpace

import Cubical.Relation.Premetric.Completion.Base
  as CompletionDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as CompletionPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as CompletionLift

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing
open CategoryStructures

private
  variable
    ℓM ℓM' ℓN ℓN' : Level


-- Completion preserves the max product, as an isomorphism of underlying
-- types.  The forward map extends
--
--   (m , n) ↦ (ι m , ι n),
--
-- while the inverse is the binary extension of
--
--   m ↦ n ↦ ι (m , n).

module CompletionProduct
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

  private
    M = M' .fst
    N = N' .fst

    ℓMℭ = ℓ-max ℓM ℓM'
    ℓNℭ = ℓ-max ℓN ℓN'
    ℓMNℭ = ℓ-max ℓMℭ ℓNℭ

    MN : PremetricSpace (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
    MN = PremetricProduct M' N'

  module Mℭ = CompletionDefinition M'
  module Nℭ = CompletionDefinition N'
  module MNℭ = CompletionDefinition MN

  module MP = CompletionPropertiesDefinition M'
  module NP = CompletionPropertiesDefinition N'
  module MNP = CompletionPropertiesDefinition MN

  private
    MℭSpace : PremetricSpace ℓMℭ ℓMℭ
    MℭSpace = MP.ℭPremetricSpace

    NℭSpace : PremetricSpace ℓNℭ ℓNℭ
    NℭSpace = NP.ℭPremetricSpace

    MNℭSpace : PremetricSpace ℓMNℭ ℓMNℭ
    MNℭSpace = MNP.ℭPremetricSpace

    ProductℭSpace : PremetricSpace ℓMNℭ ℓMNℭ
    ProductℭSpace = PremetricProduct MℭSpace NℭSpace

    module PM = PremetricStr (M' .snd)
    module PN = PremetricStr (N' .snd)
    module PMℭ = PremetricStr (MℭSpace .snd)
    module PNℭ = PremetricStr (NℭSpace .snd)
    module PMNℭ = PremetricStr (MNℭSpace .snd)


  productCompletionIsComplete :
    PremetricTheory.isComplete ProductℭSpace
  productCompletionIsComplete =
    isCompleteProduct {M = MℭSpace} {N = NℭSpace}
      MP.isCompleteℭ NP.isCompleteℭ


  baseToProductCompletionsⁿ : NE[ MN , ProductℭSpace ]
  baseToProductCompletionsⁿ .fst (m , n) = Mℭ.ι m , Nℭ.ι n
  baseToProductCompletionsⁿ .snd .IsNonExpanding.pres≈
    (m , n) (m' , n') ε mn≈mn' =
      Mℭ.ι-ι m m' ε (fst mn≈mn')
    , Nℭ.ι-ι n n' ε (snd mn≈mn')

  private
    module LiftPair = CompletionLift.LiftCompleteCodomain
      MN ProductℭSpace productCompletionIsComplete

  completionToProduct : MNℭ.ℭ → Mℭ.ℭ × Nℭ.ℭ
  completionToProduct =
    LiftPair.liftNonExpandingFun baseToProductCompletionsⁿ

  opaque
    completionToProduct-isNonExpanding :
      IsNonExpanding (MNℭSpace .snd) completionToProduct
        (ProductℭSpace .snd)
    completionToProduct-isNonExpanding =
      snd (LiftPair.liftNonExpanding baseToProductCompletionsⁿ)

  completionToProductⁿ : NE[ MNℭSpace , ProductℭSpace ]
  completionToProductⁿ =
    completionToProduct , completionToProduct-isNonExpanding

  completionToProduct-ι : ∀ m n →
    completionToProduct (MNℭ.ι (m , n)) ≡
      (Mℭ.ι m , Nℭ.ι n)
  completionToProduct-ι m n = refl


  private
    pairInjection : M → N → MNℭ.ℭ
    pairInjection m n = MNℭ.ι (m , n)

    pairInjectionLeftⁿ : ∀ n → NE[ M' , MNℭSpace ]
    pairInjectionLeftⁿ n .fst m = pairInjection m n
    pairInjectionLeftⁿ n .snd .IsNonExpanding.pres≈ m m' ε m≈m' =
      MNℭ.ι-ι (m , n) (m' , n) ε (m≈m' , PN.isRefl≈ n ε)

    pairInjectionRightⁿ : ∀ m → NE[ N' , MNℭSpace ]
    pairInjectionRightⁿ m .fst n = pairInjection m n
    pairInjectionRightⁿ m .snd .IsNonExpanding.pres≈ n n' ε n≈n' =
      MNℭ.ι-ι (m , n) (m , n') ε (PM.isRefl≈ m ε , n≈n')

    pairInjectionRightLip : ∀ m →
      IsLipschitzWith (N' .snd) (pairInjection m) (MNℭSpace .snd) 1
    pairInjectionRightLip m =
      isNonExpanding→isLipschitzWith1
        (N' .snd) (pairInjection m) (MNℭSpace .snd)
        (snd (pairInjectionRightⁿ m))

  private
    module NℭMaps = MappingSpaces NℭSpace MNℭSpace
    NℭMapSpace : PremetricSpace ℓMNℭ ℓMNℭ
    NℭMapSpace = NℭMaps.NE[_,_]PrSpace
    module PNℭMap = PremetricStr (NℭMapSpace .snd)

    module LiftRight = CompletionLift.LiftCompleteCodomain
      N' MNℭSpace MNP.isCompleteℭ

    rightExtensionⁿ : M → NE[ NℭSpace , MNℭSpace ]
    rightExtensionⁿ m =
      LiftRight.liftNonExpanding (pairInjectionRightⁿ m)

    opaque
      rightExtensions-isNonExpanding :
        IsNonExpanding (M' .snd) rightExtensionⁿ (NℭMapSpace .snd)
      rightExtensions-isNonExpanding .IsNonExpanding.pres≈
        m m' ε m≈m' =
        PT.rec squash₁ withSmaller (PM.isRounded≈ m m' ε m≈m')
        where
        withSmaller :
          (Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) × (m PM.≈[ κ ] m')) →
          rightExtensionⁿ m PNℭMap.≈[ ε ] rightExtensionⁿ m'
        withSmaller (κ , κ<ε , m≈κm') =
          ∣ κ +₊ η , κ+η<ε , pointwise ∣₁
          where
          gap : ℚ₊
          gap = [ ε -₊ κ ]⟨ κ<ε ⟩

          η : ℚ₊
          η = gap /2₊

          κ+η<ε : (κ +₊ η) <₊ ε
          κ+η<ε = begin<
            fst (κ +₊ η)
              ≡→≤⟨ ℚ.+Comm (fst κ) (fst η) ⟩
            fst (η +₊ κ)
              <⟨ +MonoR< (fst η) (fst gap) (fst κ) (/2₊<id gap) ⟩
            fst (gap +₊ κ)
              ≡→≤⟨ minusPlus₊ ε κ ⟩
            fst ε ◾

          baseClose : ∀ n ρ →
            pairInjection m n PMNℭ.≈[ κ +₊ ρ ] pairInjection m' n
          baseClose n ρ =
            PMNℭ.isMonotone≈< _ _ κ (κ +₊ ρ)
              (<₊SumLeft κ ρ)
              (pairInjectionLeftⁿ n .snd .IsNonExpanding.pres≈
                m m' κ m≈κm')

          pointwise : ∀ y →
            fst (rightExtensionⁿ m) y
              PMNℭ.≈[ κ +₊ η ]
            fst (rightExtensionⁿ m') y
          pointwise y =
            CompletionLift.liftCloseness
              M' N' MNℭSpace MNP.isCompleteℭ 1
              (pairInjection m) (pairInjection m')
              (pairInjectionRightLip m) (pairInjectionRightLip m')
              κ baseClose y η

    rightExtensionsⁿ : NE[ M' , NℭMapSpace ]
    rightExtensionsⁿ =
      rightExtensionⁿ , rightExtensions-isNonExpanding

    module LiftLeft = CompletionLift.LiftCompleteCodomain
      M' NℭMapSpace (NℭMaps.isCompleteNE MNP.isCompleteℭ)

    curriedProductⁿ : NE[ MℭSpace , NℭMapSpace ]
    curriedProductⁿ = LiftLeft.liftNonExpanding rightExtensionsⁿ


  productCompletionsToCompletion : Mℭ.ℭ × Nℭ.ℭ → MNℭ.ℭ
  productCompletionsToCompletion (x , y) =
    fst (fst curriedProductⁿ x) y

  productCompletionsToCompletion-ι : ∀ m n →
    productCompletionsToCompletion (Mℭ.ι m , Nℭ.ι n) ≡
      MNℭ.ι (m , n)
  productCompletionsToCompletion-ι m n = refl


  private
    reindex₁ : ℚ₊ → ℚ₊
    reindex₁ ε = ε ₊／₊ 1

    reindex₁-fst : ∀ ε → fst (reindex₁ ε) ≡ fst ε
    reindex₁-fst ε =
      sym (ℚ.·IdL (fst (reindex₁ ε))) ∙ ·／ 1 ε

    reindex₁-sum : ∀ ε δ →
      fst (reindex₁ ε +₊ reindex₁ δ) ≡ fst (ε +₊ δ)
    reindex₁-sum ε δ =
      cong₂ ℚ._+_ (reindex₁-fst ε) (reindex₁-fst δ)

    opaque
      product-ι-lim-cauchy :
        (m : M) (y : ℚ₊ → Nℭ.ℭ)
        (yc : ∀ ε δ → y ε Nℭ.∼[ ε +₊ δ ] y δ)
        (ε δ : ℚ₊) →
        productCompletionsToCompletion
            (Mℭ.ι m , y (reindex₁ ε))
          MNℭ.∼[ ε +₊ δ ]
        productCompletionsToCompletion
            (Mℭ.ι m , y (reindex₁ δ))
      product-ι-lim-cauchy m y yc ε δ =
        PMNℭ.subst≈ _ _
          {ε = reindex₁ ε +₊ reindex₁ δ} {ε' = ε +₊ δ}
          (reindex₁-sum ε δ)
          (rightExtensionⁿ m .snd .IsNonExpanding.pres≈
            (y (reindex₁ ε)) (y (reindex₁ δ))
            (reindex₁ ε +₊ reindex₁ δ)
            (yc (reindex₁ ε) (reindex₁ δ)))

      product-lim-cauchy :
        (x : ℚ₊ → Mℭ.ℭ)
        (xc : ∀ ε δ → x ε Mℭ.∼[ ε +₊ δ ] x δ)
        (y : Nℭ.ℭ) (ε δ : ℚ₊) →
        productCompletionsToCompletion (x (reindex₁ ε) , y)
          MNℭ.∼[ ε +₊ δ ]
        productCompletionsToCompletion (x (reindex₁ δ) , y)
      product-lim-cauchy x xc y ε δ =
        PMNℭ.subst≈ _ _
          {ε = reindex₁ ε +₊ reindex₁ δ} {ε' = ε +₊ δ}
          (reindex₁-sum ε δ)
          (≈→→pointwise Nℭ.ℭ MNℭSpace _ _
            (reindex₁ ε +₊ reindex₁ δ)
            (curriedProductⁿ .snd .IsNonExpanding.pres≈
              (x (reindex₁ ε)) (x (reindex₁ δ))
              (reindex₁ ε +₊ reindex₁ δ)
              (xc (reindex₁ ε) (reindex₁ δ))) y)


  productCompletionsToCompletion-ι-lim :
    (m : M) (y : ℚ₊ → Nℭ.ℭ)
    (yc : ∀ ε δ → y ε Nℭ.∼[ ε +₊ δ ] y δ) →
    productCompletionsToCompletion (Mℭ.ι m , Nℭ.lim y yc) ≡
      MNℭ.lim
        (λ ε → productCompletionsToCompletion
          (Mℭ.ι m , y (ε ₊／₊ 1)))
        (product-ι-lim-cauchy m y yc)
  productCompletionsToCompletion-ι-lim m y yc =
    cong (MNℭ.lim _)
      ((isPropΠ2 λ ε δ → MNℭ.isProp∼ _ _ _) _ _)

  productCompletionsToCompletion-lim :
    (x : ℚ₊ → Mℭ.ℭ)
    (xc : ∀ ε δ → x ε Mℭ.∼[ ε +₊ δ ] x δ)
    (y : Nℭ.ℭ) →
    productCompletionsToCompletion (Mℭ.lim x xc , y) ≡
      MNℭ.lim
        (λ ε → productCompletionsToCompletion
          (x (ε ₊／₊ 1) , y))
        (product-lim-cauchy x xc y)
  productCompletionsToCompletion-lim x xc y =
    cong (MNℭ.lim _)
      ((isPropΠ2 λ ε δ → MNℭ.isProp∼ _ _ _) _ _)


  private
    join : Mℭ.ℭ → Nℭ.ℭ → MNℭ.ℭ
    join x y = productCompletionsToCompletion (x , y)

    joinRightNE : ∀ x → NE[ NℭSpace , MNℭSpace ]
    joinRightNE x = fst curriedProductⁿ x

    joinRightLip : ∀ x →
      IsLipschitzWith (NℭSpace .snd) (join x) (MNℭSpace .snd) 1
    joinRightLip x = isNonExpanding→isLipschitzWith1
      (NℭSpace .snd) (join x) (MNℭSpace .snd) (snd (joinRightNE x))

    joinLeftNE : ∀ y → NE[ MℭSpace , MNℭSpace ]
    joinLeftNE y .fst x = join x y
    joinLeftNE y .snd .IsNonExpanding.pres≈ x x' ε x≈x' =
      ≈→→pointwise Nℭ.ℭ MNℭSpace
        (join x) (join x') ε
        (curriedProductⁿ .snd .IsNonExpanding.pres≈
          x x' ε x≈x') y

    joinLeftLip : ∀ y →
      IsLipschitzWith (MℭSpace .snd) (flip join y) (MNℭSpace .snd) 1
    joinLeftLip y = isNonExpanding→isLipschitzWith1
      (MℭSpace .snd) (flip join y) (MNℭSpace .snd) (snd (joinLeftNE y))

    joinRightL : ∀ x → L[ NℭSpace , MNℭSpace ]
    joinRightL x = join x , ∣ 1 , joinRightLip x ∣₁

    joinLeftL : ∀ y → L[ MℭSpace , MNℭSpace ]
    joinLeftL y = flip join y , ∣ 1 , joinLeftLip y ∣₁

    joinRightⁿ : ∀ x → NE[ NℭSpace , MNℭSpace ]
    joinRightⁿ x =
      join x , isLipschitzWith1→isNonExpanding
        (NℭSpace .snd) (join x) (MNℭSpace .snd) (joinRightLip x)

    joinLeftⁿ : ∀ y → NE[ MℭSpace , MNℭSpace ]
    joinLeftⁿ y =
      flip join y , isLipschitzWith1→isNonExpanding
        (MℭSpace .snd) (flip join y) (MNℭSpace .snd) (joinLeftLip y)

    completionFstⁿ : NE[ MNℭSpace , MℭSpace ]
    completionFstⁿ = productFstNE ∘NE completionToProductⁿ

    completionSndⁿ : NE[ MNℭSpace , NℭSpace ]
    completionSndⁿ = productSndNE ∘NE completionToProductⁿ

    constantMⁿ : Mℭ.ℭ → NE[ NℭSpace , MℭSpace ]
    constantMⁿ x .fst _ = x
    constantMⁿ x .snd .IsNonExpanding.pres≈ _ _ ε _ = PMℭ.isRefl≈ x ε

    constantNⁿ : Nℭ.ℭ → NE[ MℭSpace , NℭSpace ]
    constantNⁿ y .fst _ = y
    constantNⁿ y .snd .IsNonExpanding.pres≈ _ _ ε _ = PNℭ.isRefl≈ y ε

    firstBaseMap : M → NE[ NℭSpace , MℭSpace ]
    firstBaseMap m =
      completionFstⁿ ∘NE joinRightⁿ (Mℭ.ι m)

    firstBaseConstant : M → NE[ NℭSpace , MℭSpace ]
    firstBaseConstant m = constantMⁿ (Mℭ.ι m)

    firstMap : Nℭ.ℭ → NE[ MℭSpace , MℭSpace ]
    firstMap y = completionFstⁿ ∘NE joinLeftⁿ y

    secondBaseMap : N → NE[ MℭSpace , NℭSpace ]
    secondBaseMap n =
      completionSndⁿ ∘NE joinLeftⁿ (Nℭ.ι n)

    secondBaseConstant : N → NE[ MℭSpace , NℭSpace ]
    secondBaseConstant n = constantNⁿ (Nℭ.ι n)

    secondMap : Mℭ.ℭ → NE[ NℭSpace , NℭSpace ]
    secondMap x = completionSndⁿ ∘NE joinRightⁿ x


    opaque
      firstOnBaseLeft : ∀ m →
        (λ (y : Nℭ.ℭ) → fst (completionToProduct (join (Mℭ.ι m) y))) ≡
        (λ (_ : Nℭ.ℭ) → Mℭ.ι m)
      firstOnBaseLeft m = cong fst $
        CompletionLift.nonExpanding≡ N' MℭSpace
          (firstBaseMap m) (firstBaseConstant m)
          (funExt λ n →
            cong (fst ∘ completionToProduct)
              (productCompletionsToCompletion-ι m n)
            ∙ cong fst (completionToProduct-ι m n))

      firstProjection : ∀ y →
        (λ x → fst (completionToProduct (join x y))) ≡ idfun Mℭ.ℭ
      firstProjection y = cong fst $
        CompletionLift.nonExpanding≡ M' MℭSpace
          (firstMap y) CategoryStructures.idⁿ
          (funExt λ m → funExt⁻ (firstOnBaseLeft m) y)


    opaque
      secondOnBaseRight : ∀ n →
        (λ (x : Mℭ.ℭ) → snd (completionToProduct (join x (Nℭ.ι n)))) ≡
        (λ (_ : Mℭ.ℭ) → Nℭ.ι n)
      secondOnBaseRight n = cong fst $
        CompletionLift.nonExpanding≡ M' NℭSpace
          (secondBaseMap n) (secondBaseConstant n)
          (funExt λ m →
            cong (snd ∘ completionToProduct)
              (productCompletionsToCompletion-ι m n)
            ∙ cong snd (completionToProduct-ι m n))

      secondProjection : ∀ x →
        (λ y → snd (completionToProduct (join x y))) ≡ idfun Nℭ.ℭ
      secondProjection x = cong fst $
        CompletionLift.nonExpanding≡ N' NℭSpace
          (secondMap x) CategoryStructures.idⁿ
          (funExt λ n → funExt⁻ (secondOnBaseRight n) x)


  opaque
    completionToProduct-after-productToCompletion : ∀ x →
      completionToProduct (productCompletionsToCompletion x) ≡ x
    completionToProduct-after-productToCompletion (x , y) =
      cong₂ _,_ (funExt⁻ (firstProjection y) x)
        (funExt⁻ (secondProjection x) y)


  private
    two : ℚ₊
    two = 1 +₊ 1

    twiceRadius : ∀ ε →
      fst (two ·₊ ε) ≡ fst (ε +₊ ε)
    twiceRadius ε =
      ℚ.·DistR+ 1 1 (fst ε)
      ∙ cong₂ ℚ._+_ (ℚ.·IdL (fst ε)) (ℚ.·IdL (fst ε))

    joinLipschitzWithTwo :
      IsLipschitzWith
        (ProductℭSpace .snd) productCompletionsToCompletion
        (MNℭSpace .snd) two
    joinLipschitzWithTwo .IsLipschitzWith.pres≈
      (x , y) (x' , y') ε xy≈xy' =
      PMNℭ.subst≈ (join x y) (join x' y')
        (sym (twiceRadius ε))
        (PMNℭ.isTriangular≈ (join x y) (join x' y) (join x' y')
          ε ε
          (PMNℭ.subst≈ (join x y) (join x' y)
            (ℚ.·IdL (fst ε))
            (joinLeftLip y .IsLipschitzWith.pres≈
              x x' ε (fst xy≈xy')))
          (PMNℭ.subst≈ (join x' y) (join x' y')
            (ℚ.·IdL (fst ε))
            (joinRightLip x' .IsLipschitzWith.pres≈
              y y' ε (snd xy≈xy'))))

    productToCompletionᴸ : L[ ProductℭSpace , MNℭSpace ]
    productToCompletionᴸ =
      productCompletionsToCompletion , ∣ two , joinLipschitzWithTwo ∣₁

    roundTripᴸ : L[ MNℭSpace , MNℭSpace ]
    roundTripᴸ = productToCompletionᴸ ∘L NE→L completionToProductⁿ


  opaque
    productCompletionsToCompletion-isLipschitzWithTwo :
      IsLipschitzWith
        (ProductℭSpace .snd) productCompletionsToCompletion
        (MNℭSpace .snd) (1 +₊ 1)
    productCompletionsToCompletion-isLipschitzWithTwo =
      joinLipschitzWithTwo

  productCompletionsToCompletionᴸ :
    L[ ProductℭSpace , MNℭSpace ]
  productCompletionsToCompletionᴸ = productToCompletionᴸ


  opaque
    productToCompletion-after-completionToProduct : ∀ x →
      productCompletionsToCompletion (completionToProduct x) ≡ x
    productToCompletion-after-completionToProduct x =
      funExt⁻ (cong fst $
        CompletionLift.lipschitz≡ MN MNℭSpace
          roundTripᴸ CategoryStructures.idᴸ
          (funExt λ { (m , n) →
            cong productCompletionsToCompletion
              (completionToProduct-ι m n)
            ∙ productCompletionsToCompletion-ι m n })) x


  completionProductIso : Iso MNℭ.ℭ (Mℭ.ℭ × Nℭ.ℭ)
  completionProductIso .Iso.fun = completionToProduct
  completionProductIso .Iso.inv = productCompletionsToCompletion
  completionProductIso .Iso.sec =
    completionToProduct-after-productToCompletion
  completionProductIso .Iso.ret =
    productToCompletion-after-completionToProduct

  completionProductEquiv : MNℭ.ℭ ≃ (Mℭ.ℭ × Nℭ.ℭ)
  completionProductEquiv = isoToEquiv completionProductIso
