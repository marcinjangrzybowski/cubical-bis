module Cubical.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Univalence

open import Cubical.Categories.Category.Base as Cat

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast as ℤ
open import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)


open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto hiding (id)
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Relation.Binary.Properties
open import Cubical.Relation.Premetric.Base

open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ


private
  variable
    ℓ ℓ' ℓM ℓM' ℓN ℓN' : Level

module _
  {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A)
  (f : A → B)
  (N : PremetricStr ℓN' B)
  where

  private
    module M = PremetricStr M
    module N = PremetricStr N

  record IsContinuousAt (x : A) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor iscontinuousat
    field
      pres≈ : ∀ ε → ∃[ δ ∈ ℚ₊ ] (∀ y → x M.≈[ δ ] y → f x N.≈[ ε ] f y)

  unquoteDecl IsContinuousAtIsoΣ = declareRecordIsoΣ IsContinuousAtIsoΣ (quote IsContinuousAt)

  isPropIsContinuousAt : ∀ x → isProp (IsContinuousAt x)
  isPropIsContinuousAt x = isOfHLevelRetractFromIso 1
    IsContinuousAtIsoΣ $ isPropΠ λ _ → squash₁

  isContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isContinuous = ∀ x → IsContinuousAt x

  isPropIsContinuous : isProp isContinuous
  isPropIsContinuous = isPropΠ isPropIsContinuousAt

  record IsUniformlyContinuousWith (μ : ℚ₊ → ℚ₊) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isuniformlycontinuouswith
    field
      pres≈ : ∀ x y ε → x M.≈[ μ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsUniformlyContinuousWithIsoΣ = declareRecordIsoΣ IsUniformlyContinuousWithIsoΣ (quote IsUniformlyContinuousWith)

  isPropIsUniformlyContinuousWith : ∀ L → isProp (IsUniformlyContinuousWith L)
  isPropIsUniformlyContinuousWith L = isOfHLevelRetractFromIso 1
    IsUniformlyContinuousWithIsoΣ $ isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isUniformlyContinuous : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isUniformlyContinuous = ∃[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith μ

  isPropIsUniformlyContinuous : isProp isUniformlyContinuous
  isPropIsUniformlyContinuous = squash₁

  record IsLipschitzWith (L : ℚ₊) : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor islipschitzwith
    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ L ·₊ ε ] f y

  unquoteDecl IsLipschitzWithIsoΣ = declareRecordIsoΣ IsLipschitzWithIsoΣ (quote IsLipschitzWith)

  isPropIsLipschitzWith : ∀ L → isProp (IsLipschitzWith L)
  isPropIsLipschitzWith L = isOfHLevelRetractFromIso 1
    IsLipschitzWithIsoΣ $ isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  isLipschitz : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN')
  isLipschitz = ∃[ L ∈ ℚ₊ ] IsLipschitzWith L

  isPropIsLipschitz : isProp isLipschitz
  isPropIsLipschitz = squash₁

  record IsNonExpanding : Type (ℓ-max (ℓ-max ℓM ℓM') ℓN') where
    no-eta-equality
    constructor isnonexpanding
    field
      pres≈ : ∀ x y ε → x M.≈[ ε ] y → f x N.≈[ ε ] f y

  unquoteDecl IsNonExpandingIsoΣ = declareRecordIsoΣ IsNonExpandingIsoΣ (quote IsNonExpanding)

  isPropIsNonExpanding : isProp IsNonExpanding
  isPropIsNonExpanding = isOfHLevelRetractFromIso 1 IsNonExpandingIsoΣ $
    isPropΠ3 λ _ _ _ → isProp→ (N.isProp≈ _ _ _)

  -- Implications Non-expanding ⇒ Lipschitz ⇒ U.Continuous ⇒ Continuous :

  isNonExpanding→isLipschitzWith1 : IsNonExpanding → IsLipschitzWith 1
  isNonExpanding→isLipschitzWith1 isNE .IsLipschitzWith.pres≈ x y ε =
    N.subst≈ (f x) (f y) (sym (ℚ.·IdL ⟨ ε ⟩₊)) ∘ isNE .IsNonExpanding.pres≈ x y ε

  isLipschitzWith1→isNonExpanding : IsLipschitzWith 1 → IsNonExpanding
  IsNonExpanding.pres≈ (isLipschitzWith1→isNonExpanding lip) x y ε =
    N.subst≈ (f x) (f y) (ℚ.·IdL ⟨ ε ⟩₊) ∘ lip .IsLipschitzWith.pres≈ x y ε

  IsNonExpanding≃IsLipschitzWith1 : IsNonExpanding ≃ IsLipschitzWith 1
  IsNonExpanding≃IsLipschitzWith1 = propBiimpl→Equiv
    isPropIsNonExpanding (isPropIsLipschitzWith 1)
    isNonExpanding→isLipschitzWith1 isLipschitzWith1→isNonExpanding

  isNonExpanding→isLipschitz : IsNonExpanding → isLipschitz
  isNonExpanding→isLipschitz isNE = ∣ 1 , isNonExpanding→isLipschitzWith1 isNE ∣₁

  isLipschitz→isUniformlyContinuous : isLipschitz → isUniformlyContinuous
  isLipschitz→isUniformlyContinuous = PT.map λ
    { (L , L-lip) .fst → _/ L
    ; (L , L-lip) .snd .IsUniformlyContinuousWith.pres≈ x y ε →
      N.subst≈ (f x) (f y) (·/ L ε) ∘ L-lip .IsLipschitzWith.pres≈ x y (ε / L) }

  isUniformlyContinuous→isContinuous : isUniformlyContinuous → isContinuous
  isUniformlyContinuous→isContinuous is-uc x .IsContinuousAt.pres≈ ε = do
    (μ , μ-uc) ← is-uc
    return λ where
      .fst → μ ε
      .snd → flip (μ-uc .IsUniformlyContinuousWith.pres≈ x) ε

  isNonExpanding→isUniformlyContinuous : IsNonExpanding → isUniformlyContinuous
  isNonExpanding→isUniformlyContinuous =
    isLipschitz→isUniformlyContinuous ∘ isNonExpanding→isLipschitz

  isLipschitz→isContinuous : isLipschitz → isContinuous
  isLipschitz→isContinuous =
    isUniformlyContinuous→isContinuous ∘ isLipschitz→isUniformlyContinuous

  isNonExpanding→isContinuous : IsNonExpanding → isContinuous
  isNonExpanding→isContinuous =
    isLipschitz→isContinuous ∘ isNonExpanding→isLipschitz

C[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
C[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isContinuous (M .snd) f (N .snd)

UC[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
UC[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isUniformlyContinuous (M .snd) f (N .snd)

L[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
L[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] isLipschitz (M .snd) f (N .snd)

NE[_,_] : PremetricSpace ℓM ℓM' → PremetricSpace ℓN ℓN' → Type _
NE[ M , N ] = Σ[ f ∈ (M .fst → N .fst) ] IsNonExpanding (M .snd) f (N .snd)

NE→L : ∀ {M : PremetricSpace ℓM ℓM'} {N : PremetricSpace ℓN ℓN'} → NE[ M , N ] → L[ M , N ]
fst (NE→L f) = fst f
snd (NE→L f) = isNonExpanding→isLipschitz _ (fst f) _ (snd f)

module CategoryStructures where
  open OrderedCommRingStr (str ℚOrderedCommRing)

  idⁿ : ∀ {M : PremetricSpace ℓM ℓM'} → NE[ M , M ]
  fst idⁿ = idfun _
  IsNonExpanding.pres≈ (snd idⁿ) = λ _ _ _ → idfun _

  idᶜ : ∀ {M : PremetricSpace ℓM ℓM'} → C[ M , M ]
  fst idᶜ = idfun _
  snd idᶜ = isNonExpanding→isContinuous _ _ _ (idⁿ .snd)

  idᵘᶜ : ∀ {M : PremetricSpace ℓM ℓM'} → UC[ M , M ]
  fst idᵘᶜ = idfun _
  snd idᵘᶜ = isNonExpanding→isUniformlyContinuous _ _ _ (idⁿ .snd)

  idᴸ : ∀ {M : PremetricSpace ℓM ℓM'} → L[ M , M ]
  fst idᴸ = idfun _
  snd idᴸ = isNonExpanding→isLipschitz _ _ _ (idⁿ .snd)

  _∘NE_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → NE[ N , O ] → NE[ M , N ] → NE[ M , O ]
  fst (g ∘NE f) = fst g ∘ fst f
  IsNonExpanding.pres≈ (snd (g ∘NE f)) =
    λ x y ε → g .snd .pres≈ (fst f x) (fst f y) ε ∘ f .snd .pres≈ x y ε
    where open IsNonExpanding

  _∘C_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → C[ N , O ] → C[ M , N ] → C[ M , O ]
  fst (g ∘C f) = fst g ∘ fst f
  IsContinuousAt.pres≈ (snd (g ∘C f) x) = λ ε → do
    (δ , ≈δ→≈ε) ← g .snd (fst f x) .pres≈ ε
    (η , ≈η→≈δ) ← f .snd x .pres≈ δ
    return λ where
      .fst   → η
      .snd y → ≈δ→≈ε (fst f y) ∘ ≈η→≈δ y
    where open IsContinuousAt

  _∘UC_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → UC[ N , O ] → UC[ M , N ] → UC[ M , O ]
  fst (g ∘UC f) = fst g ∘ fst f
  snd (g ∘UC f) = do
    (μ , μ-uc) ← f .snd
    (ν , ν-uc) ← g .snd
    return λ where
      .fst → μ ∘ ν
      .snd .pres≈ x y ε → ν-uc .pres≈ (fst f x) (fst f y) ε ∘ μ-uc .pres≈ x y (ν ε)
    where open IsUniformlyContinuousWith

  _∘L_ : ∀ {M N O : PremetricSpace ℓM ℓM'} → L[ N , O ] → L[ M , N ] → L[ M , O ]
  fst (g ∘L f) = fst g ∘ fst f
  snd (_∘L_ {O = O} g f) = do
    (L , L-lip) ← f .snd
    (R , R-lip) ← g .snd
    return λ where
      .fst → R ·₊ L
      .snd .pres≈ x y ε →
        subst≈ (str O) (fst g (fst f x)) (fst g (fst f y)) (ℚ.·Assoc ⟨ R ⟩₊ ⟨ L ⟩₊ _)
        ∘ R-lip .pres≈ (fst f x) (fst f y) (L ·₊ ε)
        ∘ L-lip .pres≈ x y ε
    where
      open IsLipschitzWith
      open PremetricStr

  C≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : C[ M , N ]} → fst f ≡ fst g → f ≡ g
  C≡ = ΣPathPProp (flip (isPropIsContinuous _) _)

  UC≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : UC[ M , N ]} → fst f ≡ fst g → f ≡ g
  UC≡ = ΣPathPProp λ _ → squash₁

  L≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : L[ M , N ]} → fst f ≡ fst g → f ≡ g
  L≡ = ΣPathPProp λ _ → squash₁

  NE≡ : ∀ {M N : PremetricSpace ℓM ℓM'} → {f g : NE[ M , N ]} → fst f ≡ fst g → f ≡ g
  NE≡ = ΣPathPProp (flip (isPropIsNonExpanding _) _)

  module _ (ℓM ℓM' : Level) where
    open Category

    PremetricSpaceCategoryᶜ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryᶜ = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryᶜ = C[_,_]
    id       PremetricSpaceCategoryᶜ = idᶜ
    _⋆_      PremetricSpaceCategoryᶜ = flip _∘C_
    ⋆IdL     PremetricSpaceCategoryᶜ = λ _ → C≡ refl
    ⋆IdR     PremetricSpaceCategoryᶜ = λ _ → C≡ refl
    ⋆Assoc   PremetricSpaceCategoryᶜ = λ _ _ _ → C≡ refl
    isSetHom PremetricSpaceCategoryᶜ {y = N} =
      isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsContinuous _) _)
      where open PremetricStr

    PremetricSpaceCategoryᵘᶜ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryᵘᶜ = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryᵘᶜ = UC[_,_]
    id       PremetricSpaceCategoryᵘᶜ = idᵘᶜ
    _⋆_      PremetricSpaceCategoryᵘᶜ = flip _∘UC_
    ⋆IdL     PremetricSpaceCategoryᵘᶜ = λ _ → UC≡ refl
    ⋆IdR     PremetricSpaceCategoryᵘᶜ = λ _ → UC≡ refl
    ⋆Assoc   PremetricSpaceCategoryᵘᶜ = λ _ _ _ → UC≡ refl
    isSetHom PremetricSpaceCategoryᵘᶜ {y = N} =
      isSetΣSndProp (isSet→ (N .snd .isSetM)) λ _ → squash₁
      where open PremetricStr

    PremetricSpaceCategoryᴸ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryᴸ = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryᴸ = L[_,_]
    id       PremetricSpaceCategoryᴸ = idᴸ
    _⋆_      PremetricSpaceCategoryᴸ = flip _∘L_
    ⋆IdL     PremetricSpaceCategoryᴸ = λ _ → L≡ refl
    ⋆IdR     PremetricSpaceCategoryᴸ = λ _ → L≡ refl
    ⋆Assoc   PremetricSpaceCategoryᴸ = λ _ _ _ → L≡ refl
    isSetHom PremetricSpaceCategoryᴸ {y = N} =
      isSetΣSndProp (isSet→ (N .snd .isSetM)) λ _ → squash₁
      where open PremetricStr

    PremetricSpaceCategoryⁿ : Category (ℓ-suc (ℓ-max ℓM ℓM')) (ℓ-max ℓM ℓM')
    ob       PremetricSpaceCategoryⁿ = PremetricSpace ℓM ℓM'
    Hom[_,_] PremetricSpaceCategoryⁿ = NE[_,_]
    id       PremetricSpaceCategoryⁿ = idⁿ
    _⋆_      PremetricSpaceCategoryⁿ = flip _∘NE_
    ⋆IdL     PremetricSpaceCategoryⁿ = λ _ → NE≡ refl
    ⋆IdR     PremetricSpaceCategoryⁿ = λ _ → NE≡ refl
    ⋆Assoc   PremetricSpaceCategoryⁿ = λ _ _ _ → NE≡ refl
    isSetHom PremetricSpaceCategoryⁿ {y = N} =
      isSetΣSndProp (isSet→ (N .snd .isSetM)) (flip (isPropIsNonExpanding _) _)
      where open PremetricStr

  open isIso
  CatIsoⁿ→CatIsoᴸ : ∀ {M N : PremetricSpace ℓM ℓM'}
                  → CatIso (PremetricSpaceCategoryⁿ ℓM ℓM') M N
                  → CatIso (PremetricSpaceCategoryᴸ ℓM ℓM') M N
  fst (CatIsoⁿ→CatIsoᴸ f)       = NE→L (fst f)
  inv (snd (CatIsoⁿ→CatIsoᴸ f)) = NE→L (inv (snd f))
  sec (snd (CatIsoⁿ→CatIsoᴸ f)) = L≡ (cong fst (sec (snd f)))
  ret (snd (CatIsoⁿ→CatIsoᴸ f)) = L≡ (cong fst (ret (snd f)))

record IsIsometry {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
  : Type (ℓ-suc (ℓ-max ℓM (ℓ-max ℓN (ℓ-max ℓM' ℓN'))))
  where
  no-eta-equality
  constructor
    isisometry
  -- Shorter qualified names
  private
    module M = PremetricStr M
    module N = PremetricStr N

  field
    pres≈ : ∀ x ε y → x M.≈[ ε ] y ≃ equivFun e x N.≈[ ε ] equivFun e y

unquoteDecl IsIsometryIsoΣ = declareRecordIsoΣ IsIsometryIsoΣ (quote IsIsometry)

isPropIsIsometry : {A : Type ℓM} {B : Type ℓN}
  (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
  → isProp (IsIsometry M e N)
isPropIsIsometry M e N = isOfHLevelRetractFromIso 1
  IsIsometryIsoΣ $ isPropΠ3 λ _ _ _ → isOfHLevel≃ 1
    (isProp≈ M _ _ _) (isProp≈ N _ _ _)
    where open PremetricStr

isIsometry→IsNonExpanding : {A : Type ℓM} {B : Type ℓN}
                          → (M : PremetricStr ℓM' A) (e : A ≃ B) (N : PremetricStr ℓN' B)
                          → IsIsometry M e N
                          → IsNonExpanding M (equivFun e) N
IsNonExpanding.pres≈ (isIsometry→IsNonExpanding M e N ise) x y ε =
  equivFun (IsIsometry.pres≈ ise x ε y)

IsIsometry→isContinuous : {A : Type ℓM} {B : Type ℓN}
                       → (M : PremetricStr ℓM' A)
                       → (e : A ≃ B)
                       → (N : PremetricStr ℓN' B)
                       → IsIsometry M e N
                       → isContinuous M (equivFun e) N
IsIsometry→isContinuous M e N =
  isNonExpanding→isContinuous M (equivFun e) N ∘ isIsometry→IsNonExpanding M e N

IsIsometry→isUniformlyContinuous : {A : Type ℓM} {B : Type ℓN}
                                 → (M : PremetricStr ℓM' A)
                                 → (e : A ≃ B)
                                 → (N : PremetricStr ℓN' B)
                                 → IsIsometry M e N
                                 → isUniformlyContinuous M (equivFun e) N
IsIsometry→isUniformlyContinuous M e N =
  isNonExpanding→isUniformlyContinuous M (equivFun e) N ∘ isIsometry→IsNonExpanding M e N

IsIsometry→isLipschitz : {A : Type ℓM} {B : Type ℓN}
                       → (M : PremetricStr ℓM' A)
                       → (e : A ≃ B)
                       → (N : PremetricStr ℓN' B)
                       → IsIsometry M e N
                       → isLipschitz M (equivFun e) N
IsIsometry→isLipschitz M e N =
  isNonExpanding→isLipschitz M (equivFun e) N ∘ isIsometry→IsNonExpanding M e N

PremetricSpaceEquiv : (M : PremetricSpace ℓM ℓM') (N : PremetricSpace ℓN ℓN') → Type _
PremetricSpaceEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsIsometry (M .snd) e (N .snd)

module _ {ℓ ℓ' : Level} where
  𝒮ᴰ-Premetric : DUARel (𝒮-Univ ℓ) (PremetricStr ℓ') (ℓ-suc (ℓ-max ℓ ℓ'))
  𝒮ᴰ-Premetric =
    𝒮ᴰ-Record (𝒮-Univ _) IsIsometry
      (fields:
        data[ _≈[_]_ ∣ ternRel ∣ pres≈ ]
        prop[ isPremetric ∣ (λ _ _ → isPropIsPremetric _) ])
    where
    open PremetricStr
    open IsIsometry

    ternRel = autoDUARel (𝒮-Univ _) (λ A → A → ℚ₊ → A → Type ℓ')

  PremetricSIP : (M N : PremetricSpace ℓ ℓ') → PremetricSpaceEquiv M N ≃ (M ≡ N)
  PremetricSIP = ∫ 𝒮ᴰ-Premetric .UARel.ua

module _ {ℓ ℓ' : Level} (M N : PremetricSpace ℓ ℓ') where
  open Iso
  open CategoryStructures
  private
    module M = PremetricStr (M .snd)
    module N = PremetricStr (N .snd)

  isCatIso→PremetricSpaceEquiv : (f : NE[ M , N ])
    → Cat.isIso (PremetricSpaceCategoryⁿ ℓ ℓ') f
    → PremetricSpaceEquiv M N
  isCatIso→PremetricSpaceEquiv f fi = isoToEquiv is , isisometry pres
    where
    open Cat.isIso fi renaming (inv to invⁿ ; sec to secⁿ ; ret to retⁿ)

    is : Iso ⟨ M ⟩ ⟨ N ⟩
    is .fun = fst f
    is .inv = fst invⁿ
    is .sec = funExt⁻ (cong fst secⁿ)
    is .ret = funExt⁻ (cong fst retⁿ)

    pres : ∀ x ε y → x M.≈[ ε ] y ≃ isoToEquiv is .fst x N.≈[ ε ] isoToEquiv is .fst y
    pres x ε y = propBiimpl→Equiv
      (M.isProp≈ x y ε)
      (N.isProp≈ (fst f x) (fst f y) ε)
      (IsNonExpanding.pres≈ (snd f) x y ε)
      (subst2 (λ x y → x M.≈[ ε ] y) (funExt⁻ (cong fst retⁿ) x) (funExt⁻ (cong fst retⁿ) y)
        ∘ IsNonExpanding.pres≈ (snd invⁿ) (fst f x) (fst f y) ε)

  CatIso→PremetricSpaceEquiv : CatIso (PremetricSpaceCategoryⁿ ℓ ℓ') M N
                             → PremetricSpaceEquiv M N
  CatIso→PremetricSpaceEquiv = uncurry isCatIso→PremetricSpaceEquiv

  PremetricSpaceEquiv→CatIso : PremetricSpaceEquiv M N
                             → CatIso (PremetricSpaceCategoryⁿ ℓ ℓ') M N
  fst (PremetricSpaceEquiv→CatIso e) = f where
    f : NE[ M , N ]
    fst f = equivFun (fst e)
    snd f = isIsometry→IsNonExpanding _ (fst e) _ (snd e)
  isIso.inv (snd (PremetricSpaceEquiv→CatIso e)) = g where
    g : NE[ N , M ]
    fst g = invEq (fst e)
    IsNonExpanding.pres≈ (snd g) x y ε =
        invEq (IsIsometry.pres≈ (snd e) (invEq (fst e) x) ε (invEq (fst e) y))
      ∘ subst2 N._≈[ ε ]_ (sym (secEq (fst e) x)) (sym (secEq (fst e) y))
  isIso.sec (snd (PremetricSpaceEquiv→CatIso e)) = NE≡ (funExt (secEq (fst e)))
  isIso.ret (snd (PremetricSpaceEquiv→CatIso e)) = NE≡ (funExt (retEq (fst e)))

  PrSpacesⁿCatIso≃PremetricSpaceEquiv
    : CatIso (PremetricSpaceCategoryⁿ ℓ ℓ') M N ≃ PremetricSpaceEquiv M N
  PrSpacesⁿCatIso≃PremetricSpaceEquiv = isoToEquiv isom
    where
    isom : Iso (CatIso (PremetricSpaceCategoryⁿ ℓ ℓ') M N) (PremetricSpaceEquiv M N)
    isom .fun = CatIso→PremetricSpaceEquiv
    isom .inv = PremetricSpaceEquiv→CatIso
    isom .sec (e , ise) =
      Σ≡Prop (λ _ → isPropIsIsometry (M .snd) _ (N .snd))
        (equivEq refl)
    isom .ret (f , _) = CatIso≡ _ _ (NE≡ refl)

isUnivalentPrSpacesⁿ : isUnivalent (CategoryStructures.PremetricSpaceCategoryⁿ ℓ ℓ')
isUnivalent.univ isUnivalentPrSpacesⁿ M N =
  precomposesToId→Equiv pathToIso _
    (funExt (CatIso≡ _ _ ∘ CategoryStructures.NE≡ ∘ λ _ → transportRefl _))
    (snd (PrSpacesⁿCatIso≃PremetricSpaceEquiv M N ∙ₑ PremetricSIP M N))
