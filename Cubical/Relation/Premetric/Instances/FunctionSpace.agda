module Cubical.Relation.Premetric.Instances.FunctionSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base using (fiber)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (⟨_⟩ ; str)

open import Cubical.Data.Sigma

open import Cubical.Data.Rationals.Properties as ℚ using ()
open import Cubical.Data.Rationals.Order as ℚOrd using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace

open OrderedCommRingStr (str ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

private
  variable
    ℓA ℓM ℓM' ℓN ℓN' ℓX ℓX' : Level

module _ {ℓA ℓN ℓN'} (A : Type ℓA) (N' : PremetricSpace ℓN ℓN') where
  private
    N = ⟨ N' ⟩
    module PN = PremetricStr (snd N')
    module NTh = PremetricTheory N'

  infix 5 _≈→[_]_

  -- Definition 2.14
  _≈→[_]_ : (A → N) → ℚ₊ → (A → N) → Type (ℓ-max ℓA ℓN')
  f ≈→[ ε ] g = ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ x → f x PN.≈[ δ ] g x)

  -- Lemma 2.15
  ≈→→pointwise : ∀ f g ε → f ≈→[ ε ] g → ∀ x → f x PN.≈[ ε ] g x
  ≈→→pointwise f g ε =
    PT.rec (isPropΠ λ x → PN.isProp≈ (f x) (g x) ε) λ where
      (δ , δ<ε , pw) x → PN.isMonotone≈< (f x) (g x) δ ε δ<ε (pw x)

  -- Theorem 2.16 (first part)
  isPremetric→ : IsPremetric _≈→[_]_
  isPremetric→ .IsPremetric.isSetM = isSet→ PN.isSetM
  isPremetric→ .IsPremetric.isProp≈ _ _ _ = squash₁
  isPremetric→ .IsPremetric.isRefl≈ f ε =
    ∣ (ε /2₊ , /2₊<id ε , λ x → PN.isRefl≈ (f x) (ε /2₊)) ∣₁
  isPremetric→ .IsPremetric.isSym≈ f g ε =
    PT.map λ where
      (δ , δ<ε , pw) → (δ , δ<ε , λ x → PN.isSym≈ (f x) (g x) δ (pw x))
  isPremetric→ .IsPremetric.isSeparated≈ f g f≈g =
    funExt λ x → PN.isSeparated≈ (f x) (g x) λ ε → ≈→→pointwise f g ε (f≈g ε) x
  isPremetric→ .IsPremetric.isTriangular≈ f g h ε θ f≈g g≈h = do
    (δ₁ , δ₁<ε , fg) ← f≈g
    (δ₂ , δ₂<θ , gh) ← g≈h
    return (δ₁ +₊ δ₂
          , +Mono< ⟨ δ₁ ⟩₊ ⟨ ε ⟩₊ ⟨ δ₂ ⟩₊ ⟨ θ ⟩₊ δ₁<ε δ₂<θ
          , λ x → PN.isTriangular≈ (f x) (g x) (h x) δ₁ δ₂ (fg x) (gh x))
  isPremetric→ .IsPremetric.isRounded≈ f g ε =
    PT.map λ where
      (δ₁ , δ₁<ε , pw) →
        (mean₊ δ₁ ε , <₊→mean₊<₊ δ₁ ε δ₁<ε , ∣ δ₁ , <₊→<₊mean₊ δ₁ ε δ₁<ε , pw ∣₁)

  →PremetricSpace : PremetricSpace (ℓ-max ℓA ℓN) (ℓ-max ℓA ℓN')
  fst →PremetricSpace = A → N
  snd →PremetricSpace = premetricstr _≈→[_]_ isPremetric→

  module FTh = PremetricTheory →PremetricSpace

  -- Theorem 2.16 (second part)
  isComplete→ : NTh.isComplete → FTh.isComplete
  isComplete→ N-complete s s-cauchy = l , l-lim
    where
    pointwiseCauchy : ∀ x → NTh.isCauchy (λ ε → s ε x)
    pointwiseCauchy x ε θ = ≈→→pointwise (s ε) (s θ) (ε +₊ θ) (s-cauchy ε θ) x

    l : A → N
    l x = fst (N-complete (λ ε → s ε x) (pointwiseCauchy x))

    l-lim-pointwise : ∀ x → NTh.isLimit (λ ε → s ε x) (l x)
    l-lim-pointwise x = snd (N-complete (λ ε → s ε x) (pointwiseCauchy x))

    l-lim : FTh.isLimit s l
    l-lim ε θ =
      ∣ (ε +₊ θ /2₊
      , +MonoL< ⟨ θ /2₊ ⟩₊ ⟨ θ ⟩₊ ⟨ ε ⟩₊ (/2₊<id θ)
      , λ x → l-lim-pointwise x ε (θ /2₊))
      ∣₁

module _ {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where
  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    module PM = PremetricStr (snd M')
    module PN = PremetricStr (snd N')
    module NTh' = PremetricTheory N'
    module FTh' = PremetricTheory (→PremetricSpace M N')

  -- Lemma 2.17
  limLipschitz :
    (N-complete : NTh'.isComplete) (L : ℚ₊)
    → (s : ℚ₊ → (M → N)) (s-cauchy : FTh'.isCauchy s)
    → (∀ ε → IsLipschitzWith (snd M') (s ε) (snd N') L)
    → IsLipschitzWith (snd M') (fst (isComplete→ M N' N-complete s s-cauchy)) (snd N') L
  limLipschitz N-complete L s s-cauchy L-lip .IsLipschitzWith.pres≈ x y ε x≈y =
    PT.rec (PN.isProp≈ (l x) (l y) (L ·₊ ε)) (step x y ε) (PM.isRounded≈ x y ε x≈y)
    where
    l : M → N
    l = fst (isComplete→ M N' N-complete s s-cauchy)

    l-lim : FTh'.isLimit s l
    l-lim = snd (isComplete→ M N' N-complete s s-cauchy)

    l-lim-pointwise : ∀ z → NTh'.isLimit (λ ρ → s ρ z) (l z)
    l-lim-pointwise z ρ θ = ≈→→pointwise M N' (s ρ) l (ρ +₊ θ) (l-lim ρ θ) z

    step : ∀ x y ε → Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x PM.≈[ δ ] y) → l x PN.≈[ L ·₊ ε ] l y
    step x y ε (δ , δ<ε , x≈δy) =
      PN.isRounded≈⁻ (l x) (l y) (L ·₊ ε)
        ∣ (η +₊ (η +₊ L ·₊ δ)
        , η+η+Lδ<Lε
        , NTh'.isLim≈+₂
            (λ ρ → s ρ x) (λ ρ → s ρ y) (l x) (l y)
            (L ·₊ δ) η η
            (l-lim-pointwise x)
            (l-lim-pointwise y)
            (IsLipschitzWith.pres≈ (L-lip η) x y δ x≈δy))
        ∣₁
      where
      Lδ<Lε : (L ·₊ δ) <₊ (L ·₊ ε)
      Lδ<Lε = ·MonoL< ⟨ δ ⟩₊ ⟨ ε ⟩₊ ⟨ L ⟩₊ (snd L) δ<ε

      gap : ℚ₊
      gap = [ (L ·₊ ε) -₊ (L ·₊ δ) ]⟨ Lδ<Lε ⟩

      η : ℚ₊
      η = gap /4₊

      η+η+Lδ<Lε : η +₊ (η +₊ L ·₊ δ) <₊ L ·₊ ε
      η+η+Lδ<Lε = begin<
        ⟨ η +₊ (η +₊ L ·₊ δ) ⟩₊      ≡→≤⟨ ℚ.+Assoc ⟨ η ⟩₊ ⟨ η ⟩₊ ⟨ L ·₊ δ ⟩₊ ⟩
        ⟨ η +₊ η ⟩₊ ℚ.+ ⟨ L ·₊ δ ⟩₊  ≡→≤⟨ cong (ℚ._+ ⟨ L ·₊ δ ⟩₊) (/4+/4≡/2 ⟨ gap ⟩₊) ⟩
        ⟨ gap /2₊ +₊ L ·₊ δ ⟩₊         <⟨ /2₊<id gap <+[ ⟨ L ·₊ δ ⟩₊ ] ⟩
        ⟨ gap ⟩₊ ℚ.+ ⟨ L ·₊ δ ⟩₊     ≡→≤⟨ minusPlus₊ (L ·₊ ε) (L ·₊ δ) ⟩
        ⟨ L ·₊ ε ⟩₊                   ◾

  -- TO DO :
  -- A fixed Lipschitz constant is preserved by limits.  The mapping-space
  -- constructions below package the corresponding predicates as subspaces.

module MappingSpaces
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  where
  private
    M = ⟨ M' ⟩
    N = ⟨ N' ⟩
    module PM = PremetricStr (snd M')
    module PN = PremetricStr (snd N')
    module FT = PremetricTheory (→PremetricSpace M N')

    isSetNE : isSet NE[ M' , N' ]
    isSetNE = isSetΣSndProp (isSet→ PN.isSetM)
      (λ (f : M → N) → isPropIsNonExpanding (snd M') f (snd N'))

    isSetC : isSet C[ M' , N' ]
    isSetC = isSetΣSndProp (isSet→ PN.isSetM)
      (λ (f : M → N) → isPropIsContinuous (snd M') f (snd N'))

    isSetUC : isSet UC[ M' , N' ]
    isSetUC = isSetΣSndProp (isSet→ PN.isSetM)
      (λ (f : M → N) →
        isPropIsUniformlyContinuous (snd M') f (snd N'))

    isSetL : isSet L[ M' , N' ]
    isSetL = isSetΣSndProp (isSet→ PN.isSetM)
      (λ (f : M → N) → isPropIsLipschitz (snd M') f (snd N'))

    module NESpace = SubspaceAlongInjection
      (→PremetricSpace M N')
      isSetNE
      (λ (f : NE[ M' , N' ]) → fst f)
      (λ (f g : NE[ M' , N' ]) → Σ≡Prop λ h →
        isPropIsNonExpanding (snd M') h (snd N'))

    module CSpace = SubspaceAlongInjection
      (→PremetricSpace M N')
      isSetC
      (λ (f : C[ M' , N' ]) → fst f)
      (λ (f g : C[ M' , N' ]) → Σ≡Prop λ h →
        isPropIsContinuous (snd M') h (snd N'))

    module UCSpace = SubspaceAlongInjection
      (→PremetricSpace M N')
      isSetUC
      (λ (f : UC[ M' , N' ]) → fst f)
      (λ (f g : UC[ M' , N' ]) → Σ≡Prop λ h →
        isPropIsUniformlyContinuous (snd M') h (snd N'))

    module LSpace = SubspaceAlongInjection
      (→PremetricSpace M N')
      isSetL
      (λ (f : L[ M' , N' ]) → fst f)
      (λ (f g : L[ M' , N' ]) → Σ≡Prop λ h →
        isPropIsLipschitz (snd M') h (snd N'))

  NE[_,_]PrSpace :
    PremetricSpace
      (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN')
      (ℓ-max ℓM ℓN')
  NE[_,_]PrSpace = NESpace.injectionPremetricSpace

  C[_,_]PrSpace :
    PremetricSpace
      (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN')
      (ℓ-max ℓM ℓN')
  C[_,_]PrSpace = CSpace.injectionPremetricSpace

  UC[_,_]PrSpace :
    PremetricSpace
      (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN')
      (ℓ-max ℓM ℓN')
  UC[_,_]PrSpace = UCSpace.injectionPremetricSpace

  L[_,_]PrSpace :
    PremetricSpace
      (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') ℓN) ℓN')
      (ℓ-max ℓM ℓN')
  L[_,_]PrSpace = LSpace.injectionPremetricSpace

  module _ (N-complete : PremetricTheory.isComplete N') where
    private
      functionSpaceComplete :
        FT.isComplete
      functionSpaceComplete = isComplete→ M N' N-complete

      limitNE :
        (x : ℚ₊ → NE[ M' , N' ])
        (xs : FT.isCauchy (λ ε → fst (x ε)))
        → IsNonExpanding
            (snd M')
            (fst (functionSpaceComplete (λ ε → fst (x ε)) xs))
            (snd N')
      limitNE x xs = isLipschitzWith1→isNonExpanding
        (snd M')
        (fst (functionSpaceComplete (λ ε → fst (x ε)) xs))
        (snd N')
        (limLipschitz M' N' N-complete 1 (λ ε → fst (x ε)) xs
          (λ ε → isNonExpanding→isLipschitzWith1
            (snd M') (fst (x ε)) (snd N') (snd (x ε))))

      limitNEInFiber :
        (x : ℚ₊ → NE[ M' , N' ])
        (xs : FT.isCauchy (λ ε → fst (x ε)))
        → fiber (λ (f : NE[ M' , N' ]) → fst f)
            (fst (functionSpaceComplete (λ ε → fst (x ε)) xs))
      fst (limitNEInFiber x xs) =
        fst (functionSpaceComplete (λ ε → fst (x ε)) xs) , limitNE x xs
      snd (limitNEInFiber x xs) = refl

    isCompleteNE : PremetricTheory.isComplete NE[_,_]PrSpace
    isCompleteNE =
      NESpace.fiberLimit→isComplete functionSpaceComplete limitNEInFiber

module BinaryNonExpanding
  (M : PremetricSpace ℓM ℓM')
  (N : PremetricSpace ℓN ℓN')
  (X : PremetricSpace ℓX ℓX')
  where
  open IsNonExpanding

  private
    module PM = PremetricStr (snd M)
    ℓM* = ℓ-max ℓM ℓM'
    ℓN* = ℓ-max ℓN ℓN'
    ℓX* = ℓ-max ℓX ℓX'

  record NE₂[_,_,_] : Type (ℓ-max ℓM* (ℓ-max ℓN* ℓX*)) where
    no-eta-equality
    field
      fun : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩
      leftNE : ∀ y → IsNonExpanding (snd M) (flip fun y) (snd X)
      rightNE : ∀ x → IsNonExpanding (snd N) (fun x) (snd X)

    makeNE₂ : NE[ M , MappingSpaces.NE[ N , X ]PrSpace ]
    fst (fst makeNE₂ x) = fun x
    snd (fst makeNE₂ x) = rightNE x
    pres≈ (snd makeNE₂) x y ε =
      PT.map (λ where
        (δ , δ<ε , x≈y) →
          δ , δ<ε , λ z → pres≈ (leftNE z) x y δ x≈y)
      ∘ PM.isRounded≈ x y ε

  open NE₂[_,_,_]

  NE→NE₂ : NE[ M , MappingSpaces.NE[ N , X ]PrSpace ] → NE₂[_,_,_]
  fun (NE→NE₂ f) = fst ∘ fst f
  pres≈ (leftNE (NE→NE₂ f) y) a b ε =
    flip (≈→→pointwise ⟨ N ⟩ X (fst (fst f a)) (fst (fst f b)) ε) y
      ∘ pres≈ (snd f) a b ε
  rightNE (NE→NE₂ f) x = snd (fst f x)

flipNE :
  {M : PremetricSpace ℓM ℓM'}
  {N : PremetricSpace ℓN ℓN'}
  {X : PremetricSpace ℓX ℓX'}
  → NE[ M , MappingSpaces.NE[ N , X ]PrSpace ]
  → NE[ N , MappingSpaces.NE[ M , X ]PrSpace ]
flipNE {M = M} {N = N} {X = X} f =
  NMX.NE₂[_,_,_].makeNE₂ flipped
  where
  module MNX = BinaryNonExpanding M N X
  module NMX = BinaryNonExpanding N M X

  flipped : NMX.NE₂[_,_,_]
  NMX.NE₂[_,_,_].fun flipped = flip (fst ∘ fst f)
  NMX.NE₂[_,_,_].leftNE flipped = MNX.NE₂[_,_,_].rightNE (MNX.NE→NE₂ f)
  NMX.NE₂[_,_,_].rightNE flipped = MNX.NE₂[_,_,_].leftNE (MNX.NE→NE₂ f)

evalⁿ :
  {M : PremetricSpace ℓM ℓM'}
  {N : PremetricSpace ℓN ℓN'}
  → NE[ M , MappingSpaces.NE[
      MappingSpaces.NE[ M , N ]PrSpace , N ]PrSpace ]
evalⁿ = flipNE CategoryStructures.idⁿ

module CompositionMappings (X : PremetricSpace ℓX ℓX') where
  open CategoryStructures
  open IsNonExpanding

  module _
    {M : PremetricSpace ℓM ℓM'}
    {N : PremetricSpace ℓN ℓN'}
    where

    -∘ⁿ_ :
      NE[ M , N ]
      → NE[ MappingSpaces.NE[ N , X ]PrSpace
          , MappingSpaces.NE[ M , X ]PrSpace ]
    fst (-∘ⁿ f) = _∘NE f
    pres≈ (snd (-∘ⁿ f)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) → δ , δ<ε , g≈h ∘ fst f

    -∘ᴸ_ :
      L[ M , N ]
      → NE[ MappingSpaces.L[ N , X ]PrSpace
          , MappingSpaces.L[ M , X ]PrSpace ]
    fst (-∘ᴸ f) = _∘L f
    pres≈ (snd (-∘ᴸ f)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) → δ , δ<ε , g≈h ∘ fst f

    -∘ᵘᶜ_ :
      UC[ M , N ]
      → NE[ MappingSpaces.UC[ N , X ]PrSpace
          , MappingSpaces.UC[ M , X ]PrSpace ]
    fst (-∘ᵘᶜ f) = _∘UC f
    pres≈ (snd (-∘ᵘᶜ f)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) → δ , δ<ε , g≈h ∘ fst f

    -∘ᶜ_ :
      C[ M , N ]
      → NE[ MappingSpaces.C[ N , X ]PrSpace
          , MappingSpaces.C[ M , X ]PrSpace ]
    fst (-∘ᶜ f) = _∘C f
    pres≈ (snd (-∘ᶜ f)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) → δ , δ<ε , g≈h ∘ fst f

    _ⁿ∘ⁿ- :
      NE[ M , N ]
      → NE[ MappingSpaces.NE[ X , M ]PrSpace
          , MappingSpaces.NE[ X , N ]PrSpace ]
    fst (f ⁿ∘ⁿ-) = f ∘NE_
    pres≈ (snd (f ⁿ∘ⁿ-)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) →
          δ , δ<ε , λ x → pres≈ (snd f) (fst g x) (fst h x) δ (g≈h x)

    _ⁿ∘ᴸ- :
      NE[ M , N ]
      → NE[ MappingSpaces.L[ X , M ]PrSpace
          , MappingSpaces.L[ X , N ]PrSpace ]
    fst (f ⁿ∘ᴸ-) = NE→L f ∘L_
    pres≈ (snd (f ⁿ∘ᴸ-)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) →
          δ , δ<ε , λ x → pres≈ (snd f) (fst g x) (fst h x) δ (g≈h x)

    _ⁿ∘ᵘᶜ- :
      NE[ M , N ]
      → NE[ MappingSpaces.UC[ X , M ]PrSpace
          , MappingSpaces.UC[ X , N ]PrSpace ]
    fst (f ⁿ∘ᵘᶜ-) = NE→UC f ∘UC_
    pres≈ (snd (f ⁿ∘ᵘᶜ-)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) →
          δ , δ<ε , λ x → pres≈ (snd f) (fst g x) (fst h x) δ (g≈h x)

    _ⁿ∘ᶜ- :
      NE[ M , N ]
      → NE[ MappingSpaces.C[ X , M ]PrSpace
          , MappingSpaces.C[ X , N ]PrSpace ]
    fst (f ⁿ∘ᶜ-) = NE→C f ∘C_
    pres≈ (snd (f ⁿ∘ᶜ-)) g h ε =
      PT.map λ where
        (δ , δ<ε , g≈h) →
          δ , δ<ε , λ x → pres≈ (snd f) (fst g x) (fst h x) δ (g≈h x)
