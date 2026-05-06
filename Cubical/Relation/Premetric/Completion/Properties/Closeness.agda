{- This is a formalization of section 3.2 of "Formalising Real Numbers in Homotopy Type Theory", Gilbert -}
-- TO DO : correctly cite the paper
open import Cubical.Relation.Premetric.Base



module Cubical.Relation.Premetric.Completion.Properties.Closeness {ℓ} {ℓ'}
  (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.NatPlusOne.Base as ℕ₊₁
open import Cubical.Data.Int.Fast.Base as ℤ hiding (_-_)

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ using () renaming (_<_ to _<ℚ_)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary.Properties
open import Cubical.Relation.Premetric.Properties

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Reflection.RecordEquiv

open import Cubical.Tactics.CommRingSolver

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open PremetricTheory using (isLimit ; limit ; isComplete ; subst≈L ; subst≈R)
open PremetricTheory.PremetricReasoning M'


private
  M = M' .fst
  ℚOCR = ℚOrderedCommRing
  ℚCR  = OrderedCommRing→CommRing ℚOCR
  ℚR   = OrderedCommRing→Ring ℚOCR
  open OrderedCommRingReasoning ℚOCR
  open OrderedCommRingTheory ℚOCR
  open RingTheory ℚR
  open PremetricStr (M' .snd)
  open import Cubical.Relation.Premetric.Completion.Base M' renaming (ℭ to ℭM)
  open import Cubical.Relation.Premetric.Completion.Elim M'

substℚ₊ : ∀ {ℓP} {P : ℚ₊ → Type ℓP} {ε ε'} → ⟨ ε ⟩₊ ≡ ⟨ ε' ⟩₊ → P ε → P ε'
substℚ₊ {P = P} p = subst P (ℚ₊≡ p)

substBall : ∀ {B : ℚ₊ → ℭM → Type (ℓ-max ℓ ℓ')} {ε ε' y}
          → ⟨ ε ⟩₊ ≡ ⟨ ε' ⟩₊ → B ε y → B ε' y
substBall {B = B} {y = y} = substℚ₊ {P = flip B y}

subst∼ : ∀ x y {ε ε'} → ⟨ ε ⟩₊ ≡ ⟨ ε' ⟩₊ → x ∼[ ε ] y → x ∼[ ε' ] y
subst∼ x y = substℚ₊ {P = x ∼[_] y}

ι-lim+₊ : ∀ x y ε δ yc → ι x ∼[ ε ] y δ → ι x ∼[ ε +₊ δ ] lim y yc
ι-lim+₊ x y ε δ yc p = ι-lim x y (ε +₊ δ) δ yc
  <≤ℚ!
  (subst∼ _ _ (sym (plusMinus₊ ε δ)) p)

lim-ι+₊ : ∀ x y ε δ xc → x δ ∼[ ε ] ι y → lim x xc ∼[ ε +₊ δ ] ι y
lim-ι+₊ x y ε δ xc p = lim-ι x y (ε +₊ δ) δ xc
  <≤ℚ!
  (subst∼ _ _ (sym (plusMinus₊ ε δ)) p)

lim-lim+₊ : ∀ x y ε δ η xc yc → x δ ∼[ ε ] y η → lim x xc ∼[ ε +₊ (δ +₊ η) ] lim y yc
lim-lim+₊ x y ε δ η xc yc p = lim-lim x y (ε +₊ (δ +₊ η)) δ η xc yc
  <≤ℚ!
  (subst∼ _ _ (sym (plusMinus₊ ε (δ +₊ η))) p)

-- Lemma 3.5
isRefl∼ : ∀ x ε → x ∼[ ε ] x
isRefl∼ = Elimℭ-Prop.go e where
  e : Elimℭ-Prop (λ x → ∀ ε → x ∼[ ε ] x)
  Elimℭ-Prop.ιA      e x ε       = ι-ι x x ε (isRefl≈ x ε)
  Elimℭ-Prop.limA    e x xc IH ε =
    lim-lim x x ε (ε /4₊) (ε /4₊) xc xc <≤ℚ!
      (IH (ε /4₊) (ε -₊ (ε /4₊ +₊ ε /4₊) , <≤ℚ!))
  Elimℭ-Prop.isPropA e = λ _ → isPropΠ (λ _ → isProp∼ _ _ _)

-- lemma 3.6
isSetℭ : isSet ℭM
isSetℭ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼[ ε ] y) isRefl∼ (λ _ _ → isPropΠ (λ _ → isProp∼ _ _ _)) (eqℭ _ _)

-- lemma 3.7
isSym∼ : ∀ x y ε → x ∼[ ε ] y → y ∼[ ε ] x
isSym∼ = λ _ _ _ → Recℭ∼.go∼ r where
  r : Recℭ∼ λ x y ε → y ∼[ ε ] x
  Recℭ∼.ι-ι-B     r x y ε x≈y             = ι-ι y x ε (isSym≈ x y ε x≈y)
  Recℭ∼.ι-lim-B   r x y ε δ yc Δ _ q      = lim-ι y x ε δ yc Δ q
  Recℭ∼.lim-ι-B   r x y ε δ xc Δ _ q      = ι-lim y x ε δ xc Δ q
  Recℭ∼.lim-lim-B r x y ε δ η xc yc Δ _ q =
    lim-lim y x ε η δ yc xc <≤ℚ![ Δ ] (subst∼ (y η) (x δ) ℚ!! q)
    
  Recℭ∼.isPropB   r x y ε                 = isProp∼ y ε x

-- Using isSym∼, we can introduce a variant for Casesℭ:


record CasesℭSym {ℓA} {ℓB} (A : Type ℓA)
              (B : A → A → ℚ₊ → Type ℓB) : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (x : ℚ₊ → ℭM) → ((δ ε : ℚ₊) → x δ ∼[ δ +₊ ε ] x ε) → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y ε δ yc Δ
                → ι x ∼[ ε -₊ δ , Δ ] y δ
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
                → B (ιA x) (a∘x δ) (ε -₊ δ , Δ)
                → B (ιA x) (limA y yc) ε
    lim-lim-B : ∀ x y ε δ η xc yc Δ
                → x δ ∼[ ε -₊ (δ +₊ η) , Δ ] y η
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘x ε') (a∘x δ') (ε' +₊ δ'))
                → (a∘y : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B (a∘y ε') (a∘y δ') (ε' +₊ δ'))
                → B (a∘x δ) (a∘y η) (ε -₊ (δ +₊ η) , Δ)
                → B (limA x xc) (limA y yc) ε
    isSymB    : ∀ a a' ε → B a a' ε → B a' a ε
    isPropB   : ∀ a a' ε → isProp (B a a' ε)

  private
    c : Casesℭ A B
    Casesℭ.ιA        c = ιA
    Casesℭ.limA      c = limA
    Casesℭ.eqA       c = eqA
    Casesℭ.ι-ι-B     c = ι-ι-B
    Casesℭ.ι-lim-B   c = ι-lim-B
    Casesℭ.lim-ι-B   c = λ x y ε δ xc Δ xδ∼y Bx Bxc Bxδ,y →
      isSymB (ιA y) (limA x xc) ε
        (ι-lim-B y x ε δ xc Δ
          (isSym∼ (x δ) (ι y) (ε -₊ δ , Δ) xδ∼y)
          Bx
          Bxc
          (isSymB (Bx δ) (ιA y) (ε -₊ δ , Δ) Bxδ,y))
    Casesℭ.lim-lim-B c = lim-lim-B
    Casesℭ.isPropB   c = isPropB

  go : ℭM → A
  go = Casesℭ.go c

  go∼ : {x y : ℭM} {ε : ℚ₊} → x ∼[ ε ] y → B (go x) (go y) ε
  go∼ = Casesℭ.go∼ c

-- Definition 3.8
record IsBall (B : ℚ₊ → ℭM → Type (ℓ-max ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  constructor isball
  field
    isPropBall       : ∀ ε y     → isProp (B ε y)
    isRoundedBall    : ∀ ε y     → B ε y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × B δ y
    isTriangularBall : ∀ ε δ y z → B ε y → y ∼[ δ ] z → B (ε +₊ δ) z

  isMonotoneBall< : ∀ y ε δ → ε <₊ δ → B ε y → B δ y
  isMonotoneBall< y ε δ ε<δ Bεy = subst (flip B y)
    (ℚ₊≡ (ℚ.+Comm ⟨ ε ⟩₊ (δ -₊ ε) ∙ minusPlus₊ δ ε)) $
    isTriangularBall ε [ δ -₊ ε ]⟨ ε<δ ⟩ y y
    (Bεy                          )
    (isRefl∼ y [ δ -₊ ε ]⟨ ε<δ ⟩ )

  isMonotoneBall≤ : ∀ y ε δ → ε ≤₊ δ → B ε y → B δ y
  isMonotoneBall≤ y ε δ ε≤δ Bεy with ⟨ ε ⟩₊ ℚ.≟ ⟨ δ ⟩₊
  ... | ℚ.lt ε<δ = isMonotoneBall< y ε δ ε<δ Bεy
  ... | ℚ.eq ε≡δ = subst (flip B y) (ℚ₊≡ ε≡δ) Bεy
  ... | ℚ.gt δ<ε = ⊥.rec (ℚ.isIrrefl< ⟨ ε ⟩₊ (ℚ.isTrans≤< ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟨ ε ⟩₊ ε≤δ δ<ε))

  isRoundedBall⁻ : ∀ ε y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (B δ y) → B ε y
  isRoundedBall⁻ ε y = PT.rec (isPropBall ε y) $
    uncurry λ δ → uncurry (isMonotoneBall< y δ ε)

  isRoundedBall≃ : ∀ ε y → (B ε y) ≃ (∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (B δ y))
  isRoundedBall≃ ε y = propBiimpl→Equiv
    (isPropBall _ _) squash₁ (isRoundedBall ε y) (isRoundedBall⁻ ε y)

unquoteDecl IsBallIsoΣ = declareRecordIsoΣ IsBallIsoΣ (quote IsBall)

Balls : Type (ℓ-suc (ℓ-max ℓ ℓ'))
Balls = Σ[ B ∈ (ℚ₊ → ℭM → Type (ℓ-max ℓ ℓ')) ] IsBall B

isPropIsBall : ∀ B → isProp (IsBall B)
isPropIsBall B = isOfHLevelRetractFromIso 1
  IsBallIsoΣ $
  isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ isPropBall →
  isProp×
    (isPropΠ3 λ _ _ _ → squash₁)
    (isPropΠ6 λ _ _ _ _ _ _ → isPropBall _ _)

_≈ᴮ[_]_ : Balls → ℚ₊ → Balls → Type (ℓ-max ℓ ℓ')
(B , _) ≈ᴮ[ ε ] (B' , _) = ∀ δ y → (B δ y → B' (δ +₊ ε) y) × (B' δ y → B (δ +₊ ε) y)

isProp≈ᴮ : ∀ B B' ε → isProp (B ≈ᴮ[ ε ] B')
isProp≈ᴮ (B , isBallB) (B' , isBallB') ε =
  isPropΠ2 λ δ y → isProp× (isProp→ (B'.isPropBall _ _)) (isProp→ (B.isPropBall _ _))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

isSym≈ᴮ : ∀ B B' ε → B ≈ᴮ[ ε ] B' → B' ≈ᴮ[ ε ] B
isSym≈ᴮ B B' ε B≈B' δ y = fst Σ-swap-≃ (B≈B' δ y)

-- Defintion 3.9
-- NOTE : The definition of UpperCut present in Gilpert's paper requires
-- an equivalence in the field `isRoundedUpperCut`.
-- However, in order to construct `B[_]⟨_,_⟩`, we only need one implication.
record IsUpperCut (U : ℚ₊ → Type (ℓ-max ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  constructor isuppercut
  field
    isPropUpperCut    : ∀ ε → isProp (U ε)
    isRoundedUpperCut : ∀ ε → U ε → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × U δ

unquoteDecl IsUpperCutIsoΣ = declareRecordIsoΣ IsUpperCutIsoΣ (quote IsUpperCut)

UpperCuts : Type (ℓ-suc (ℓ-max ℓ ℓ'))
UpperCuts = Σ[ U ∈ (ℚ₊ → Type (ℓ-max ℓ ℓ')) ] IsUpperCut U

isPropIsUpperCut : ∀ U → isProp (IsUpperCut U)
isPropIsUpperCut U = isOfHLevelRetractFromIso 1
  IsUpperCutIsoΣ $
  isPropΣ (isPropΠ λ _ → isPropIsProp) λ _ →
    (isPropΠ2 λ _ _ → squash₁)

_≈ᵁ[_]_ : UpperCuts → ℚ₊ → UpperCuts → Type (ℓ-max ℓ ℓ')
(U , _) ≈ᵁ[ ε ] (U' , _) = ∀ δ → (U δ → U' (δ +₊ ε)) × (U' δ → U (δ +₊ ε))

isProp≈ᵁ : ∀ U U' ε → isProp (U ≈ᵁ[ ε ] U')
isProp≈ᵁ (U , isUpperCutU) (U' , isUpperCutU') ε =
  isPropΠ λ δ → isProp× (isProp→ (U'.isPropUpperCut _)) (isProp→ (U.isPropUpperCut _))
  where
    module U  = IsUpperCut isUpperCutU
    module U' = IsUpperCut isUpperCutU'

isSym≈ᵁ : ∀ U U' ε → U ≈ᵁ[ ε ] U' → U' ≈ᵁ[ ε ] U
isSym≈ᵁ U U' ε U≈U' δ = fst Σ-swap-≃ (U≈U' δ)

-- Lemma 3.10
isSeparated≈ᴮ : ∀ B B' → (∀ ε → B ≈ᴮ[ ε ] B') → B ≡ B'
isSeparated≈ᴮ (B , isBallB) (B' , isBallB') B≈B' = Σ≡Prop isPropIsBall $
  funExt λ ε → funExt λ y → hPropExt (B.isPropBall _ _) (B'.isPropBall _ _)
    (λ Bεy → flip (PT.rec (B'.isPropBall _ _)) (B.isRoundedBall ε y Bεy)
     λ (δ , δ<ε , Bδy) →
     subst (flip B' y) (ℚ₊≡ ℚ!!)
                       (fst (B≈B' [ ε -₊ δ ]⟨ δ<ε ⟩ δ y) Bδy) )
    (λ B'εy → flip (PT.rec (B.isPropBall _ _)) (B'.isRoundedBall ε y B'εy)
     λ (δ , δ<ε , B'δy) →
     subst (flip B  y) (ℚ₊≡ ℚ!!)
                       (snd (B≈B' [ ε -₊ δ ]⟨ δ<ε ⟩ δ y) B'δy))
  where
    module B  = IsBall isBallB
    module B' = IsBall isBallB'

-- Lemma 3.11
isSeparated≈ᵁ : ∀ U U' → (∀ ε → U ≈ᵁ[ ε ] U') → U ≡ U'
isSeparated≈ᵁ (U , isUpperCutU) (U' , isUpperCutU') U≈U' = Σ≡Prop isPropIsUpperCut $
  funExt λ ε → hPropExt (U.isPropUpperCut _) (U'.isPropUpperCut _)
    (λ Uε → flip (PT.rec (U'.isPropUpperCut _)) (U.isRoundedUpperCut _ Uε)
     λ (δ , δ<ε , Uδ) → subst U' (ℚ₊≡ ℚ!!)
                                 (fst (U≈U' [ ε -₊ δ ]⟨ δ<ε ⟩ δ) Uδ))
    (λ U'ε → flip (PT.rec (U.isPropUpperCut _)) (U'.isRoundedUpperCut _ U'ε)
     λ (δ , δ<ε , U'δ) → subst U (ℚ₊≡ ℚ!!)
                                 (snd (U≈U' [ ε -₊ δ ]⟨ δ<ε ⟩ δ) U'δ))
  where
    module U  = IsUpperCut isUpperCutU
    module U' = IsUpperCut isUpperCutU'


isBall→isUpperCut : (B : Balls) → ∀ y → IsUpperCut (flip (fst B) y)
isBall→isUpperCut (B , isB) y = isUC where
  open IsBall
  open IsUpperCut

  isUC : IsUpperCut (flip B y)
  isPropUpperCut    isUC = flip (isPropBall isB) y
  isRoundedUpperCut isUC = flip (isRoundedBall isB) y

UpperCut≈ : (x y : M) → UpperCuts
fst (UpperCut≈ x y) = Lift {ℓ'} ℓ ∘ (x ≈[_] y)
snd (UpperCut≈ x y) = isUC where
  open IsUpperCut
  opaque
   isUC : IsUpperCut (UpperCut≈ x y .fst)
   isPropUpperCut    isUC ε (lift p) (lift q) = cong lift (isProp≈ x y ε p q)
   isRoundedUpperCut isUC ε (lift p) = PT.map (λ (δ , δ<ε , q) → (δ , δ<ε , lift q))
                                              (isRounded≈ x y ε p)

UpperCut∃< : (U : ℚ₊ → UpperCuts) → UpperCuts
fst (UpperCut∃< U) ε = ∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] fst (U δ) [ ε -₊ δ ]⟨ δ<ε ⟩
snd (UpperCut∃< U) = isUC∃< where
  module UC (η : ℚ₊) = IsUpperCut (snd (U η))
  open IsUpperCut

  opaque
   isUC∃< : IsUpperCut λ ε → ∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] fst (U δ) [ ε -₊ δ ]⟨ δ<ε ⟩
   isPropUpperCut    isUC∃< _ = squash₁
   isRoundedUpperCut isUC∃< ε = PT.rec squash₁ λ (δ , δ<ε , Uδ[ε-δ]) →
     flip PT.map (UC.isRoundedUpperCut δ _ Uδ[ε-δ]) λ (ξ , ξ<ε-δ , Uδ[ξ]) →
       ξ +₊ δ , <≤ℚ![ ξ<ε-δ ] , ∣ δ , <≤ℚ! ,
            subst (fst (U δ)) (ℚ₊≡ ℚ!!) Uδ[ξ] ∣₁
         

UpperCut∃₂< : (U : ℚ₊ → ℚ₊ → UpperCuts) → UpperCuts
fst (UpperCut∃₂< U) = λ ε →
  ∃[ δ ∈ ℚ₊ ] Σ[ η ∈ ℚ₊ ] Σ[ δ+η<ε ∈ _ ] fst (U δ η) [ ε -₊ (δ +₊ η) ]⟨ δ+η<ε ⟩
snd (UpperCut∃₂< U) = makeOpaque isUC∃₂< where
  module UC (δ η : ℚ₊) = IsUpperCut (snd (U δ η))
  open IsUpperCut

  isUC∃₂< : IsUpperCut _
  isPropUpperCut    isUC∃₂< ε = squash₁
  isRoundedUpperCut isUC∃₂< ε = PT.rec squash₁ $
    λ (δ , η , (δ+η<ε , Uδ,η[ε-[δ+η]])) →
    flip PT.map (UC.isRoundedUpperCut δ η _ Uδ,η[ε-[δ+η]]) (λ (ξ , (ξ<ε-[δ+η] , Uδ,η[ξ])) →
      ξ +₊ (δ +₊ η) , <≤ℚ![ ξ<ε-[δ+η] ] , ∣ δ , η , <≤ℚ! ,
          subst (fst (U δ η)) (ℚ₊≡ ℚ!!) Uδ,η[ξ] ∣₁)




UpperCut∃<→UpperCut∃₂< : ∀ U ε δ δ<ε →
  fst (UpperCut∃< (flip U δ)) [ ε -₊ δ ]⟨ δ<ε ⟩ → fst (UpperCut∃₂< U) ε
UpperCut∃<→UpperCut∃₂< U ε δ δ<ε =
 PT.map λ (η , (η<ε-δ , U[ε-δ-η]η,δ)) →
              η , δ , <≤ℚ![ η<ε-δ ]
                , (flip (subst (fst (U η δ))) U[ε-δ-η]η,δ $ ℚ₊≡ $ ℚ!!)

nonExpanding∼→≈ᵁ : (ℭM → UpperCuts) → Type (ℓ-max ℓ ℓ')
nonExpanding∼→≈ᵁ B = ∀ x y ε → x ∼[ ε ] y → B x ≈ᵁ[ ε ] B y

nonExpanding∼→≈ᴮ : (ℭM → Balls) → Type (ℓ-max ℓ ℓ')
nonExpanding∼→≈ᴮ B = ∀ x y ε → x ∼[ ε ] y → B x ≈ᴮ[ ε ] B y

-- Lemma 3.12
isNonExpanding∼→≈ᵁ→isBall : ∀ B → nonExpanding∼→≈ᵁ B → IsBall (λ ε y → fst (B y) ε)
isNonExpanding∼→≈ᵁ→isBall B isNE = isBall where opaque
  open IsBall
  open IsUpperCut

  isBall : IsBall λ ε y → fst (B y) ε
  isPropBall       isBall ε y                = isPropUpperCut (snd (B y)) ε
  isRoundedBall    isBall ε y                = isRoundedUpperCut (snd (B y)) ε
  isTriangularBall isBall ε δ y z ⟨By⟩ε y∼δz = fst (isNE y z δ y∼δz ε) ⟨By⟩ε

module _ (x y z : M) (ε : ℚ₊) (y≈z : y ≈[ ε ] z) (δ : ℚ₊) where

  B⟨ι,ι⟩→B⟨ι,ι⟩ : Lift {ℓ'} ℓ (x ≈[ δ ] y) → Lift {ℓ'} ℓ (x ≈[ δ +₊ ε ] z)
  B⟨ι,ι⟩→B⟨ι,ι⟩ (lift x≈y) = lift (isTriangular≈ x y z δ ε x≈y y≈z)

private
  B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ : ∀ x y z ε → (y ≈[ ε ] z) → UpperCut≈ x y ≈ᵁ[ ε ] UpperCut≈ x z
  fst (B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ x y z ε y≈z δ) = B⟨ι,ι⟩→B⟨ι,ι⟩ x y z ε y≈z δ
  snd (B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ x y z ε y≈z δ) = B⟨ι,ι⟩→B⟨ι,ι⟩ x z y ε (isSym≈ y z ε y≈z) δ

module _
  (x y : M) (Bx,z_ : ℚ₊ → UpperCuts) (ε δ : ℚ₊)
  (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
  (Δ : 0 <ℚ ε -₊ δ)
  (Bx,y≈ᵁBx,zδ : (UpperCut≈ x y) ≈ᵁ[ ε -₊ δ , Δ ] (Bx,z δ))
  (η : ℚ₊)
  where

  B⟨ι,ι⟩→B⟨ι,lim⟩ : fst (UpperCut≈ x y) η → fst (UpperCut∃< Bx,z_) (η +₊ ε)
  B⟨ι,ι⟩→B⟨ι,lim⟩ x≈y = ∣ δ , _ , B[η+ε-δ]x,zδ ∣₁ where opaque
    

    B[η+ε-δ]x,zδ : fst (Bx,z δ) [ (η +₊ ε) -₊ δ ]⟨ <≤ℚ![ Δ ] ⟩
    B[η+ε-δ]x,zδ = subst (fst (Bx,z δ)) (ℚ₊≡ ℚ!!)
                                        (fst (Bx,y≈ᵁBx,zδ η) x≈y)

  B⟨ι,lim⟩→B⟨ι,ι⟩ : fst (UpperCut∃< Bx,z_) η → fst (UpperCut≈ x y) (η +₊ ε)
  B⟨ι,lim⟩→B⟨ι,ι⟩ B[η]x,limz =
    subst (Lift {ℓ'} ℓ ∘ (x ≈[_] y)) (ℚ₊≡ $ ℚ!!) x≈[η+δ+ε-δ]y where opaque

    module Bz (η : ℚ₊) = IsUpperCut (snd (Bx,z η))

    Bx,zc→ : ∀ ε' δ' η' → fst (Bx,z ε') η' → fst (Bx,z δ') (η' +₊ (ε' +₊ δ'))
    Bx,zc→ ε' δ' η' = fst (Bx,zc ε' δ' η')

    B[η+δ]x,zδ : fst (Bx,z δ) (η +₊ δ)
    B[η+δ]x,zδ = flip (PT.rec (Bz.isPropUpperCut δ (η +₊ δ))) B[η]x,limz λ
      { (δ' , δ'<η , B[η-δ']x,zδ') →
        let
          B[η-δ'+δ'+δ]x,zδ = Bx,zc→ δ' δ [ η -₊ δ' ]⟨ δ'<η ⟩ B[η-δ']x,zδ'

        in
          subst (fst (Bx,z δ)) (ℚ₊≡ $ ℚ!!) B[η-δ'+δ'+δ]x,zδ }

    Bx,zδ→x≈[+ε-δ]y : ∀ ξ → fst (Bx,z δ) ξ → Lift {ℓ'} ℓ (x ≈[ ξ +₊ ((ε -₊ δ) , Δ) ] y)
    Bx,zδ→x≈[+ε-δ]y = λ ξ → snd (Bx,y≈ᵁBx,zδ ξ)

    x≈[η+δ+ε-δ]y : Lift {ℓ'} ℓ (x ≈[ (η +₊ δ) +₊ ((ε -₊ δ) , Δ) ] y)
    x≈[η+δ+ε-δ]y = Bx,zδ→x≈[+ε-δ]y (η +₊ δ) B[η+δ]x,zδ


private
  B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ : ∀ x y Bx,z_ ε δ → (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                  → (Δ : 0 <ℚ ε -₊ δ)
                  → (Bx,y≈ᵁBx,zδ : (UpperCut≈ x y) ≈ᵁ[ ε -₊ δ , Δ ] (Bx,z δ))
                  → (UpperCut≈ x y) ≈ᵁ[ ε ] (UpperCut∃< Bx,z_)
  fst (B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ x y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η) =
    B⟨ι,ι⟩→B⟨ι,lim⟩ x y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η
  snd (B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ x y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η) =
    B⟨ι,lim⟩→B⟨ι,ι⟩ x y Bx,z_ ε δ Bx,zc Δ Bx,y≈ᵁBx,zδ η


module _
  (x : M) (Bx,y_ Bx,z_ : ℚ₊ → UpperCuts) (ε δ η : ℚ₊)
  (Bx,yc : ∀ α β → (Bx,y α) ≈ᵁ[ α +₊ β ] (Bx,y β))
  (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
  (Δ : 0 <ℚ ε -₊ (δ +₊ η))
  (Bx,yδ≈ᵁBx,zη : (Bx,y δ) ≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] (Bx,z η))
  (θ : ℚ₊)
  where

  B⟨ι,lim⟩→B⟨ι,lim⟩ : fst (UpperCut∃< Bx,y_) θ → fst (UpperCut∃< Bx,z_) (θ +₊ ε)
  B⟨ι,lim⟩→B⟨ι,lim⟩ = makeOpaque (PT.map λ (δ' , δ'<θ , B[θ-δ']x,yδ') →
    let

      B[θ-δ'+δ'+δ]x,yδ : fst (Bx,y δ) ([ θ -₊ δ' ]⟨ δ'<θ ⟩ +₊ (δ' +₊ δ))
      B[θ-δ'+δ'+δ]x,yδ = fst (Bx,yc δ' δ [ θ -₊ δ' ]⟨ δ'<θ ⟩) B[θ-δ']x,yδ'

      B[θ+δ+ε-[δ+η]]x,zη = fst (Bx,yδ≈ᵁBx,zη (θ +₊ δ))
         (flip (subst (fst (Bx,y δ))) B[θ-δ'+δ'+δ]x,yδ $ ℚ₊≡ $ ℚ!!)

    in
      η , <≤ℚ![ Δ  ] , (flip (subst (fst (Bx,z η))) B[θ+δ+ε-[δ+η]]x,zη $ ℚ₊≡ $ ℚ!!))

private
  B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ : (x : M) → ∀ Bx,y_ Bx,z_ ε δ η
                    → (Bx,yc : ∀ α β → (Bx,y α) ≈ᵁ[ α +₊ β ] (Bx,y β))
                    → (Bx,zc : ∀ α β → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                    → (Δ : 0 <ℚ ε -₊ (δ +₊ η))
                    → (Bx,yδ≈ᵁBx,zη : (Bx,y δ) ≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] (Bx,z η))
                    → (UpperCut∃< Bx,y_) ≈ᵁ[ ε ] (UpperCut∃< Bx,z_)
  fst (B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ x Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ) =
    B⟨ι,lim⟩→B⟨ι,lim⟩ x Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ
  snd (B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ x Bx,y_ Bx,z_ ε δ η Bx,yc Bx,zc Δ Bx,yδ≈ᵁBx,zη θ) =
    B⟨ι,lim⟩→B⟨ι,lim⟩ x Bx,z_ Bx,y_ ε η δ Bx,zc Bx,yc _ Bx,zη≈ᵁBx,yδ θ
    where opaque

      Bx,zη≈ᵁBx,yδ : (Bx,z η) ≈ᵁ[ ε -₊ (η +₊ δ) , <≤ℚ![ Δ ] ] (Bx,y δ)
      Bx,zη≈ᵁBx,yδ = subst ((Bx,z η) ≈ᵁ[_] (Bx,y δ)) (ℚ₊≡ ℚ!!)
        (isSym≈ᵁ (Bx,y δ) (Bx,z η) (ε -₊ (δ +₊ η) , Δ) Bx,yδ≈ᵁBx,zη)

open RecℭSym

BallsAtι[Rec] : M → RecℭSym UpperCuts (flip ∘ _≈ᵁ[_]_)
ιA        (BallsAtι[Rec] x) = UpperCut≈ x
limA      (BallsAtι[Rec] x) = const ∘ UpperCut∃<
eqA       (BallsAtι[Rec] x) = isSeparated≈ᵁ
ι-ι-B     (BallsAtι[Rec] x) = B⟨ι,ι⟩≈ᵁB⟨ι,ι⟩ x
ι-lim-B   (BallsAtι[Rec] x) = B⟨ι,ι⟩≈ᵁB⟨ι,lim⟩ x
lim-lim-B (BallsAtι[Rec] x) = B⟨ι,lim⟩≈ᵁB⟨ι,lim⟩ x
isSymB    (BallsAtι[Rec] x) = isSym≈ᵁ
isPropB   (BallsAtι[Rec] x) = isProp≈ᵁ

-- Defintion 3.13 (first part)
B⟨ι_,_⟩ : M → ℭM → UpperCuts
B⟨ι_,_⟩ = RecℭSym.go ∘ BallsAtι[Rec]

B[_]⟨ι_,_⟩ : ℚ₊ → M → ℭM → Type (ℓ-max ℓ ℓ')
B[ ε ]⟨ι x , y ⟩ = fst B⟨ι x , y ⟩ ε

isNonExpanding∼→≈ᵁB⟨ι_,⟩ : ∀ (x : M) → nonExpanding∼→≈ᵁ B⟨ι x ,_⟩
isNonExpanding∼→≈ᵁB⟨ι_,⟩ x y z ε = RecℭSym.go∼ (BallsAtι[Rec] x)

B⟨ι_,⟩ : M → Balls
fst B⟨ι x ,⟩ = B[_]⟨ι x ,_⟩
snd B⟨ι x ,⟩ = makeOpaque (isNonExpanding∼→≈ᵁ→isBall B⟨ι x ,_⟩ isNonExpanding∼→≈ᵁB⟨ι x ,⟩)

module _ (Bx : ℚ₊ → Balls) (Bxc : ∀ ε δ → Bx ε ≈ᴮ[ ε +₊ δ ] Bx δ) where

  module isBx (η : ℚ₊) = IsBall (snd (Bx η))

  B⟨limᴿ[_,_],ι_⟩ : M → UpperCuts
  B⟨limᴿ[_,_],ι_⟩ y = UpperCut∃< λ δ →
    flip (fst (Bx δ)) (ι y) , isBall→isUpperCut (Bx δ) (ι y)

  B⟨limᴿ[_,_],lim[_,_]⟩ : (y : ℚ₊ → ℭM) (yc : ∀ α β → y α ∼[ α +₊ β ] y β) → UpperCuts
  B⟨limᴿ[_,_],lim[_,_]⟩ y yc = UpperCut∃₂< λ δ η →
    flip (fst (Bx δ)) (y η) , isBall→isUpperCut (Bx δ) (y η)


  module _ (y z : M) (ε : ℚ₊) (y≈z : y ≈[ ε ] z) (δ : ℚ₊) where

    B⟨lim,ι⟩→B⟨lim,ι⟩ : fst (B⟨limᴿ[_,_],ι_⟩ y) δ → fst (B⟨limᴿ[_,_],ι_⟩ z) (δ +₊ ε)
    B⟨lim,ι⟩→B⟨lim,ι⟩ = makeOpaque (PT.map λ (η , η<δ , B[δ-η]xη,y) →
      let

        B[δ-η+ε]xη,z = isBx.isTriangularBall η
          [ δ -₊ η ]⟨ η<δ ⟩ ε (ι y) (ι z) B[δ-η]xη,y (ι-ι y z ε y≈z)

      in
        η , <≤ℚ![ η<δ  ] , (flip (subst (flip (fst (Bx η)) (ι z))) B[δ-η+ε]xη,z $ ℚ₊≡ $ ℚ!!))
  private
    B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩ : ∀ y z ε
                        → (y ≈[ ε ] z)
                        → (B⟨limᴿ[_,_],ι_⟩ y) ≈ᵁ[ ε ] (B⟨limᴿ[_,_],ι_⟩ z)
    fst (B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩ y z ε y≈z δ) =
      B⟨lim,ι⟩→B⟨lim,ι⟩ y z ε y≈z δ
    snd (B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩ y z ε y≈z δ) =
      B⟨lim,ι⟩→B⟨lim,ι⟩ z y ε (isSym≈ y z ε y≈z) δ

  module _
    (y : M) (z : ℚ₊ → ℭM) (ε δ : ℚ₊)
    (zc : ∀ α β → z α ∼[ α +₊ β ] z β)
    (Δ : 0 <ℚ ε -₊ δ) (y∼zδ : ι y ∼[ ε -₊ δ , Δ ] z δ) (η : ℚ₊)
    where

    B⟨lim,ι⟩→B⟨lim,lim⟩ : fst (B⟨limᴿ[_,_],ι_⟩ y) η
                       → fst (B⟨limᴿ[_,_],lim[_,_]⟩ z zc) (η +₊ ε)
    B⟨lim,ι⟩→B⟨lim,lim⟩ = makeOpaque (PT.map λ (θ , θ<η , B[η-θ]xθ,y) →
      
        θ , δ , <≤ℚ![ Δ ][ θ<η  ]
            , (subst (flip (fst (Bx θ)) (z δ))
              (ℚ₊≡ ℚ!!)
              (isBx.isTriangularBall θ [ η -₊ θ ]⟨ θ<η ⟩ (ε -₊ δ , Δ)
                (ι y) (z δ) B[η-θ]xθ,y y∼zδ)))

    B⟨lim,lim⟩→B⟨lim,ι⟩ : fst (B⟨limᴿ[_,_],lim[_,_]⟩ z zc) η
                       → fst (B⟨limᴿ[_,_],ι_⟩ y) (η +₊ ε)
    B⟨lim,lim⟩→B⟨lim,ι⟩ = makeOpaque (PT.map λ (ξ , ζ , ξ+ζ<η , B[η-[ξ+ζ]]xξ,zζ) →      
        ξ , <≤ℚ![ ξ+ζ<η  ] , (subst (flip (fst (Bx ξ)) (ι y))
          (ℚ₊≡ ℚ!!)
          (isBx.isTriangularBall ξ ([ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ +₊ (ζ +₊ δ)) (ε -₊ δ , Δ)
            (z δ) (ι y)
          (isBx.isTriangularBall ξ [ η -₊ ξ +₊ ζ ]⟨ ξ+ζ<η ⟩ (ζ +₊ δ)
            (z ζ) (z δ)
          (B[η-[ξ+ζ]]xξ,zζ)
          (zc ζ δ))
          (isSym∼ (ι y) (z δ) ((ε -₊ δ) , Δ) y∼zδ))))

  private
    B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩ : ∀ y z ε δ zc Δ
                         → (y∼zδ : ι y ∼[ ε -₊ δ , Δ ] z δ)
                         → (Bx,z_ : ℚ₊ → UpperCuts)
                         → ((α β : ℚ₊) → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                         → (B⟨limᴿ[_,_],ι_⟩ y) ≈ᵁ[ ε -₊ δ , Δ ] (Bx,z δ)
                         → (B⟨limᴿ[_,_],ι_⟩ y) ≈ᵁ[ ε ] (B⟨limᴿ[_,_],lim[_,_]⟩ z zc)
    fst (B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩ y z ε δ zc Δ y∼zδ _ _ _ η) =
      B⟨lim,ι⟩→B⟨lim,lim⟩ y z ε δ zc Δ y∼zδ η
    snd (B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩ y z ε δ zc Δ y∼zδ _ _ _ η) =
      B⟨lim,lim⟩→B⟨lim,ι⟩ y z ε δ zc Δ y∼zδ η

  module _
    (y z : ℚ₊ → ℭM) (ε δ η : ℚ₊)
    (yc : ∀ α β → y α ∼[ α +₊ β ] y β)
    (zc : ∀ α β → z α ∼[ α +₊ β ] z β)
    (Δ : 0 <ℚ ε -₊ (δ +₊ η)) (yδ∼zη : y δ ∼[ ε -₊ (δ +₊ η) , Δ ] z η) (θ : ℚ₊)
    where opaque

    B⟨lim,lim⟩→B⟨lim,lim⟩ : fst (B⟨limᴿ[_,_],lim[_,_]⟩ y yc) θ
                        → fst (B⟨limᴿ[_,_],lim[_,_]⟩ z zc) (θ +₊ ε)
    B⟨lim,lim⟩→B⟨lim,lim⟩ = PT.map λ (ξ , ζ , ξ+ζ<θ , B[θ-[ξ+ζ]]xξ,yζ) →
      let


        B[θ+ε-[ξ+η]]xξ,zη = subst (flip (fst (Bx ξ)) (z η))
          (ℚ₊≡ ℚ!!)
          (isBx.isTriangularBall ξ
            ([ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ +₊ (ζ +₊ δ)) (ε -₊ (δ +₊ η) , Δ)
            (y δ) (z η)
          (isBx.isTriangularBall ξ [ θ -₊ (ξ +₊ ζ) ]⟨ ξ+ζ<θ ⟩ (ζ +₊ δ)
            (y ζ) (y δ)
          (B[θ-[ξ+ζ]]xξ,yζ)
          (yc ζ δ))
          (yδ∼zη))

      in
        ξ , η , <≤ℚ![ ξ+ζ<θ  ][ Δ ] , B[θ+ε-[ξ+η]]xξ,zη

  private
    B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩ : ∀ y z ε δ η yc zc Δ
                          → (yδ∼zη : y δ ∼[ ε -₊ (δ +₊ η) , Δ ] z η)
                          → (Bx,y_ : ℚ₊ → UpperCuts)
                          → ((α β : ℚ₊) → (Bx,y α) ≈ᵁ[ α +₊ β ] (Bx,y β))
                          → (Bx,z_ : ℚ₊ → UpperCuts)
                          → ((α β : ℚ₊) → (Bx,z α) ≈ᵁ[ α +₊ β ] (Bx,z β))
                          → (Bx,y δ) ≈ᵁ[ ε -₊ (δ +₊ η) , Δ ] (Bx,z η)
                          → (B⟨limᴿ[_,_],lim[_,_]⟩ y yc) ≈ᵁ[ ε ] (B⟨limᴿ[_,_],lim[_,_]⟩ z zc)
    fst (B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩ y z ε δ η yc zc Δ yδ∼zη _ _ _ _ _ θ) =
      B⟨lim,lim⟩→B⟨lim,lim⟩ y z ε δ η yc zc Δ yδ∼zη θ
    snd (B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩ y z ε δ η yc zc Δ yδ∼zη _ _ _ _ _ θ) =
      B⟨lim,lim⟩→B⟨lim,lim⟩ z y ε η δ zc yc _ zη∼yδ θ where opaque
        

        zη∼yδ : z η ∼[ ε -₊ (η +₊ δ) , <≤ℚ![ Δ ] ] y δ
        zη∼yδ = subst∼ (z η) (y δ) ℚ!! (isSym∼ (y δ) (z η) (ε -₊ (δ +₊ η) , Δ) yδ∼zη)

  open CasesℭSym

  BallsAtlim[Cases] : CasesℭSym UpperCuts (flip ∘ _≈ᵁ[_]_)
  ιA        BallsAtlim[Cases] = B⟨limᴿ[_,_],ι_⟩
  limA      BallsAtlim[Cases] = B⟨limᴿ[_,_],lim[_,_]⟩
  eqA       BallsAtlim[Cases] = isSeparated≈ᵁ
  ι-ι-B     BallsAtlim[Cases] = B⟨lim,ι⟩≈ᵁB⟨lim,ι⟩
  ι-lim-B   BallsAtlim[Cases] = B⟨lim,ι⟩≈ᵁB⟨lim,lim⟩
  lim-lim-B BallsAtlim[Cases] = B⟨lim,lim⟩≈ᵁB⟨lim,lim⟩
  isSymB    BallsAtlim[Cases] = isSym≈ᵁ
  isPropB   BallsAtlim[Cases] = isProp≈ᵁ

  B⟨limᴿ[_,_],_⟩ : ℭM → UpperCuts
  B⟨limᴿ[_,_],_⟩ = CasesℭSym.go BallsAtlim[Cases]

  isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩ : nonExpanding∼→≈ᵁ B⟨limᴿ[_,_],_⟩
  isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩ = λ _ _ _ → CasesℭSym.go∼ BallsAtlim[Cases]

  B⟨limᴿ[_,_],⟩ : Balls
  B⟨limᴿ[_,_],⟩ = _ ,
    makeOpaque (isNonExpanding∼→≈ᵁ→isBall B⟨limᴿ[_,_],_⟩ isNonExpanding∼→≈ᵁB⟨limᴿ[_,_],⟩)

B[_]⟨limᴿ[_,_],_⟩ : ℚ₊ → ∀ Bx (Bxc : ∀ ε δ → Bx ε ≈ᴮ[ ε +₊ δ ] Bx δ) → ℭM → Type _
B[_]⟨limᴿ[_,_],_⟩ ε Bx Bxc = fst (B⟨limᴿ[ Bx , Bxc ],⟩) ε

module _ (x y : M) (ε : ℚ₊) (x≈y : x ≈[ ε ] y) where
  open IsBall

  B⟨ι,⟩→B⟨ι,⟩ : ∀ z δ → B[ δ ]⟨ι x , z ⟩ → B[ δ +₊ ε ]⟨ι y , z ⟩
  B⟨ι,⟩→B⟨ι,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → (δ : ℚ₊) → B[ δ ]⟨ι x , z ⟩ → B[ δ +₊ ε ]⟨ι y , z ⟩
    ιA      e z δ (lift x≈z) =
      lift (begin≈[ δ +₊ ε ]⟨ ℚ.+Comm ⟨ ε ⟩₊ ⟨ δ ⟩₊ ⟩
        y ≈[ ε ]⟨ ≈⁻ x≈y ⟩
        x ≈[ δ ]⟨ x≈z ⟩
        z ≈∎)
    limA    e z zc Bx,z→By,z δ = PT.map λ (η , η<δ , B[δ-η]ιx,zη) →
      
        η , <≤ℚ![ η<δ ] , subst (B[_]⟨ι y , z η ⟩)
          (ℚ₊≡ $ ℚ!!)
          (Bx,z→By,z η [ δ -₊ η ]⟨ η<δ ⟩ B[δ-η]ιx,zη)
    isPropA e z = isPropΠ λ δ → isProp→ (isPropBall (snd B⟨ι y ,⟩) (δ +₊ ε) z)

private
  B⟨ι,⟩≈ᴮB⟨ι,⟩ : (x y : M) (ε : ℚ₊) → x ≈[ ε ] y → B⟨ι x ,⟩ ≈ᴮ[ ε ] B⟨ι y ,⟩
  B⟨ι,⟩≈ᴮB⟨ι,⟩ x y ε x≈y δ z .fst = B⟨ι,⟩→B⟨ι,⟩ x y ε x≈y z δ
  B⟨ι,⟩≈ᴮB⟨ι,⟩ x y ε x≈y δ z .snd = B⟨ι,⟩→B⟨ι,⟩ y x ε (isSym≈ x y ε x≈y) z δ

module _
  (x : M) (By : ℚ₊ → Balls) (ε δ : ℚ₊)
  (Byc : ∀ α β → By α ≈ᴮ[ α +₊ β ] By β)
  (Δ : 0 <ℚ ε -₊ δ)
  (Bιx≈ᴮ[ε-δ]Byδ : B⟨ι x ,⟩ ≈ᴮ[ ε -₊ δ , Δ ] By δ)
  where

  open IsBall

  B⟨ι,⟩→B⟨lim,⟩ : ∀ z η → B[ η ]⟨ι x , z ⟩ → B[ η +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
  B⟨ι,⟩→B⟨lim,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ η → B[ η ]⟨ι x , z ⟩ → B[ η +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
    ιA      e z η (lift x≈z) =
      let
        B[η+[ε-δ]]yδ,ιz : fst (By δ) (η +₊ (ε -₊ δ , Δ)) (ι z)
        B[η+[ε-δ]]yδ,ιz = fst (Bιx≈ᴮ[ε-δ]Byδ η (ι z)) (lift x≈z)


        B[η+ε-δ]yδ,ιz = substBall {B = fst (By δ)} {y = ι z}
          (ℚ.+Assoc ⟨ η ⟩₊ ⟨ ε ⟩₊ _)
          B[η+[ε-δ]]yδ,ιz
      in
        ∣ δ , <≤ℚ![ Δ  ] , B[η+ε-δ]yδ,ιz ∣₁
    limA    e z zc Bx,z→Blimy,z η = PT.map λ (θ , θ<η , B[η-θ]x,zθ) →
      let

        B[η-θ+ε-δ]yδ,zθ : fst (By δ) ([ η -₊ θ ]⟨ θ<η ⟩ +₊ (ε -₊ δ , Δ)) (z θ)
        B[η-θ+ε-δ]yδ,zθ = fst (Bιx≈ᴮ[ε-δ]Byδ [ η -₊ θ ]⟨ θ<η ⟩ (z θ)) B[η-θ]x,zθ

      in
        δ , θ , <≤ℚ![ θ<η  ][ Δ ] , substBall {B = fst (By δ)} {y = z θ}
          ℚ!!
          B[η-θ+ε-δ]yδ,zθ
    isPropA e z = isPropΠ λ η → isProp→ (isPropBall (snd B⟨limᴿ[ By , Byc ],⟩) (η +₊ ε) z)

  B⟨lim,⟩→B⟨ι,⟩ : ∀ z η → B[ η ]⟨limᴿ[ By , Byc ], z ⟩ → B[ η +₊ ε ]⟨ι x , z ⟩
  B⟨lim,⟩→B⟨ι,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ η → B[ η ]⟨limᴿ[ By , Byc ], z ⟩ → B[ η +₊ ε ]⟨ι x , z ⟩
    ιA      e z η = PT.rec (isPropBall (snd B⟨ι x ,⟩) (η +₊ ε) (ι z))
      λ (θ , θ<η , B[η-θ]yθ,z) →
      let
        η-θ : ℚ₊
        η-θ = [ η -₊ θ ]⟨ θ<η ⟩

        B[η-θ]yθ,z' : fst (By θ) η-θ (ι z)
        B[η-θ]yθ,z' = B[η-θ]yθ,z

        B[η-θ+θ+δ]yδ,z : fst (By δ) (η-θ +₊ (θ +₊ δ)) (ι z)
        B[η-θ+θ+δ]yδ,z = fst (Byc θ δ η-θ (ι z)) B[η-θ]yθ,z'

        B[η-θ+θ+δ+ε-δ]x,z : B[ η-θ +₊ (θ +₊ δ) +₊ (ε -₊ δ , Δ) ]⟨ι x , ι z ⟩
        B[η-θ+θ+δ+ε-δ]x,z =
          snd (Bιx≈ᴮ[ε-δ]Byδ (η-θ +₊ (θ +₊ δ)) (ι z)) B[η-θ+θ+δ]yδ,z
      in
      substℚ₊ {P = λ ρ → B[ ρ ]⟨ι x , ι z ⟩}
        ℚ!!
        B[η-θ+θ+δ+ε-δ]x,z
      
    limA    e z zc Blimy,z→Bx,z η = PT.map λ (ζ , ξ , ζ+ξ<η , B[η-[ζ+ξ]]yζ,zξ) →
      let
        ε-δ = (ε -₊ δ , Δ) ; η-[ζ+ξ] = [ η -₊ (ζ +₊ ξ) ]⟨ ζ+ξ<η ⟩

        B[η-[ζ+ξ]+ζ+δ]yδ,zξ : fst (By δ) (η-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ)
        B[η-[ζ+ξ]+ζ+δ]yδ,zξ =
          fst (Byc ζ δ η-[ζ+ξ] (z ξ))
            B[η-[ζ+ξ]]yζ,zξ 

        B[η-[ζ+ξ]+ζ+δ+ε-δ]x,zξ : B[ η-[ζ+ξ] +₊ (ζ +₊ δ) +₊ ε-δ ]⟨ι x , z ξ ⟩
        B[η-[ζ+ξ]+ζ+δ+ε-δ]x,zξ =
          snd (Bιx≈ᴮ[ε-δ]Byδ (η-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ))
            B[η-[ζ+ξ]+ζ+δ]yδ,zξ


        B[η+ε-ξ]x,zξ = substℚ₊ {P = λ ρ → B[ ρ ]⟨ι x , z ξ ⟩}
          ℚ!!
          B[η-[ζ+ξ]+ζ+δ+ε-δ]x,zξ

      in
        ξ , <≤ℚ![ ζ+ξ<η ][ Δ ] , B[η+ε-ξ]x,zξ
    isPropA e z = isPropΠ λ η → isProp→ (isPropBall (snd B⟨ι x ,⟩) (η +₊ ε) z)

  B⟨ι,⟩≈ᴮB⟨lim,⟩ : B⟨ι x ,⟩ ≈ᴮ[ ε ] B⟨limᴿ[ By , Byc ],⟩
  B⟨ι,⟩≈ᴮB⟨lim,⟩ η z .fst = B⟨ι,⟩→B⟨lim,⟩ z η
  B⟨ι,⟩≈ᴮB⟨lim,⟩ η z .snd = B⟨lim,⟩→B⟨ι,⟩ z η

module _
  (Bx By : ℚ₊ → Balls) (ε δ η : ℚ₊)
  (Bxc : ∀ α β → (Bx α) ≈ᴮ[ α +₊ β ] (Bx β))
  (Byc : ∀ α β → (By α) ≈ᴮ[ α +₊ β ] (By β))
  (Δ : 0 <ℚ (ε -₊ (δ +₊ η)))
  (Bxδ≈[ε-[δ+η]]Byη : (Bx δ) ≈ᴮ[ ε -₊ (δ +₊ η) , Δ ] (By η))
  where

  open IsBall

  B⟨lim,⟩→B⟨lim,⟩ : ∀ z θ → B[ θ ]⟨limᴿ[ Bx , Bxc ], z ⟩ → B[ θ +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
  B⟨lim,⟩→B⟨lim,⟩ = Elimℭ-Prop.go e where
    open Elimℭ-Prop

    e : Elimℭ-Prop λ z → ∀ θ → B[ θ ]⟨limᴿ[ Bx , Bxc ], z ⟩ → B[ θ +₊ ε ]⟨limᴿ[ By , Byc ], z ⟩
    ιA      e z θ = PT.map λ (ζ , ζ<θ , B[θ-ζ]xζ,z) →
      let
        ε-[δ+η] = (ε -₊ (δ +₊ η) , Δ) ; θ-ζ = [ θ -₊ ζ ]⟨ ζ<θ ⟩

        B[θ-ζ+ζ+δ]xδ,z : fst (Bx δ) (θ-ζ +₊ (ζ +₊ δ)) (ι z)
        B[θ-ζ+ζ+δ]xδ,z = fst (Bxc ζ δ θ-ζ (ι z))
          (B[θ-ζ]xζ,z)

        B[θ-ζ+ζ+δ+ε-[δ+η]]yη,z : fst (By η) (θ-ζ +₊ (ζ +₊ δ) +₊ ε-[δ+η]) (ι z)
        B[θ-ζ+ζ+δ+ε-[δ+η]]yη,z =
          fst (Bxδ≈[ε-[δ+η]]Byη (θ-ζ +₊ (ζ +₊ δ)) (ι z))
            B[θ-ζ+ζ+δ]xδ,z

    

      in
        η , <≤ℚ![ Δ ] , substBall {B = fst (By η)} {y = ι z}
          ℚ!!
          B[θ-ζ+ζ+δ+ε-[δ+η]]yη,z
    limA    e z zc _ θ = PT.map λ (ζ , ξ , ζ+ξ<θ , B[θ-[ζ+ξ]]xζ,zξ) →
      let

        θ-[ζ+ξ] : ℚ₊
        θ-[ζ+ξ] = [ θ -₊ (ζ +₊ ξ) ]⟨ ζ+ξ<θ ⟩



        B[θ-[ζ+ξ]+ζ+δ]xδ,zξ = fst (Bxc ζ δ θ-[ζ+ξ] (z ξ))
          (B[θ-[ζ+ξ]]xζ,zξ)


        B[θ-[ζ+ξ]+ζ+δ+ε-[δ+η]]yη,zξ =
          fst (Bxδ≈[ε-[δ+η]]Byη (θ-[ζ+ξ] +₊ (ζ +₊ δ)) (z ξ))
            B[θ-[ζ+ξ]+ζ+δ]xδ,zξ


        B[θ+ε-[η+ξ]]yη,zξ = substBall {B = fst (By η)} {y = z ξ}
          ℚ!!
          B[θ-[ζ+ξ]+ζ+δ+ε-[δ+η]]yη,zξ

      in
        η , ξ , <≤ℚ![ ζ+ξ<θ ][ Δ ] , B[θ+ε-[η+ξ]]yη,zξ
    isPropA e z = isPropΠ λ θ → isProp→ (isPropBall (snd B⟨limᴿ[ By , Byc ],⟩) (θ +₊ ε) z)

private
  B⟨lim,⟩≈B⟨lim,⟩ : ∀ Bx By ε δ η Bxc Byc Δ
                   → (Bx δ) ≈ᴮ[ ε -₊ (δ +₊ η) , Δ ] (By η)
                   → B⟨limᴿ[ Bx , Bxc ],⟩ ≈ᴮ[ ε ] B⟨limᴿ[ By , Byc ],⟩
  B⟨lim,⟩≈B⟨lim,⟩ Bx By ε δ η Bxc Byc Δ Bxδ≈[ε-[δ+η]]Byη θ z .fst =
    B⟨lim,⟩→B⟨lim,⟩ Bx By ε δ η Bxc Byc Δ Bxδ≈[ε-[δ+η]]Byη z θ
  B⟨lim,⟩≈B⟨lim,⟩ Bx By ε δ η Bxc Byc Δ Bxδ≈[ε-[δ+η]]Byη θ z .snd =
    B⟨lim,⟩→B⟨lim,⟩ By Bx ε η δ Byc Bxc _ Byη≈[ε-[η+δ]]Bxδ z θ
    where

      Byη≈[ε-[η+δ]]Bxδ : (By η) ≈ᴮ[ ε -₊ (η +₊ δ) , <≤ℚ![ Δ ] ] (Bx δ)
      Byη≈[ε-[η+δ]]Bxδ = subst ((By η) ≈ᴮ[_] (Bx δ)) (ℚ₊≡ ℚ!!)
        (isSym≈ᴮ (Bx δ) (By η) (ε -₊ (δ +₊ η) , Δ) Bxδ≈[ε-[δ+η]]Byη)


BallsAt[Rec] : RecℭSym Balls (flip ∘ _≈ᴮ[_]_)
ιA        BallsAt[Rec] = B⟨ι_,⟩
limA      BallsAt[Rec] = B⟨limᴿ[_,_],⟩
eqA       BallsAt[Rec] = isSeparated≈ᴮ
ι-ι-B     BallsAt[Rec] = makeOpaque B⟨ι,⟩≈ᴮB⟨ι,⟩
ι-lim-B   BallsAt[Rec] = makeOpaque B⟨ι,⟩≈ᴮB⟨lim,⟩
lim-lim-B BallsAt[Rec] = makeOpaque B⟨lim,⟩≈B⟨lim,⟩
isSymB    BallsAt[Rec] = isSym≈ᴮ
isPropB   BallsAt[Rec] = isProp≈ᴮ


-- Defintion 3.13 (second part)
opaque
  B⟨_,⟩ : ℭM → Balls
  B⟨_,⟩ = RecℭSym.go BallsAt[Rec]

  B[_]⟨_,_⟩ : ℚ₊ → ℭM → ℭM → Type (ℓ-max ℓ ℓ')
  B[_]⟨_,_⟩ = flip (fst ∘ B⟨_,⟩)

  isNonExpanding∼→≈ᴮB⟨,⟩ : nonExpanding∼→≈ᴮ B⟨_,⟩
  isNonExpanding∼→≈ᴮB⟨,⟩ = λ _ _ _ → RecℭSym.go∼ BallsAt[Rec]

-- -- Theorem 3.14
-- -- {-
--   _ : ∀ {ε x y} → B[ ε ]⟨ ι x , ι y ⟩ ≡ Lift {ℓ'} ℓ (x ≈[ ε ] y)
--   _ = refl

--   _ : ∀ {ε x y yc}
--       → B[ ε ]⟨ ι x , lim y yc ⟩
--       ≡ (∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] B[ (-₊< ε δ δ<ε .fst) , (-₊< ε δ δ<ε .snd) ]⟨ ι x , y δ ⟩)
--   _ = refl

--   _ : ∀ {ε x y xc}
--       → B[ ε ]⟨ lim x xc , ι y ⟩
--       ≡ (∃[ δ ∈ ℚ₊ ] Σ[ δ<ε ∈ (δ <₊ ε) ] B[ (-₊< ε δ δ<ε .fst) , (-₊< ε δ δ<ε .snd) ]⟨ x δ , ι y ⟩)
--   _ = refl

--   _ : ∀ {ε x y xc yc}
--       → B[ ε ]⟨ lim x xc , lim y yc ⟩
--       ≡ (∃[ δ ∈ ℚ₊ ] Σ[ η ∈ ℚ₊ ] Σ[ δ+η<ε ∈ ((δ +₊ η) <₊ ε) ]
--           B[ (-₊< ε (δ +₊ η) δ+η<ε .fst) , (-₊< ε (δ +₊ η) δ+η<ε .snd) ]⟨ x δ , y η ⟩)
--   _ = refl
-- -- -}

  ∼→B : ∀ {x y ε} → x ∼[ ε ] y → B[ ε ]⟨ x , y ⟩
  ∼→B =  (Recℭ∼.go∼ r) where
    r : Recℭ∼ λ x y → B[_]⟨ x , y ⟩
    Recℭ∼.ι-ι-B     r x y ε = lift
    Recℭ∼.ι-lim-B   r x y ε δ yc Δ _ q      =
      ∣ δ , 0<Δ→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ , subst B[_]⟨ ι x , y δ ⟩ (ℚ₊≡ refl) q ∣₁
    Recℭ∼.lim-ι-B   r x y ε δ xc Δ _ q      =
      ∣ δ , 0<Δ→< ⟨ δ ⟩₊ ⟨ ε ⟩₊ Δ , subst B[_]⟨ x δ , ι y ⟩ (ℚ₊≡ refl) q ∣₁
    Recℭ∼.lim-lim-B r x y ε δ η xc yc Δ _ q =
      ∣ δ , η , 0<Δ→< ⟨ δ +₊ η ⟩₊ ⟨ ε ⟩₊ Δ , subst B[_]⟨ x δ , y η ⟩ (ℚ₊≡ refl) q ∣₁
    Recℭ∼.isPropB   r x y ε                 = IsBall.isPropBall (snd B⟨ x ,⟩) ε y


  B→∼ : ∀ {x y ε} → B[ ε ]⟨ x , y ⟩ → x ∼[ ε ] y
  B→∼ {x} {y} {ε} = Elimℭ-Prop2.go e x y ε where
    open Elimℭ-Prop2

    e : Elimℭ-Prop2 λ x y → ∀ ε → B[ ε ]⟨ x , y ⟩ → x ∼[ ε ] y
    ι-ιA     e x y ε (lift x≈y) = ι-ι x y ε x≈y
    ι-limA   e x y yc IH ε = PT.rec (isProp∼ (ι x) ε (lim y yc))
      λ (δ , δ<ε , B[ε-δ]x,yδ) →
        ι-lim x y ε δ yc _ (IH δ (ε -₊ δ , _) B[ε-δ]x,yδ)
    lim-ιA   e x xc y IH ε = PT.rec (isProp∼ (lim x xc) ε (ι y))
      λ (δ , δ<ε , B[ε-δ]xδ,y) →
        lim-ι x y ε δ xc _ (
          IH δ (ε -₊ δ , _) B[ε-δ]xδ,y)
    lim-limA e x xc y yc IH ε = PT.rec (isProp∼ (lim x xc) ε (lim y yc))
      λ (δ , η , δ+η<ε , B[ε-[δ+η]]xδ,yη) →
        lim-lim x y ε δ η xc yc _ (
          IH δ η (ε -₊ (δ +₊ η) , _) B[ε-[δ+η]]xδ,yη)

    isPropA  e x y = isPropΠ λ ε → isProp→ (isProp∼ x ε y)

  -- Theorem 3.15
  ∼≃B : ∀ {x y ε} → (x ∼[ ε ] y) ≃ B[ ε ]⟨ x , y ⟩
  ∼≃B {x} {y} {ε} =
    propBiimpl→Equiv (isProp∼ x ε y) (IsBall.isPropBall (snd B⟨ x ,⟩) ε y) ∼→B B→∼

  isTriangular∼ : ∀ x y z ε δ → x ∼[ ε ] y → y ∼[ δ ] z → x ∼[ ε +₊ δ ] z
  isTriangular∼ x y z ε δ x∼y y∼z =
    (B→∼ (isTriangularBall (snd B⟨ x ,⟩) ε δ y z (∼→B x∼y) y∼z))
    where open IsBall

  _▴_ : ∀ {x y z ε δ} → x ∼[ ε ] y → y ∼[ δ ] z → x ∼[ ε +₊ δ ] z
  _▴_ = isTriangular∼ _ _ _ _ _
  
  isRounded∼ : ∀ x y ε → x ∼[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × x ∼[ δ ] y
  isRounded∼ x y ε x∼y = PT.map (λ (δ , δ<ε , B[δ]x,y) → (δ , δ<ε , B→∼ B[δ]x,y))
    (isRoundedBall (snd B⟨ x ,⟩) ε y (∼→B x∼y))
    where open IsBall

  -- Theorem 3.17
  isInjectiveι : ∀ x y → ι x ≡ ι y → x ≡ y
  isInjectiveι x y ιx≡ιy = isSeparated≈ x y λ ε →
    ∼→B (subst (ι x ∼[ ε ]_) ιx≡ιy (isRefl∼ (ι x) ε)) .lower

-- Theorem 3.16
ℭPremetricSpace : PremetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
fst ℭPremetricSpace = ℭM
PremetricStr._≈[_]_      (snd ℭPremetricSpace) = _∼[_]_
PremetricStr.isPremetric (snd ℭPremetricSpace) = isPMℭ
  where opaque
    open IsPremetric

    isPMℭ : IsPremetric _∼[_]_
    isSetM        isPMℭ = isSetℭ
    isProp≈       isPMℭ = flip ∘ isProp∼
    isRefl≈       isPMℭ = isRefl∼
    isSym≈        isPMℭ = isSym∼
    isSeparated≈  isPMℭ = eqℭ
    isTriangular≈ isPMℭ = isTriangular∼
    isRounded≈    isPMℭ = isRounded∼

isLimitLim : ∀ x xc → isLimit ℭPremetricSpace x (lim x xc)
isLimitLim x xc ε θ = Elimℭ-Prop.go e (x ε) x xc ε θ (isRefl∼ (x ε) θ) where 
  open Elimℭ-Prop

  e : Elimℭ-Prop λ u → ∀ x xc ε θ → u ∼[ θ ] (x ε) → u ∼[ ε +₊ θ ] lim x xc
  ιA      e u x xc ε θ =
    subst∼ _ _ (ℚ.+Comm ⟨ θ ⟩₊ ⟨ ε ⟩₊) ∘ ι-lim+₊ u x θ ε xc
  limA    e u uc IH x xc ε θ limu∼[θ]xε = PT.rec
    (isProp∼ (lim u uc) (ε +₊ θ) (lim x xc))
    ((λ (δ , (δ<θ , limu∼[δ]xε)) →
    let η = [ θ -₊ δ ]⟨ δ<θ ⟩ /4₊        
    in lim-lim u x (ε +₊ θ) η ε uc xc <≤ℚ! (
        subst∼ (u η) (x ε) ℚ!! ((IH η u uc _ _ (uc η η)) ▴ limu∼[δ]xε))))
    (isRounded∼ (lim u uc) (x ε) θ limu∼[θ]xε)
  isPropA e u = isPropΠ4 λ _ _ _ _ → isProp→ (isProp∼ _ _ _)

-- Theorem 3.18
isCompleteℭ : isComplete ℭPremetricSpace
isCompleteℭ x xc = lim x xc , isLimitLim x xc
