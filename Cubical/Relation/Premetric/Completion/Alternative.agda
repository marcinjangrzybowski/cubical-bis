open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative {ℓ} {ℓ'}
  (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Binary.Properties

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚProp

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

private
  M = M' .fst
  open PremetricStr (M' .snd)
  open import Cubical.Relation.Premetric.Completion.Base M'
    renaming (ℭ to ℭM)

-- Keep all existing results about the regular completion available while
-- developing the alternative one, without mixing their names with the
-- hatted constructors.
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularCloseness
import Cubical.Relation.Premetric.Completion.Properties.Approximations
  as RegularApproximations
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as RegularLift
import Cubical.Relation.Premetric.Properties as PremetricProperties
import Cubical.Relation.Premetric.Completion.Base as RegularBaseDefinition

module Regular = RegularCloseness M'
module RegularPremetric = PremetricStr (Regular.ℭPremetricSpace .snd)
module RegularTheory = PremetricProperties.PremetricTheory Regular.ℭPremetricSpace
module RegularBase = RegularBaseDefinition M'

open import Cubical.Relation.Premetric.Completion.Elim M'

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  reassociate4₊ : ∀ (a b c d : ℚ₊) →
    fst (a +₊ (b +₊ (c +₊ d))) ≡ fst ((a +₊ d) +₊ (b +₊ c))
  reassociate4₊ a b c d =
      cong (λ q → fst a ℚProp.+ (fst b ℚProp.+ q))
        (ℚProp.+Comm (fst c) (fst d))
    ∙ cong (λ q → fst a ℚProp.+ q)
        (ℚRing.+Assoc-comm1 (fst b) (fst d) (fst c))
    ∙ ℚProp.+Assoc (fst a) (fst d) (fst b ℚProp.+ fst c)

  reassociateMinus : ∀ (ε a b : ℚ₊) →
    (fst ε ℚProp.- fst (a +₊ b)) ≡
    ((fst ε ℚProp.- fst a) ℚProp.- fst b)
  reassociateMinus ε a b =
      cong (λ q → fst ε ℚProp.+ q)
        (ℚProp.-Distr (fst a) (fst b))
    ∙ ℚProp.+Assoc
        (fst ε) (ℚProp.-_ (fst a)) (ℚProp.-_ (fst b))

  recoverOuterMinus : ∀ (ε a b : ℚ₊) →
    ((fst ε ℚProp.- fst (a +₊ b)) ℚProp.+ fst b) ≡
    (fst ε ℚProp.- fst a)
  recoverOuterMinus ε a b =
      cong (λ q → q ℚProp.+ fst b) (reassociateMinus ε a b)
    ∙ ℚRing.minusPlus (fst ε ℚProp.- fst a) (fst b)

  recoverNestedMinus₊ : ∀ (base κ δ ε : ℚ₊) (κ<base : κ <₊ base)
    → fst base ℚProp.+ fst δ ≡ fst ε
    → fst ([ base -₊ κ ]⟨ κ<base ⟩ +₊ (κ +₊ δ)) ≡ fst ε
  recoverNestedMinus₊ base κ δ ε κ<base base+δ≡ε =
      ℚProp.+Assoc
        (fst [ base -₊ κ ]⟨ κ<base ⟩) (fst κ) (fst δ)
    ∙ cong (λ q → q ℚProp.+ fst δ) (minusPlus₊ base κ)
    ∙ base+δ≡ε



private
  closeToLimit : ∀ (u v : ℭM) (Y : ℚ₊ → ℭM) (g : Γ) ε δ Δ
    → (Yc : ∀ θ κ → Y θ ∼[ θ +₊ κ ] Y κ)
    → u ∼[ ε -₊ g .γ δ , Δ ] v
    → (∀ θ → v ∼[ g .γ δ +₊ g .γ (g .τ θ) ] Y θ)
    → u ∼[ ε ] lim Y Yc
  closeToLimit u v Y g ε δ Δ Yc u∼v bridge =
    PT.rec (RegularPremetric.isProp≈ _ _ ε) step
      (Regular.isRounded∼ _ _ _ u∼v)
    where
    step : Σ[ κ ∈ ℚ₊ ] (κ <₊ (ε -₊ g .γ δ , Δ)) × (u ∼[ κ ] v)
         → u ∼[ ε ] lim Y Yc
    step (κ , κ<ε-γδ , u∼κv) =
      let gap = [ (ε -₊ g .γ δ , Δ) -₊ κ ]⟨ κ<ε-γδ ⟩
          θ = gap /4₊
          γτθ≤θ = g .γ∘τ≤id θ
          v∼Yθ = bridge θ
          u∼Yθ = RegularPremetric.isTriangular≈ _ _ _ _ _ u∼κv v∼Yθ
          u∼lim = RegularTheory.isLim≈+ u Y (lim Y Yc) θ _
            (Regular.isLimitLim Y Yc) u∼Yθ
          θ+θ<gap : fst (θ +₊ θ) <ℚ fst gap
          θ+θ<gap = begin<
            fst (θ +₊ θ) ≡→≤⟨ /4+/4≡/2 (fst gap) ⟩
            fst (gap /2₊) <⟨ /2₊<id gap ⟩
            fst gap ◾
          gap+κ+γδ≡ε : fst (gap +₊ (κ +₊ g .γ δ)) ≡ fst ε
          gap+κ+γδ≡ε = recoverNestedMinus₊
            (ε -₊ g .γ δ , Δ) κ (g .γ δ) ε κ<ε-γδ
            (minusPlus₊ ε (g .γ δ))
          inner-radius≤ :
            fst (g .γ δ +₊ g .γ (g .τ θ)) ≤ℚ fst (g .γ δ +₊ θ)
          inner-radius≤ = +MonoL≤
            (fst (g .γ (g .τ θ))) (fst θ) (fst (g .γ δ)) γτθ≤θ
          middle-radius≤ :
            fst (κ +₊ (g .γ δ +₊ g .γ (g .τ θ)))
            ≤ℚ fst (κ +₊ (g .γ δ +₊ θ))
          middle-radius≤ = +MonoL≤
            (fst (g .γ δ +₊ g .γ (g .τ θ)))
            (fst (g .γ δ +₊ θ)) (fst κ) inner-radius≤
          raw-radius≤ :
            fst (θ +₊ (κ +₊ (g .γ δ +₊ g .γ (g .τ θ))))
            ≤ℚ fst (θ +₊ (κ +₊ (g .γ δ +₊ θ)))
          raw-radius≤ = +MonoL≤
            (fst (κ +₊ (g .γ δ +₊ g .γ (g .τ θ))))
            (fst (κ +₊ (g .γ δ +₊ θ))) (fst θ) middle-radius≤
          radius≤ :
            fst (θ +₊ (κ +₊ (g .γ δ +₊ g .γ (g .τ θ))))
            ≤ℚ fst ((θ +₊ θ) +₊ (κ +₊ g .γ δ))
          radius≤ = subst
            (fst (θ +₊ (κ +₊ (g .γ δ +₊ g .γ (g .τ θ)))) ≤ℚ_)
            (reassociate4₊ θ κ (g .γ δ) θ) raw-radius≤
          radius<ε : fst (θ +₊ (κ +₊ (g .γ δ +₊ g .γ (g .τ θ)))) <ℚ fst ε
          radius<ε = begin<
            fst (θ +₊ (κ +₊ (g .γ δ +₊ g .γ (g .τ θ))))
              ≤⟨ radius≤ ⟩
            fst ((θ +₊ θ) +₊ (κ +₊ g .γ δ))
              <⟨ θ+θ<gap <+[ fst (κ +₊ g .γ δ) ] ⟩
            fst (gap +₊ (κ +₊ g .γ δ))
              ≡→≤⟨ gap+κ+γδ≡ε ⟩
            fst ε ◾
      in RegularPremetric.isMonotone≈< _ _ _ ε radius<ε u∼lim


data ℭ̂ : Type (ℓ-max ℓ ℓ')
data _∼̂[_]_ : ℭ̂ → ℚ₊ → ℭ̂ → Type (ℓ-max ℓ ℓ')


data ℭ̂ where
  ι   : M → ℭ̂
  lim : (x : ℚ₊ → ℭ̂) (g : Γ)
        → (∀ ε δ → x ε ∼̂[ (g .γ ε) +₊ (g .γ δ) ] x δ)
        → ℭ̂
  eqℭ : ∀ x y → (∀ ε → x ∼̂[ ε ] y) → x ≡ y

data _∼̂[_]_ where
  ι-ι     : ∀ x y ε → x ≈[ ε ] y → ι x ∼̂[ ε ] ι y
  ι-lim   : ∀ x y g ε δ yc Δ
            → ι x ∼̂[ ε -₊ (g .γ δ) , Δ ] y δ
            → ι x ∼̂[ ε ] lim y g yc
  lim-ι   : ∀ x g y ε δ xc Δ
            → x δ ∼̂[ ε -₊ (g .γ δ) , Δ ] ι y
            → lim x g xc ∼̂[ ε ] ι y
  lim-lim : ∀ x g y g' ε δ η xc yc Δ
            → x δ ∼̂[ ε -₊ ((g .γ δ) +₊ (g' .γ η)) , Δ ] y η
            → lim x g xc ∼̂[ ε ] lim y g' yc
  isProp∼ : ∀ x ε y → isProp (x ∼̂[ ε ] y)

private
  ℭ̂M = ℭ̂


→̂ : ℭM → ℭ̂M
→̂~ : ∀ x y ε → x ∼[ ε ] y → →̂ x ∼̂[ ε ] →̂ y

→̂ (ι x) = ι x
→̂ (lim x xc) = lim (λ ε → →̂ (x ε)) Γid λ ε δ →
  →̂~ (x ε) (x δ) (ε +₊ δ) (xc ε δ)
→̂ (eqℭ x y x~y i) =
  eqℭ (→̂ x) (→̂ y) (λ ε → →̂~ x y ε (x~y ε)) i

→̂~ x y ε (ι-ι x' y' ε' x≈y) = ι-ι x' y' ε' x≈y
→̂~ x y ε (ι-lim x' y' ε' δ yc Δ r) =
  ι-lim _ _ _ _ _ _ _ (→̂~ _ _ _ r)
→̂~ x y ε (lim-ι x' y' ε' δ xc Δ r) =
  lim-ι _ _ _ _ _ _ _ (→̂~ _ _ _ r)
→̂~ x y ε (lim-lim x' y' ε' δ η xc yc Δ r) =
  lim-lim _ _ _ _ _ _ _ _ _ _ (→̂~ _ _ _ r)
→̂~ x y ε (isProp∼ x' ε' y' p q i) =
  isProp∼ (→̂ x') ε (→̂ y') (→̂~ x y ε p) (→̂~ x y ε q) i


←̂ : ℭ̂M → ℭM
←̂~ : ∀ x y ε → x ∼̂[ ε ] y → ←̂ x ∼[ ε ] ←̂ y
←̂Cauchy : ∀ x g
  → (xc : ∀ ε δ → x ε ∼̂[ g .γ ε +₊ g .γ δ ] x δ)
  → ∀ ε δ → ←̂ (x (g .τ ε)) ∼[ ε +₊ δ ] ←̂ (x (g .τ δ))

←̂ (ι x) = ι x
←̂ (lim x g xc) =
  lim (λ ε → ←̂ (x (g .τ ε))) (←̂Cauchy x g xc)
←̂ (eqℭ x y x~y i) = eqℭ (←̂ x) (←̂ y) (λ ε → ←̂~ x y ε (x~y ε)) i

←̂Cauchy x g xc ε δ =
  let z = ←̂~ (x (g .τ ε)) (x (g .τ δ)) _ (xc (g .τ ε) (g .τ δ))
      γε≤ε = g .γ∘τ≤id ε
      γδ≤δ = g .γ∘τ≤id δ
      radius≤ : fst (g .γ (g .τ ε) +₊ g .γ (g .τ δ)) ≤ℚ fst (ε +₊ δ)
      radius≤ = +Mono≤ _ _ _ _ γε≤ε γδ≤δ
  in RegularPremetric.isMonotone≈≤ _ _ _ _ radius≤ z

←̂~ x y ε (ι-ι x' y' ε' x≈y) = ι-ι x' y' ε' x≈y
←̂~ x y ε (ι-lim x' y' g ε' δ yc Δ r) =
  closeToLimit (ι x') (←̂ (y' δ)) Y g ε δ Δ Yc
    (←̂~ _ _ _ r) (λ θ → ←̂~ _ _ _ (yc δ (g .τ θ)))
  where
  Y : ℚ₊ → ℭM
  Y θ = ←̂ (y' (g .τ θ))

  Yc : ∀ θ κ → Y θ ∼[ θ +₊ κ ] Y κ
  Yc = ←̂Cauchy y' g yc
←̂~ x y ε (lim-ι x' g y' ε' δ xc Δ r) =
  RegularPremetric.isSym≈ _ _ ε
    (closeToLimit (ι y') (←̂ (x' δ)) X g ε δ Δ Xc
      (RegularPremetric.isSym≈ _ _ _ (←̂~ _ _ _ r))
      (λ θ → ←̂~ _ _ _ (xc δ (g .τ θ))))
  where
  X : ℚ₊ → ℭM
  X θ = ←̂ (x' (g .τ θ))

  Xc : ∀ θ κ → X θ ∼[ θ +₊ κ ] X κ
  Xc = ←̂Cauchy x' g xc
←̂~ x y ε (lim-lim x' g y' g' ε' δ η xc yc Δ r) =
  let α = g .γ δ
      β = g' .γ η
      Δα : OrderedCommRingStr.0r (snd ℚOrderedCommRing) <ℚ (ε -₊ α)
      Δα = subst
        (λ q → OrderedCommRingStr.0r (snd ℚOrderedCommRing) <ℚ q)
        (recoverOuterMinus ε α β)
        (PositiveRationals.0<+Closed
          (ε -₊ (α +₊ β)) (fst β) Δ (snd β))
      ε-α = (ε -₊ α , Δα)
      Δβ : OrderedCommRingStr.0r (snd ℚOrderedCommRing) <ℚ (ε-α -₊ β)
      Δβ = subst
        (λ q → OrderedCommRingStr.0r (snd ℚOrderedCommRing) <ℚ q)
        (reassociateMinus ε α β) Δ
      z = ←̂~ _ _ _ r
      z' = RegularPremetric.subst≈ _ _ (reassociateMinus ε α β) z
      xδ∼limY = closeToLimit (←̂ (x' δ)) (←̂ (y' η)) Y g' ε-α η Δβ Yc z'
        (λ θ → ←̂~ _ _ _ (yc η (g' .τ θ)))
      limY∼limX = closeToLimit (lim Y Yc) (←̂ (x' δ)) X g ε δ Δα Xc
        (RegularPremetric.isSym≈ _ _ _ xδ∼limY)
        (λ θ → ←̂~ _ _ _ (xc δ (g .τ θ)))
  in RegularPremetric.isSym≈ _ _ ε limY∼limX
  where
  X : ℚ₊ → ℭM
  X θ = ←̂ (x' (g .τ θ))

  Xc : ∀ θ κ → X θ ∼[ θ +₊ κ ] X κ
  Xc = ←̂Cauchy x' g xc

  Y : ℚ₊ → ℭM
  Y θ = ←̂ (y' (g' .τ θ))

  Yc : ∀ θ κ → Y θ ∼[ θ +₊ κ ] Y κ
  Yc = ←̂Cauchy y' g' yc
←̂~ x y ε (isProp∼ x' ε' y' p q i) =
  isProp∼ (←̂ x') ε (←̂ y') (←̂~ x y ε p) (←̂~ x y ε q) i



record Elimℭ̂
  {ℓA} {ℓB} (A : ℭ̂M → Type ℓA)
  (B : ∀ {x y : ℭ̂M} → A x → A y → ∀ ε → x ∼̂[ ε ] y → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : ∀ x → A (ι x)
    limA      : ∀ x g xc → (a∘x : ∀ q → A (x q))
                → (∀ ε δ → B
                    {x ε} {x δ}
                    (a∘x ε) (a∘x δ)
                    (g .γ ε +₊ g .γ δ) (xc ε δ))
                → A (lim x g xc)
    eqA       : ∀ {x y} p a a' → (∀ ε δ → B a a' _ (p (ε +₊ δ)))
                → (∀ ε → B a a' ε (p ε))
                → PathP (λ i → A (eqℭ x y p i)) a a'
    ι-ι-B     : ∀ x y ε x≈y → B (ιA x) (ιA y) ε (ι-ι x y ε x≈y)
    ι-lim-B   : ∀ x y g ε δ yc Δ r a∘y ydc
                → B (ιA x) (a∘y δ) (ε -₊ g .γ δ , Δ) r
                → B (ιA x) (limA y g yc a∘y ydc) ε
                    (ι-lim x y g ε δ yc Δ r)
    lim-ι-B   : ∀ x g y ε δ xc Δ u a∘x xdc
                → B (a∘x δ) (ιA y) (ε -₊ g .γ δ , Δ) u
                → B (limA x g xc a∘x xdc) (ιA y) ε
                    (lim-ι x g y ε δ xc Δ u)
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
                → (r : x δ ∼̂[ ε -₊ (g .γ δ +₊ g' .γ η) , Δ ] y η)
                → ∀ a∘x xdc a∘y ydc
                → B (a∘x δ) (a∘y η)
                    (ε -₊ (g .γ δ +₊ g' .γ η) , Δ) r
                → B (limA x g xc a∘x xdc) (limA y g' yc a∘y ydc) ε
                    (lim-lim x g y g' ε δ η xc yc Δ r)
    isPropB   : ∀ {x y} a a' ε u → isProp (B {x} {y} a a' ε u)

  go : ∀ x → A x
  go∼ : ∀ {x x' ε} → (r : x ∼̂[ ε ] x') → B (go x) (go x') ε r

  go (ι x) = ιA x
  go (lim x g xc) = limA x g xc (go ∘ x) λ ε δ → go∼ (xc ε δ)
  go (eqℭ x y x~y i) =
    eqA x~y (go x) (go y) (λ ε δ → go∼ (x~y (ε +₊ δ)))
      (λ ε → go∼ (x~y ε)) i

  go∼ (ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go∼ (ι-lim x y g ε δ yc Δ r) =
    ι-lim-B x y g ε δ yc Δ r
      (go ∘ y) (λ ε' → go∼ ∘ (yc ε')) (go∼ r)
  go∼ (lim-ι x g y ε δ xc Δ r) =
    lim-ι-B x g y ε δ xc Δ r
      (go ∘ x) (λ ε' → go∼ ∘ (xc ε')) (go∼ r)
  go∼ (lim-lim x g y g' ε δ η xc yc Δ r) =
    lim-lim-B x g y g' ε δ η xc yc Δ r
      (go ∘ x) (λ ε' → go∼ ∘ (xc ε'))
      (go ∘ y) (λ ε' → go∼ ∘ (yc ε')) (go∼ r)
  go∼ (isProp∼ x ε y p q i) =
    isProp→PathP (λ i → isPropB (go x) (go y) ε (isProp∼ x ε y p q i))
      (go∼ p) (go∼ q) i

  β-go-ι : ∀ q → go (ι q) ≡ ιA q
  β-go-ι _ = refl

  β-go-lim : ∀ x g xc → go (lim x g xc) ≡ limA x g xc _ _
  β-go-lim _ _ _ = refl


record Elimℭ̂∼
  {ℓB} (B : ∀ x y ε → x ∼̂[ ε ] y → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where

  no-eta-equality

  field
    ι-ι-B     : ∀ x y ε x≈y → B (ι x) (ι y) ε (ι-ι x y ε x≈y)
    ι-lim-B   : ∀ x y g ε δ yc Δ r
                → B (ι x) (y δ) (ε -₊ g .γ δ , Δ) r
                → B (ι x) (lim y g yc) ε (ι-lim x y g ε δ yc Δ r)
    lim-ι-B   : ∀ x g y ε δ xc Δ u
                → B (x δ) (ι y) (ε -₊ g .γ δ , Δ) u
                → B (lim x g xc) (ι y) ε (lim-ι x g y ε δ xc Δ u)
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
                → (r : x δ ∼̂[ ε -₊ (g .γ δ +₊ g' .γ η) , Δ ] y η)
                → B (x δ) (y η)
                    (ε -₊ (g .γ δ +₊ g' .γ η) , Δ) r
                → B (lim x g xc) (lim y g' yc) ε
                    (lim-lim x g y g' ε δ η xc yc Δ r)
    isPropB   : ∀ x y ε u → isProp (B x y ε u)

  go∼ : ∀ {x x' ε} → (r : x ∼̂[ ε ] x') → B x x' ε r
  go∼ (ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go∼ (ι-lim x y g ε δ yc Δ r) =
    ι-lim-B x y g ε δ yc Δ r (go∼ r)
  go∼ (lim-ι x g y ε δ xc Δ r) =
    lim-ι-B x g y ε δ xc Δ r (go∼ r)
  go∼ (lim-lim x g y g' ε δ η xc yc Δ r) =
    lim-lim-B x g y g' ε δ η xc yc Δ r (go∼ r)
  go∼ (isProp∼ x ε y p q i) =
    isProp→PathP (λ i → isPropB x y ε (isProp∼ x ε y p q i))
      (go∼ p) (go∼ q) i


record Elimℭ̂-Prop {ℓA} (A : ℭ̂M → Type ℓA)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ιA      : ∀ x → A (ι x)
    limA    : ∀ x g xc → (∀ q → A (x q)) → A (lim x g xc)
    isPropA : ∀ x → isProp (A x)

  go : ∀ x → A x
  go (ι x) = ιA x
  go (lim x g xc) = limA x g xc (go ∘ x)
  go (eqℭ x y x~y i) =
    isProp→PathP (λ j → isPropA (eqℭ x y x~y j)) (go x) (go y) i


record Elimℭ̂-Prop2 {ℓA} (A : ℭ̂M → ℭ̂M → Type ℓA)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ι-ιA     : ∀ x y → A (ι x) (ι y)
    ι-limA   : ∀ x y g yc → (∀ ε → A (ι x) (y ε)) → A (ι x) (lim y g yc)
    lim-ιA   : ∀ x g xc y → (∀ ε → A (x ε) (ι y)) → A (lim x g xc) (ι y)
    lim-limA : ∀ x g xc y g' yc → (∀ ε δ → A (x ε) (y δ))
                → A (lim x g xc) (lim y g' yc)
    isPropA  : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = Elimℭ̂-Prop.go e
    where
    e : Elimℭ̂-Prop (λ x → ∀ y → A x y)
    Elimℭ̂-Prop.ιA e x = Elimℭ̂-Prop.go e'
      where
      e' : Elimℭ̂-Prop (A (ι x))
      Elimℭ̂-Prop.ιA e' = ι-ιA x
      Elimℭ̂-Prop.limA e' = ι-limA x
      Elimℭ̂-Prop.isPropA e' = isPropA (ι x)
    Elimℭ̂-Prop.limA e x g xc a∘x = Elimℭ̂-Prop.go e'
      where
      e' : Elimℭ̂-Prop (A (lim x g xc))
      Elimℭ̂-Prop.ιA e' y = lim-ιA x g xc y (flip a∘x (ι y))
      Elimℭ̂-Prop.limA e' y g' yc a∘y =
        lim-limA x g xc y g' yc (λ ε → a∘x ε ∘ y)
      Elimℭ̂-Prop.isPropA e' = isPropA (lim x g xc)
    Elimℭ̂-Prop.isPropA e x = isPropΠ (isPropA x)


record Elimℭ̂-Prop2Sym {ℓA} (A : ℭ̂M → ℭ̂M → Type ℓA)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ι-ιA     : ∀ x y → A (ι x) (ι y)
    ι-limA   : ∀ x y g yc → (∀ ε → A (ι x) (y ε)) → A (ι x) (lim y g yc)
    lim-limA : ∀ x g xc y g' yc → (∀ ε δ → A (x ε) (y δ))
                → A (lim x g xc) (lim y g' yc)
    isSymA   : ∀ x y → A x y → A y x
    isPropA  : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = Elimℭ̂-Prop2.go e
    where
    e : Elimℭ̂-Prop2 A
    Elimℭ̂-Prop2.ι-ιA e = ι-ιA
    Elimℭ̂-Prop2.ι-limA e = ι-limA
    Elimℭ̂-Prop2.lim-ιA e = λ x g xc y r →
      isSymA (ι y) (lim x g xc)
        (ι-limA y x g xc (isSymA _ (ι y) ∘ r))
    Elimℭ̂-Prop2.lim-limA e = lim-limA
    Elimℭ̂-Prop2.isPropA e = isPropA


record Recℭ̂ {ℓA} {ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (a∘x : ℚ₊ → A) (g : Γ)
                → (∀ ε δ → B
                    (a∘x ε) (a∘x δ) (g .γ ε +₊ g .γ δ))
                → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y g ε δ yc Δ
                → B (ιA x) (y δ) (ε -₊ g .γ δ , Δ)
                → B (ιA x) (limA y g yc) ε
    lim-ι-B   : ∀ x g y ε δ xc Δ
                → B (x δ) (ιA y) (ε -₊ g .γ δ , Δ)
                → B (limA x g xc) (ιA y) ε
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
                → B (x δ) (y η)
                    (ε -₊ (g .γ δ +₊ g' .γ η) , Δ)
                → B (limA x g xc) (limA y g' yc) ε

    isPropB : ∀ a a' ε → isProp (B a a' ε)

  private
    e : Elimℭ̂ (λ _ → A) λ a a' ε _ → B a a' ε
    Elimℭ̂.ιA e = ιA
    Elimℭ̂.limA e _ g _ a∘x = limA a∘x g
    Elimℭ̂.eqA e _ a a' _ = eqA a a'
    Elimℭ̂.ι-ι-B e = ι-ι-B
    Elimℭ̂.ι-lim-B e x _ g ε δ _ Δ _ a∘y ydc =
      ι-lim-B x a∘y g ε δ ydc Δ
    Elimℭ̂.lim-ι-B e _ g y ε δ _ Δ _ a∘x xdc =
      lim-ι-B a∘x g y ε δ xdc Δ
    Elimℭ̂.lim-lim-B e _ g _ g' ε δ η _ _ Δ _ a∘x xdc a∘y ydc =
      lim-lim-B a∘x g a∘y g' ε δ η xdc ydc Δ
    Elimℭ̂.isPropB e x y ε _ = isPropB x y ε

  go  : ℭ̂M → A
  go∼ : {x y : ℭ̂M} {ε : ℚ₊} (r : x ∼̂[ ε ] y) → B (go x) (go y) ε

  go  = Elimℭ̂.go e
  go∼ = Elimℭ̂.go∼ e


record Recℭ̂Sym {ℓA} {ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (a∘x : ℚ₊ → A) (g : Γ)
                → (∀ ε δ → B
                    (a∘x ε) (a∘x δ) (g .γ ε +₊ g .γ δ))
                → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y g ε δ yc Δ
                → B (ιA x) (y δ) (ε -₊ g .γ δ , Δ)
                → B (ιA x) (limA y g yc) ε
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
                → B (x δ) (y η)
                    (ε -₊ (g .γ δ +₊ g' .γ η) , Δ)
                → B (limA x g xc) (limA y g' yc) ε

    isSymB  : ∀ a a' ε → B a a' ε → B a' a ε
    isPropB : ∀ a a' ε → isProp (B a a' ε)

  private
    r : Recℭ̂ A B
    Recℭ̂.ιA r = ιA
    Recℭ̂.limA r = limA
    Recℭ̂.eqA r = eqA
    Recℭ̂.ι-ι-B r = ι-ι-B
    Recℭ̂.ι-lim-B r = ι-lim-B
    Recℭ̂.lim-ι-B r = λ x g y ε δ xc Δ Bxδ,y →
      isSymB (ιA y) (limA x g xc) ε
        (ι-lim-B y x g ε δ xc Δ
          (isSymB (x δ) (ιA y) ((ε -₊ g .γ δ) , Δ) Bxδ,y))
    Recℭ̂.lim-lim-B r = lim-lim-B
    Recℭ̂.isPropB r = isPropB

  go  : ℭ̂M → A
  go∼ : {x y : ℭ̂M} {ε : ℚ₊} (r : x ∼̂[ ε ] y) → B (go x) (go y) ε

  go  = Recℭ̂.go r
  go∼ = Recℭ̂.go∼ r


record Recℭ̂∼ {ℓB} (B : ℭ̂M → ℭ̂M → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where

  no-eta-equality

  field
    ι-ι-B     : ∀ x y ε → (x ≈[ ε ] y) → B (ι x) (ι y) ε
    ι-lim-B   : ∀ x y g ε δ yc Δ
                → (ι x ∼̂[ ε -₊ g .γ δ , Δ ] y δ)
                → B (ι x) (y δ) (ε -₊ g .γ δ , Δ)
                → B (ι x) (lim y g yc) ε
    lim-ι-B   : ∀ x g y ε δ xc Δ
                → (x δ ∼̂[ ε -₊ g .γ δ , Δ ] ι y)
                → B (x δ) (ι y) (ε -₊ g .γ δ , Δ)
                → B (lim x g xc) (ι y) ε
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
                → (x δ ∼̂[ ε -₊ (g .γ δ +₊ g' .γ η) , Δ ] y η)
                → B (x δ) (y η)
                    (ε -₊ (g .γ δ +₊ g' .γ η) , Δ)
                → B (lim x g xc) (lim y g' yc) ε
    isPropB   : ∀ x y ε → isProp (B x y ε)

  go∼ : ∀ {x x' ε} → x ∼̂[ ε ] x' → B x x' ε
  go∼ = Elimℭ̂∼.go∼ e
    where
    e : Elimℭ̂∼ λ x x' ε _ → B x x' ε
    Elimℭ̂∼.ι-ι-B e = ι-ι-B
    Elimℭ̂∼.ι-lim-B e = ι-lim-B
    Elimℭ̂∼.lim-ι-B e = lim-ι-B
    Elimℭ̂∼.lim-lim-B e = lim-lim-B
    Elimℭ̂∼.isPropB e = λ x y ε _ → isPropB x y ε


isMonotone∼̂< : ∀ x y ε ε' → ε <₊ ε' → x ∼̂[ ε ] y → x ∼̂[ ε' ] y
isMonotone∼̂< x y ε ε' ε<ε' r = Recℭ̂∼.go∼ monotone r ε' ε<ε'
  where
  monotone : Recℭ̂∼ λ x y ε → ∀ ε' → ε <₊ ε' → x ∼̂[ ε' ] y
  Recℭ̂∼.ι-ι-B monotone x y ε x≈y ε' ε<ε' =
    ι-ι x y ε' (isMonotone≈< x y ε ε' ε<ε' x≈y)
  Recℭ̂∼.ι-lim-B monotone x y g ε δ yc Δ r IH ε' ε<ε' =
    let ρ = g .γ δ
        ρ<ε : ρ <₊ ε
        ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ
        ρ<ε' : ρ <₊ ε'
        ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾
        Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'
        inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
        inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
          (fst ε) (fst ε') (ℚProp.-_ (fst ρ)) ε<ε'
    in ι-lim x y g ε' δ yc Δ' (IH _ inner<)
  Recℭ̂∼.lim-ι-B monotone x g y ε δ xc Δ r IH ε' ε<ε' =
    let ρ = g .γ δ
        ρ<ε : ρ <₊ ε
        ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ
        ρ<ε' : ρ <₊ ε'
        ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾
        Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'
        inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
        inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
          (fst ε) (fst ε') (ℚProp.-_ (fst ρ)) ε<ε'
    in lim-ι x g y ε' δ xc Δ' (IH _ inner<)
  Recℭ̂∼.lim-lim-B monotone x g y g' ε δ η xc yc Δ r IH ε' ε<ε' =
    let ρ = g .γ δ +₊ g' .γ η
        ρ<ε : ρ <₊ ε
        ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ
        ρ<ε' : ρ <₊ ε'
        ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾
        Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'
        inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
        inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
          (fst ε) (fst ε') (ℚProp.-_ (fst ρ)) ε<ε'
    in lim-lim x g y g' ε' δ η xc yc Δ' (IH _ inner<)
  Recℭ̂∼.isPropB monotone x y ε =
    isPropΠ λ ε' → isPropΠ λ _ → isProp∼ x ε' y


record Casesℭ̂ {ℓA} {ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA        : M → A
    limA      : (x : ℚ₊ → ℭ̂M) (g : Γ)
                → ((δ ε : ℚ₊) → x δ ∼̂[ g .γ δ +₊ g .γ ε ] x ε)
                → A
    eqA       : ∀ a a' → (∀ ε → B a a' ε) → a ≡ a'

    ι-ι-B     : ∀ x y ε
                → x ≈[ ε ] y
                → B (ιA x) (ιA y) ε
    ι-lim-B   : ∀ x y g ε δ yc Δ
                → ι x ∼̂[ ε -₊ g .γ δ , Δ ] y δ
                → (a∘y : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B
                    (a∘y ε') (a∘y δ') (g .γ ε' +₊ g .γ δ'))
                → B (ιA x) (a∘y δ) (ε -₊ g .γ δ , Δ)
                → B (ιA x) (limA y g yc) ε
    lim-ι-B   : ∀ x g y ε δ xc Δ
                → x δ ∼̂[ ε -₊ g .γ δ , Δ ] ι y
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B
                    (a∘x ε') (a∘x δ') (g .γ ε' +₊ g .γ δ'))
                → B (a∘x δ) (ιA y) (ε -₊ g .γ δ , Δ)
                → B (limA x g xc) (ιA y) ε
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
                → x δ ∼̂[ ε -₊ (g .γ δ +₊ g' .γ η) , Δ ] y η
                → (a∘x : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B
                    (a∘x ε') (a∘x δ') (g .γ ε' +₊ g .γ δ'))
                → (a∘y : ℚ₊ → A)
                → ((ε' δ' : ℚ₊) → B
                    (a∘y ε') (a∘y δ') (g' .γ ε' +₊ g' .γ δ'))
                → B (a∘x δ) (a∘y η)
                    (ε -₊ (g .γ δ +₊ g' .γ η) , Δ)
                → B (limA x g xc) (limA y g' yc) ε
    isPropB   : ∀ a a' ε → isProp (B a a' ε)

  private
    e : Elimℭ̂ (λ _ → A) λ a a' ε _ → B a a' ε
    Elimℭ̂.ιA e = ιA
    Elimℭ̂.limA e = λ x g xc _ _ → limA x g xc
    Elimℭ̂.eqA e = λ _ a a' _ p → eqA a a' p
    Elimℭ̂.ι-ι-B e = ι-ι-B
    Elimℭ̂.ι-lim-B e = ι-lim-B
    Elimℭ̂.lim-ι-B e = lim-ι-B
    Elimℭ̂.lim-lim-B e = lim-lim-B
    Elimℭ̂.isPropB e = λ x y ε _ → isPropB x y ε

  go : ℭ̂M → A
  go = Elimℭ̂.go e

  go∼ : {x y : ℭ̂M} {ε : ℚ₊} → x ∼̂[ ε ] y → B (go x) (go y) ε
  go∼ = Elimℭ̂.go∼ e


isRefl∼̂ : ∀ x ε → x ∼̂[ ε ] x
isRefl∼̂ = Elimℭ̂-Prop.go reflElim
  where
  reflElim : Elimℭ̂-Prop (λ x → ∀ ε → x ∼̂[ ε ] x)
  Elimℭ̂-Prop.ιA reflElim x ε = ι-ι x x ε (isRefl≈ x ε)
  Elimℭ̂-Prop.limA reflElim x g cx IH ε =
    let q = ε /4₊ /2₊
        δ = g .τ q
        ρ = g .γ δ
        inner = ρ +₊ ρ
        outer = ρ +₊ ρ
        ρ≤q = g .γ∘τ≤id q
        inner≤q+q : inner ≤₊ (q +₊ q)
        inner≤q+q = +Mono≤ _ _ _ _ ρ≤q ρ≤q
        total≤four-q : (inner +₊ outer) ≤₊ ((q +₊ q) +₊ (q +₊ q))
        total≤four-q = +Mono≤ _ _ _ _ inner≤q+q inner≤q+q
        four-q≡ε/2 : fst ((q +₊ q) +₊ (q +₊ q)) ≡ fst (ε /2₊)
        four-q≡ε/2 =
            cong (λ z → z ℚProp.+ z) (/2+/2≡id (fst (ε /4₊)))
          ∙ /4+/4≡/2 (fst ε)
        total<ε : fst (inner +₊ outer) <ℚ fst ε
        total<ε = begin<
          fst (inner +₊ outer) ≤⟨ total≤four-q ⟩
          fst ((q +₊ q) +₊ (q +₊ q)) ≡→≤⟨ four-q≡ε/2 ⟩
          fst (ε /2₊) <⟨ /2₊<id ε ⟩
          fst ε ◾
        outer<ε : outer <₊ ε
        outer<ε = begin<
          fst outer <⟨ <₊SumRight outer inner ⟩
          fst (inner +₊ outer) <⟨ total<ε ⟩
          fst ε ◾
        Δ = <→0<Δ (fst outer) (fst ε) outer<ε
        target = (ε -₊ outer , Δ)
        inner<target : inner <₊ target
        inner<target = +CancelR< (fst inner) (fst target) (fst outer)
          (subst (fst inner ℚProp.+ fst outer <ℚ_)
            (sym (minusPlus₊ ε outer)) total<ε)
        enlarged = isMonotone∼̂< _ _ inner target inner<target (cx δ δ)
    in lim-lim x g x g ε δ δ cx cx Δ enlarged
  Elimℭ̂-Prop.isPropA reflElim x =
    isPropΠ λ ε → isProp∼ x ε x


isSetℭ̂ : isSet ℭ̂M
isSetℭ̂ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼̂[ ε ] y)
  isRefl∼̂
  (λ x y → isPropΠ λ ε → isProp∼ x ε y)
  (eqℭ _ _)



g-lemma : ∀ x g cx cx' → lim x g cx ≡ lim (λ ε → (x (g .τ ε))) Γid cx'
g-lemma x g cx cx' = eqℭ _ _ λ ε →
  let q = ε /4₊ /2₊
      δ = g .τ q
      inner = q +₊ q
      outer = g .γ δ +₊ q
      γδ≤q = g .γ∘τ≤id q
      outer≤inner : outer ≤₊ inner
      outer≤inner = OrderedCommRingStr.+MonoR≤ (snd ℚOrderedCommRing)
        (fst (g .γ δ)) (fst q) (fst q) γδ≤q
      four-q≡ε/2 : fst (inner +₊ inner) ≡ fst (ε /2₊)
      four-q≡ε/2 =
          cong (λ z → z ℚProp.+ z) (/2+/2≡id (fst (ε /4₊)))
        ∙ /4+/4≡/2 (fst ε)
      total<ε : fst (inner +₊ outer) <ℚ fst ε
      total<ε = begin<
        fst (inner +₊ outer)
          ≤⟨ +MonoL≤ (fst outer) (fst inner) (fst inner) outer≤inner ⟩
        fst (inner +₊ inner)
          ≡→≤⟨ four-q≡ε/2 ⟩
        fst (ε /2₊) <⟨ /2₊<id ε ⟩
        fst ε ◾
      outer<ε : outer <₊ ε
      outer<ε = begin<
        fst outer <⟨ <₊SumRight outer inner ⟩
        fst (inner +₊ outer) <⟨ total<ε ⟩
        fst ε ◾
      Δ = <→0<Δ (fst outer) (fst ε) outer<ε
      target = (ε -₊ outer , Δ)
      inner<target : inner <₊ target
      inner<target = +CancelR< (fst inner) (fst target) (fst outer)
        (subst (fst inner ℚProp.+ fst outer <ℚ_)
          (sym (minusPlus₊ ε outer)) total<ε)
      same-sample = cx' q q
      enlarged = isMonotone∼̂< _ _ inner target inner<target same-sample
  in lim-lim x g (λ θ → x (g .τ θ)) Γid
       ε δ q cx cx' Δ enlarged


private
  regularLimCong :
    ∀ (x y : ℚ₊ → ℭM)
      (xc : ∀ ε δ → x ε ∼[ ε +₊ δ ] x δ)
      (yc : ∀ ε δ → y ε ∼[ ε +₊ δ ] y δ)
    → x ≡ y → RegularBase.lim x xc ≡ RegularBase.lim y yc
  regularLimCong x y xc yc p =
    cong (λ z → RegularBase.lim (fst z) (snd z)) pairPath
    where
    pairPath : (x , xc) ≡ (y , yc)
    pairPath = Σ≡Prop
      (λ z → isPropΠ2 λ ε δ →
        RegularPremetric.isProp≈ (z ε) (z δ) (ε +₊ δ)) p

  alternativeLimCong :
    ∀ (x y : ℚ₊ → ℭ̂M) g
      (xc : ∀ ε δ → x ε ∼̂[ g .γ ε +₊ g .γ δ ] x δ)
      (yc : ∀ ε δ → y ε ∼̂[ g .γ ε +₊ g .γ δ ] y δ)
    → x ≡ y → lim x g xc ≡ lim y g yc
  alternativeLimCong x y g xc yc p =
    cong (λ z → lim (fst z) g (snd z)) pairPath
    where
    pairPath : (x , xc) ≡ (y , yc)
    pairPath = Σ≡Prop
      (λ z → isPropΠ2 λ ε δ →
        isProp∼ (z ε) (g .γ ε +₊ g .γ δ) (z δ)) p


←̂→̂ : ∀ x → ←̂ (→̂ x) ≡ x
←̂→̂ = Elimℭ-Prop.go retractElim
  where
  retractElim : Elimℭ-Prop (λ x → ←̂ (→̂ x) ≡ x)
  Elimℭ-Prop.ιA retractElim x = refl
  Elimℭ-Prop.limA retractElim x xc IH =
    regularLimCong _ _ _ _ (funExt IH)
  Elimℭ-Prop.isPropA retractElim x = Regular.isSetℭ _ _


→̂←̂ : ∀ x → →̂ (←̂ x) ≡ x
→̂←̂ = Elimℭ̂-Prop.go sectionElim
  where
  sectionElim : Elimℭ̂-Prop (λ x → →̂ (←̂ x) ≡ x)
  Elimℭ̂-Prop.ιA sectionElim x = refl
  Elimℭ̂-Prop.limA sectionElim x g cx IH =
    alternativeLimCong _ _ Γid _ cxτ
      (funExt λ ε → IH (g .τ ε))
    ∙ sym (g-lemma x g cx cxτ)
    where
    cxτ : ∀ ε δ → x (g .τ ε) ∼̂[ ε +₊ δ ] x (g .τ δ)
    cxτ ε δ = subst2 (λ u v → u ∼̂[ ε +₊ δ ] v)
      (IH (g .τ ε)) (IH (g .τ δ))
      (→̂~ _ _ _ (←̂Cauchy x g cx ε δ))
  Elimℭ̂-Prop.isPropA sectionElim x = isSetℭ̂ _ _


regularAlternativeIso : Iso ℭM ℭ̂M
regularAlternativeIso .Iso.fun = →̂
regularAlternativeIso .Iso.inv = ←̂
regularAlternativeIso .Iso.sec = →̂←̂
regularAlternativeIso .Iso.ret = ←̂→̂
