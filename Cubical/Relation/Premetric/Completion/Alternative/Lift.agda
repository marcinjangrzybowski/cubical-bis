open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Lift
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Alternative M'
open import Cubical.Relation.Premetric.Completion.Alternative.Properties M'

import Cubical.Relation.Premetric.Completion.Properties.Lift as RegularLift

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing
open Γ

private
  M = M' .fst
  N = N' .fst
  module PM = PremetricStr (M' .snd)
  module PN = PremetricStr (N' .snd)
  module Pℭ̂ = PremetricStr (ℭ̂PremetricSpace .snd)


-- A Lipschitz constant determines a scale: γ divides the desired output
-- radius by L, while τ multiplies an input radius by L.

lipschitzΓ : ℚ₊ → Γ
lipschitzΓ L .γ ε = ε ₊／₊ L
lipschitzΓ L .mon-γ ε δ ε<δ =
  OrderedCommRingStr.·MonoR< (snd ℚOrderedCommRing)
    (fst ε) (fst δ) (fst (L ⁻¹₊)) (snd (L ⁻¹₊)) ε<δ
lipschitzΓ L .τ ε = L ·₊ ε
lipschitzΓ L .γ∘τ≤id ε = begin≤
  fst ((L ·₊ ε) ₊／₊ L)
    ≡→≤⟨ ℚ.·Comm (fst (L ·₊ ε)) (fst (L ⁻¹₊)) ⟩
  fst (L ⁻¹₊) ℚ.· (fst L ℚ.· fst ε)
    ≡→≤⟨ [y·x]/y L (fst ε) ⟩
  fst ε ◾


-- This is the constructor-level modulus naturally suggested by Γ.  It says
-- exactly that a g-Cauchy family is sent to an ordinary Cauchy family.

record IsΓModulusWith (g : Γ) (f : M → N) :
  Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')) where
  no-eta-equality
  field
    pres≈ : ∀ x y ε δ →
      x PM.≈[ g .γ ε +₊ g .γ δ ] y →
      f x PN.≈[ ε +₊ δ ] f y

open IsΓModulusWith

ΓModulus→presCauchy : ∀ g f → IsΓModulusWith g f →
  ∀ x →
  (∀ ε δ → x ε PM.≈[ g .γ ε +₊ g .γ δ ] x δ) →
  PremetricTheory.isCauchy N' (f ∘ x)
ΓModulus→presCauchy g f f-mod x xc ε δ =
  f-mod .pres≈ (x ε) (x δ) ε δ (xc ε δ)


-- Lipschitz maps are a special case of Γ-modulus maps.

lipschitzWith→ΓModulus : ∀ L f →
  IsLipschitzWith (M' .snd) f (N' .snd) L →
  IsΓModulusWith (lipschitzΓ L) f
lipschitzWith→ΓModulus L f f-lip .pres≈ x y ε δ p =
  PN.subst≈ (f x) (f y)
    (ℚ.·DistL+ (fst L) (fst (ε ₊／₊ L)) (fst (δ ₊／₊ L))
      ∙ cong₂ ℚ._+_ (·／ L ε) (·／ L δ))
    (f-lip .IsLipschitzWith.pres≈ x y
      ((ε ₊／₊ L) +₊ (δ ₊／₊ L)) p)


-- Conversely, a Γ-modulus is an explicit uniform-continuity modulus.  Thus
-- the scale condition is potentially more general than a constant
-- Lipschitz bound, but it is still a structured form of uniform continuity.

ΓModulus→uniformlyContinuousWith : ∀ g f →
  IsΓModulusWith g f →
  IsUniformlyContinuousWith (M' .snd) f (N' .snd)
    (λ ε → g .γ (ε /2₊) +₊ g .γ (ε /2₊))
ΓModulus→uniformlyContinuousWith g f f-mod
  .IsUniformlyContinuousWith.pres≈ x y ε p =
  PN.subst≈ (f x) (f y) (/2+/2≡id (fst ε))
    (f-mod .pres≈ x y (ε /2₊) (ε /2₊) p)


-- Since the two completions are isometric, the established Lipschitz lift
-- transfers without any loss or extra hypothesis.  Therefore the alternative
-- presentation does not by itself weaken the existing lifting theorem.

module LiftCompleteCodomain (N-com : PremetricTheory.isComplete N') where
  module RegularComplete = RegularLift.LiftCompleteCodomain M' N' N-com

  liftLipschitzWitĥ : ∀ L f →
    IsLipschitzWith (M' .snd) f (N' .snd) L →
    Σ[ f̂ ∈ (ℭ̂ → N) ]
      IsLipschitzWith (ℭ̂PremetricSpace .snd) f̂ (N' .snd) L
  liftLipschitzWitĥ L f f-lip = f̂ , f̂-lip
    where
    regular-lift = RegularComplete.liftLipschitzWith L f f-lip

    f̂ : ℭ̂ → N
    f̂ = regular-lift .fst ∘ ←̂

    f̂-lip : IsLipschitzWith (ℭ̂PremetricSpace .snd) f̂ (N' .snd) L
    f̂-lip .IsLipschitzWith.pres≈ x y ε p =
      regular-lift .snd .IsLipschitzWith.pres≈
        (←̂ x) (←̂ y) ε (←̂~ x y ε p)

  liftLipschitzWitĥ∘ι : ∀ L f f-lip →
    fst (liftLipschitzWitĥ L f f-lip) ∘ ι ≡ f
  liftLipschitzWitĥ∘ι L f f-lip = refl

  liftLipschitzWithFun̂ : ∀ L f →
    IsLipschitzWith (M' .snd) f (N' .snd) L → ℭ̂ → N
  liftLipschitzWithFun̂ L f f-lip =
    fst (liftLipschitzWitĥ L f f-lip)

  liftLipschitzWithFun̂-independent : ∀ L K f fL fK →
    liftLipschitzWithFun̂ L f fL ≡
      liftLipschitzWithFun̂ K f fK
  liftLipschitzWithFun̂-independent L K f fL fK =
    cong (_∘ ←̂)
      (RegularComplete.isIrrelevantLiftLipschitzWith L K f fL fK)

  liftLipschitzWithFun̂-ext :
    ∀ L K (f g : M → N)
      (fL : IsLipschitzWith (M' .snd) f (N' .snd) L)
      (gK : IsLipschitzWith (M' .snd) g (N' .snd) K) →
    (∀ x → f x ≡ g x) →
    liftLipschitzWithFun̂ L f fL ≡
      liftLipschitzWithFun̂ K g gK
  liftLipschitzWithFun̂-ext L K f g fL gK f∼g =
    lift-cong f fL (funExt f∼g) K gK
    where
    lift-cong :
      ∀ (f : M → N)
        (fL : IsLipschitzWith (M' .snd) f (N' .snd) L)
        {g : M → N} → f ≡ g →
        ∀ K (gK : IsLipschitzWith (M' .snd) g (N' .snd) K) →
      liftLipschitzWithFun̂ L f fL ≡
        liftLipschitzWithFun̂ K g gK
    lift-cong f fL {g} f≡g =
      J (λ g _ → ∀ K
          (gK : IsLipschitzWith (M' .snd) g (N' .snd) K) →
        liftLipschitzWithFun̂ L f fL ≡
            liftLipschitzWithFun̂ K g gK)
        (λ K fK →
          liftLipschitzWithFun̂-independent L K f fL fK)
        f≡g

  liftNonExpandinĝ : NE[ M' , N' ] → NE[ ℭ̂PremetricSpace , N' ]
  liftNonExpandinĝ f =
    map-snd (isLipschitzWith1→isNonExpanding _ _ _)
      (liftLipschitzWitĥ 1 (fst f)
        (isNonExpanding→isLipschitzWith1 _ (fst f) _ (snd f)))

  liftNonExpandinĝ∘ι : ∀ f → fst (liftNonExpandinĝ f) ∘ ι ≡ fst f
  liftNonExpandinĝ∘ι f = refl

  liftNonExpandinĝ-ext : ∀ f g →
    (∀ x → fst f x ≡ fst g x) →
    liftNonExpandinĝ f ≡ liftNonExpandinĝ g
  liftNonExpandinĝ-ext f g f∼g = cong liftNonExpandinĝ
    (Σ≡Prop
      (λ h → isPropIsNonExpanding (M' .snd) h (N' .snd))
      (funExt f∼g))


-- Open question left by this module: IsΓModulusWith is enough to turn each
-- individual g-Cauchy family into a Cauchy image, but the recursive relation
-- motive must also compare limits whose constructor scales vary.  The present
-- Γ and g-irrelevance results do not yet provide that coherence for an
-- arbitrary Γ-modulus.  Consequently the proved default lift remains
-- Lipschitz; Γ-moduli identify a precise candidate generalization rather than
-- an already established broader lifting theorem.
