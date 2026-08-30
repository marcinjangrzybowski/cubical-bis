module Cubical.Relation.Premetric.Completion.Rationals.Lift.MapsRationalCauchySequences where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Base as RegularDefinition
import Cubical.Relation.Premetric.Completion.Elim as RegularElimDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as ComparisonDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous
  as CauchyContinuous
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Lift.MapsRationalCauchySequencesPresented
  as Presented

module R = RegularDefinition ℚPremetricSpace
module RE = RegularElimDefinition ℚPremetricSpace
module RP = RegularPropertiesDefinition ℚPremetricSpace
module S = SequentialDefinition ℚPremetricSpace
module Comparison = ComparisonDefinition ℚPremetricSpace
module RPremetric = PremetricStr (RP.ℭPremetricSpace .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


-- A rational approximation is deliberately quotiented before it is put in
-- the proposition-valued motive below.  Its convergence point lives in the
-- ordinary (regular) completion.

RationalCauchyApproximation : Type₀
RationalCauchyApproximation = Presented.RationalCauchyPresentedReal


convergencePoint : RationalCauchyApproximation → R.ℭ
convergencePoint =
  Comparison.toRegular ∘ Presented.presentedRealQuotient


rationalApproximation : ℚ → RationalCauchyApproximation
rationalApproximation = Presented.rationalPresentedReal


convergencePoint-rational : ∀ q →
  convergencePoint (rationalApproximation q) ≡ R.ι q
convergencePoint-rational q =
  cong Comparison.toRegular
    (Presented.presentedRealQuotient-rational q)
  ∙ Comparison.toRegular-ι q


convergencePoint-injective : ∀ a b →
  convergencePoint a ≡ convergencePoint b → a ≡ b
convergencePoint-injective =
  SQ.elimProp2
    (λ a b → isProp→ (SQ.squash/ a b))
    (λ p p' same →
      SQ.eq/ p p'
        (Presented.presentedReal≡→interleavingCauchy p p'
          (sym
              (Comparison.sequentialRegularIso .Iso.ret
                (Presented.presentedReal p))
          ∙ cong Comparison.fromRegular same
          ∙ Comparison.sequentialRegularIso .Iso.ret
              (Presented.presentedReal p'))))


RationalCauchyApproximationOf : R.ℭ → Type₀
RationalCauchyApproximationOf x =
  Σ[ a ∈ RationalCauchyApproximation ] convergencePoint a ≡ x


isPropRationalCauchyApproximationOf : ∀ x →
  isProp (RationalCauchyApproximationOf x)
isPropRationalCauchyApproximationOf x (a , a→x) (b , b→x) =
  Σ≡Prop (λ _ → RP.isSetℭ _ _)
    (convergencePoint-injective a b (a→x ∙ sym b→x))


rationalHasApproximation : ∀ q →
  RationalCauchyApproximationOf (R.ι q)
rationalHasApproximation q =
  rationalApproximation q , convergencePoint-rational q


-- Mapping a quotient presentation uses only the hypothesis that `f` sends
-- rational Cauchy sequences to rational Cauchy sequences.  Interleaving is
-- what makes this operation independent of the representative.

mapApproximation :
  (f : ℚ → ℚ) → CauchyContinuous.MapsRationalCauchySequences f →
  RationalCauchyApproximation → RationalCauchyApproximation
mapApproximation = Presented.liftRationalCauchyPresentedReal


mapApproximation-rational :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f) q →
  mapApproximation f maps (rationalApproximation q) ≡
    rationalApproximation (f q)
mapApproximation-rational =
  Presented.liftRationalCauchyPresentedReal-rational


MapsEveryRationalApproximationTo :
  (f : ℚ → ℚ) → CauchyContinuous.MapsRationalCauchySequences f →
  R.ℭ → R.ℭ → Type₀
MapsEveryRationalApproximationTo f maps x y =
  ∀ a → convergencePoint a ≡ x →
    convergencePoint (mapApproximation f maps a) ≡ y


isPropMapsEveryRationalApproximationTo :
  ∀ f maps x y →
  isProp (MapsEveryRationalApproximationTo f maps x y)
isPropMapsEveryRationalApproximationTo f maps x y =
  isPropΠ2 λ _ _ → RP.isSetℭ _ _


-- Besides the proposed universal characterization of the output, the fiber
-- retains approximation classes for both endpoints.  The source class is
-- needed to make the universal condition non-vacuous when proving that the
-- whole fiber is a proposition.

LiftFiber :
  (f : ℚ → ℚ) → CauchyContinuous.MapsRationalCauchySequences f →
  R.ℭ → Type₀
LiftFiber f maps x =
  Σ[ y ∈ R.ℭ ]
    RationalCauchyApproximationOf x ×
    RationalCauchyApproximationOf y ×
    MapsEveryRationalApproximationTo f maps x y


isPropLiftFiber : ∀ f maps x → isProp (LiftFiber f maps x)
isPropLiftFiber f maps x
  (y , source , target , maps-to-y)
  (y' , source' , target' , maps-to-y') =
  Σ≡Prop
    (λ z →
      isProp× (isPropRationalCauchyApproximationOf x)
        (isProp× (isPropRationalCauchyApproximationOf z)
          (isPropMapsEveryRationalApproximationTo f maps x z)))
    (sym (maps-to-y (source .fst) (source .snd))
      ∙ maps-to-y' (source .fst) (source .snd))


fiberFromApproximation :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f) x →
  RationalCauchyApproximationOf x → LiftFiber f maps x
fiberFromApproximation f maps x source =
  convergencePoint (mapApproximation f maps (source .fst)) ,
  source ,
  (mapApproximation f maps (source .fst) , refl) ,
  mapped-limit
  where
  mapped-limit : MapsEveryRationalApproximationTo f maps x
    (convergencePoint (mapApproximation f maps (source .fst)))
  mapped-limit a a→x = cong convergencePoint
    (cong (mapApproximation f maps)
      (convergencePoint-injective a (source .fst)
        (a→x ∙ sym (source .snd))))


rationalLiftFiber :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f) q →
  LiftFiber f maps (R.ι q)
rationalLiftFiber f maps q =
  fiberFromApproximation f maps (R.ι q)
    (rationalHasApproximation q)


rationalLiftFiber-output :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f) q →
  rationalLiftFiber f maps q .fst ≡ R.ι (f q)
rationalLiftFiber-output f maps q =
  cong convergencePoint (mapApproximation-rational f maps q)
  ∙ convergencePoint-rational (f q)


-- The metric diagonal itself is constructive when the representatives have
-- not yet been quotiented.  We use one quarter for the outer approximation
-- and half of that quarter for the inner rational approximation.  Thus the
-- three legs consume only half of `ε + δ`.

record RegularRationalApproximationOf (x : R.ℭ) : Type₀ where

  no-eta-equality

  field
    terms : ℚ₊ → ℚ
    regular : ∀ ε δ →
      R.ι (terms ε) R.∼[ ε +₊ δ ] R.ι (terms δ)
    realizes : R.lim (R.ι ∘ terms) regular ≡ x

open RegularRationalApproximationOf public


regularApproximation-close : ∀ {x}
  (a : RegularRationalApproximationOf x) ε θ →
  R.ι (a .terms ε) R.∼[ ε +₊ θ ] x
regularApproximation-close a ε θ =
  subst (R.ι (a .terms ε) R.∼[ ε +₊ θ ]_)
    (a .realizes)
    (RP.isLimitLim (R.ι ∘ a .terms) (a .regular) ε θ)


diagonalRadius< : ∀ ε δ →
  ((ε /4₊ +₊ (ε /4₊ +₊ δ /4₊)) +₊ δ /4₊) <₊ (ε +₊ δ)
diagonalRadius< ε δ = begin<
  fst ((ε /4₊ +₊ (ε /4₊ +₊ δ /4₊)) +₊ δ /4₊)
    ≡→≤⟨
      cong (ℚ._+ fst (δ /4₊))
        (+Assoc (fst (ε /4₊)) (fst (ε /4₊)) (fst (δ /4₊)))
      ∙ sym (+Assoc
          (fst (ε /4₊) ℚ.+ fst (ε /4₊))
          (fst (δ /4₊)) (fst (δ /4₊)))
      ∙ cong₂ ℚ._+_
          (/4+/4≡/2 (fst ε)) (/4+/4≡/2 (fst δ))
    ⟩
  fst (ε /2₊ +₊ δ /2₊)
    <⟨ +Mono< _ _ _ _ (/2₊<id ε) (/2₊<id δ) ⟩
  fst (ε +₊ δ) ◾


diagonalRegularTerms : ∀ {x : ℚ₊ → R.ℭ} →
  (∀ ρ → RegularRationalApproximationOf (x ρ)) → ℚ₊ → ℚ
diagonalRegularTerms approximations ε =
  approximations (ε /4₊) .terms ((ε /4₊) /2₊)


-- Keep the regularity witness opaque.  The realization proof below only
-- uses its type; unfolding its nested triangle proof there makes conversion
-- checking grow dramatically.
opaque
  diagonalRegular : ∀ (x : ℚ₊ → R.ℭ)
    (xc : ∀ ε δ → x ε R.∼[ ε +₊ δ ] x δ) →
    (approximations : ∀ ρ → RegularRationalApproximationOf (x ρ)) →
    ∀ ε δ →
    R.ι (diagonalRegularTerms approximations ε)
      R.∼[ ε +₊ δ ]
    R.ι (diagonalRegularTerms approximations δ)
  diagonalRegular x xc approximations ε δ =
    RPremetric.isMonotone≈< _ _ _ (ε +₊ δ)
      (diagonalRadius< ε δ)
      (RP.isTriangular∼ _ _ _
        (ε /4₊ +₊ (ε /4₊ +₊ δ /4₊)) (δ /4₊)
        (RP.isTriangular∼ _ _ _ (ε /4₊) (ε /4₊ +₊ δ /4₊)
          left (xc (ε /4₊) (δ /4₊)))
        (RP.isSym∼ _ _ (δ /4₊) right))
    where
    left :
      R.ι (diagonalRegularTerms approximations ε)
        R.∼[ ε /4₊ ] x (ε /4₊)
    left = RP.subst∼ _ _ (/2+/2≡id (fst (ε /4₊)))
      (regularApproximation-close (approximations (ε /4₊))
        ((ε /4₊) /2₊) ((ε /4₊) /2₊))

    right :
      R.ι (diagonalRegularTerms approximations δ)
        R.∼[ δ /4₊ ] x (δ /4₊)
    right = RP.subst∼ _ _ (/2+/2≡id (fst (δ /4₊)))
      (regularApproximation-close (approximations (δ /4₊))
        ((δ /4₊) /2₊) ((δ /4₊) /2₊))


diagonalRegularApproximation : ∀ (x : ℚ₊ → R.ℭ)
  (xc : ∀ ε δ → x ε R.∼[ ε +₊ δ ] x δ) →
  (approximations : ∀ ρ → RegularRationalApproximationOf (x ρ)) →
  RegularRationalApproximationOf (R.lim x xc)
diagonalRegularApproximation x xc approximations .terms =
  diagonalRegularTerms approximations
diagonalRegularApproximation x xc approximations .regular =
  diagonalRegular x xc approximations
diagonalRegularApproximation x xc approximations .realizes =
  R.eqℭ _ _ λ ε →
    RPremetric.isMonotone≈< _ _ _ ε
      (Presented.tripleQuarter< ε)
      (RP.isTriangular∼ _ _ _ (ε /4₊ +₊ ε /4₊) (ε /4₊)
        (RP.isTriangular∼ _ _ _ (ε /4₊) (ε /4₊)
          (limit-to-sample ε) (sample-to-source ε))
        (source-to-limit ε))
  where
  sample : ∀ ε → ℚ₊
  sample ε = (ε /4₊) /2₊

  outer : ∀ ε → ℚ₊
  outer ε = sample ε /4₊

  outer<quarter : ∀ ε → outer ε <₊ ε /4₊
  outer<quarter ε =
    ℚ.isTrans< _ _ _ (/4₊<id (sample ε)) (/2₊<id (ε /4₊))

  halfOuterSum<quarter : ∀ ε →
    (outer ε +₊ outer ε) <₊ ε /4₊
  halfOuterSum<quarter ε =
    subst (_< fst (ε /4₊))
      (sym (/4+/4≡/2 (fst (sample ε))))
      (ℚ.isTrans< _ _ _
        (/2₊<id (sample ε)) (/2₊<id (ε /4₊)))

  limit-to-sample : ∀ ε →
    R.lim (R.ι ∘ diagonalRegularTerms approximations)
      (diagonalRegular x xc approximations)
      R.∼[ ε /4₊ ]
    R.ι (diagonalRegularTerms approximations (sample ε))
  limit-to-sample ε = RP.isSym∼ _ _ (ε /4₊)
    (RP.subst∼ _ _ (/2+/2≡id (fst (ε /4₊)))
      (RP.isLimitLim (R.ι ∘ diagonalRegularTerms approximations)
        (diagonalRegular x xc approximations) (sample ε) (sample ε)))

  sample-to-source : ∀ ε →
    R.ι (diagonalRegularTerms approximations (sample ε))
      R.∼[ ε /4₊ ] x (outer ε)
  sample-to-source ε =
    RPremetric.isMonotone≈< _ _ (outer ε) (ε /4₊)
      (outer<quarter ε)
      (RP.subst∼ _ _ (/2+/2≡id (fst (outer ε)))
        (regularApproximation-close (approximations (outer ε))
          ((outer ε) /2₊) ((outer ε) /2₊)))

  source-to-limit : ∀ ε →
    x (outer ε) R.∼[ ε /4₊ ] R.lim x xc
  source-to-limit ε =
    RPremetric.isMonotone≈< _ _ _ (ε /4₊)
      (halfOuterSum<quarter ε)
      (RP.isLimitLim x xc (outer ε) (outer ε))

-- The proposition eliminator now leaves exactly one operation to provide.
-- Notice that it does not mention `f`: it is closure of quotient rational
-- presentations under the regular completion's nested `lim` constructor.

record RationalApproximationLimitClosure : Type₀ where

  no-eta-equality

  field
    diagonal : ∀ x xc →
      (∀ ε → RationalCauchyApproximationOf (x ε)) →
      RationalCauchyApproximationOf (R.lim x xc)

open RationalApproximationLimitClosure public


liftFiberEliminator :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f) →
  RationalApproximationLimitClosure → RE.Elimℭ-Prop (LiftFiber f maps)
liftFiberEliminator f maps closure .RE.Elimℭ-Prop.ιA q =
  rationalLiftFiber f maps q
liftFiberEliminator f maps closure .RE.Elimℭ-Prop.limA x xc IH =
  fiberFromApproximation f maps (R.lim x xc)
    (closure .diagonal x xc (λ ε → IH ε .snd .fst))
liftFiberEliminator f maps closure .RE.Elimℭ-Prop.isPropA =
  isPropLiftFiber f maps


liftFiber :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f) →
  RationalApproximationLimitClosure → ∀ x → LiftFiber f maps x
liftFiber f maps closure =
  RE.Elimℭ-Prop.go (liftFiberEliminator f maps closure)


liftMapsRationalCauchySequences :
  (f : ℚ → ℚ) → CauchyContinuous.MapsRationalCauchySequences f →
  RationalApproximationLimitClosure → R.ℭ → R.ℭ
liftMapsRationalCauchySequences f maps closure x =
  liftFiber f maps closure x .fst


liftMapsRationalCauchySequences-ι :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f)
    (closure : RationalApproximationLimitClosure) q →
  liftMapsRationalCauchySequences f maps closure (R.ι q) ≡ R.ι (f q)
liftMapsRationalCauchySequences-ι f maps closure q =
  rationalLiftFiber-output f maps q


liftMapsRationalCauchySequences-characterization :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f)
    (closure : RationalApproximationLimitClosure) x →
  MapsEveryRationalApproximationTo f maps x
    (liftMapsRationalCauchySequences f maps closure x)
liftMapsRationalCauchySequences-characterization f maps closure x =
  liftFiber f maps closure x .snd .snd .snd


liftMapsRationalCauchySequences-hasApproximation :
  ∀ (f : ℚ → ℚ)
    (maps : CauchyContinuous.MapsRationalCauchySequences f)
    (closure : RationalApproximationLimitClosure) x →
  RationalCauchyApproximationOf
    (liftMapsRationalCauchySequences f maps closure x)
liftMapsRationalCauchySequences-hasApproximation f maps closure x =
  liftFiber f maps closure x .snd .snd .fst
