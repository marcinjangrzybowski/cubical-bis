module Cubical.Relation.Premetric.Completion.Rationals.Experimental.RationalCauchyApproximations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Base as Completion
import Cubical.Relation.Premetric.Completion.Elim as CompletionElim
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as CompletionProperties

module R = Completion ℚPremetricSpace
module RE = CompletionElim ℚPremetricSpace
module RP = CompletionProperties ℚPremetricSpace
module ℚPremetric = PremetricStr (ℚPremetricSpace .snd)
module RPremetric = PremetricStr (RP.ℭPremetricSpace .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


-- This is literally the pair of arguments supplied to `R.lim`, except that
-- its first argument is required to factor through the rational injection.

RationalCauchyApproximation : Type₀
RationalCauchyApproximation =
  Σ[ terms ∈ (ℚ₊ → ℚ) ]
    ((ε δ : ℚ₊) →
      R.ι (terms ε) R.∼[ ε +₊ δ ] R.ι (terms δ))


approximationLimit : RationalCauchyApproximation → R.ℭ
approximationLimit (terms , regular) =
  R.lim (R.ι ∘ terms) regular


SameLimit : RationalCauchyApproximation →
  RationalCauchyApproximation → Type₀
SameLimit a b = approximationLimit a ≡ approximationLimit b


RationalCauchyApproximationClass : Type₀
RationalCauchyApproximationClass =
  RationalCauchyApproximation / SameLimit


classLimit : RationalCauchyApproximationClass → R.ℭ
classLimit = SQ.rec RP.isSetℭ approximationLimit (λ _ _ same → same)


classLimit-injective : ∀ a b →
  classLimit a ≡ classLimit b → a ≡ b
classLimit-injective =
  SQ.elimProp2
    (λ a b → isProp→ (SQ.squash/ a b))
    (λ a b same → SQ.eq/ a b same)


RationalCauchyApproximationOf : R.ℭ → Type₀
RationalCauchyApproximationOf x =
  Σ[ a ∈ RationalCauchyApproximationClass ] classLimit a ≡ x


isPropRationalCauchyApproximationOf : ∀ x →
  isProp (RationalCauchyApproximationOf x)
isPropRationalCauchyApproximationOf x (a , a→x) (b , b→x) =
  Σ≡Prop (λ _ → RP.isSetℭ _ _)
    (classLimit-injective a b (a→x ∙ sym b→x))


constantApproximation : ℚ → RationalCauchyApproximation
constantApproximation q =
  (λ _ → q) ,
  (λ ε δ → R.ι-ι q q (ε +₊ δ) (ℚPremetric.isRefl≈ q (ε +₊ δ)))


constantApproximation-limit : ∀ q →
  approximationLimit (constantApproximation q) ≡ R.ι q
constantApproximation-limit q = R.eqℭ _ _ λ ε →
  RPremetric.isMonotone≈< _ _ (ε /2₊) ε (/2₊<id ε)
    (RP.isSym∼ _ _ (ε /2₊)
      (RP.subst∼ _ _ (/4+/4≡/2 (fst ε))
        (RP.isLimitLim
          (R.ι ∘ fst (constantApproximation q))
          (snd (constantApproximation q))
          (ε /4₊) (ε /4₊))))


rationalApproximation : ℚ → RationalCauchyApproximationClass
rationalApproximation q = SQ.[ constantApproximation q ]


rationalHasApproximation : ∀ q →
  RationalCauchyApproximationOf (R.ι q)
rationalHasApproximation q =
  rationalApproximation q , constantApproximation-limit q


-- Before quotienting, an approximation of `x` includes the equality saying
-- that its `lim` is `x`.  A family of these actual representatives admits a
-- constructive metric diagonal.

RationalCauchyRepresentativeOf : R.ℭ → Type₀
RationalCauchyRepresentativeOf x =
  Σ[ a ∈ RationalCauchyApproximation ] approximationLimit a ≡ x


representative→class : ∀ {x} →
  RationalCauchyRepresentativeOf x →
  RationalCauchyApproximationOf x
representative→class (a , realizes) = SQ.[ a ] , realizes


representative-close : ∀ {x}
  (a : RationalCauchyRepresentativeOf x) ε θ →
  R.ι (a .fst .fst ε) R.∼[ ε +₊ θ ] x
representative-close a ε θ =
  subst (R.ι (a .fst .fst ε) R.∼[ ε +₊ θ ]_)
    (a .snd)
    (RP.isLimitLim (R.ι ∘ a .fst .fst) (a .fst .snd) ε θ)


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


diagonalTerms : ∀ {x : ℚ₊ → R.ℭ} →
  (∀ ρ → RationalCauchyRepresentativeOf (x ρ)) → ℚ₊ → ℚ
diagonalTerms approximations ε =
  approximations (ε /4₊) .fst .fst ((ε /4₊) /2₊)


-- This proof is used below only through its type.  Keeping it opaque avoids
-- rechecking the nested triangle term during the realization proof.
opaque
  diagonalRegular : ∀ (x : ℚ₊ → R.ℭ)
    (xc : ∀ ε δ → x ε R.∼[ ε +₊ δ ] x δ) →
    (approximations : ∀ ρ → RationalCauchyRepresentativeOf (x ρ)) →
    ∀ ε δ →
    R.ι (diagonalTerms approximations ε)
      R.∼[ ε +₊ δ ]
    R.ι (diagonalTerms approximations δ)
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
      R.ι (diagonalTerms approximations ε)
        R.∼[ ε /4₊ ] x (ε /4₊)
    left = RP.subst∼ _ _ (/2+/2≡id (fst (ε /4₊)))
      (representative-close (approximations (ε /4₊))
        ((ε /4₊) /2₊) ((ε /4₊) /2₊))

    right :
      R.ι (diagonalTerms approximations δ)
        R.∼[ δ /4₊ ] x (δ /4₊)
    right = RP.subst∼ _ _ (/2+/2≡id (fst (δ /4₊)))
      (representative-close (approximations (δ /4₊))
        ((δ /4₊) /2₊) ((δ /4₊) /2₊))


tripleQuarter< : ∀ ε →
  ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
tripleQuarter< ε = begin<
  fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
    ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
  fst (ε /2₊ +₊ ε /4₊)
    <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
         (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
  fst (ε /2₊ +₊ ε /2₊)
    ≡→≤⟨ /2+/2≡id (fst ε) ⟩
  fst ε ◾


diagonalRepresentative : ∀ (x : ℚ₊ → R.ℭ)
  (xc : ∀ ε δ → x ε R.∼[ ε +₊ δ ] x δ) →
  (∀ ρ → RationalCauchyRepresentativeOf (x ρ)) →
  RationalCauchyRepresentativeOf (R.lim x xc)
diagonalRepresentative x xc approximations .fst .fst =
  diagonalTerms approximations
diagonalRepresentative x xc approximations .fst .snd =
  diagonalRegular x xc approximations
diagonalRepresentative x xc approximations .snd =
  R.eqℭ _ _ λ ε →
    RPremetric.isMonotone≈< _ _ _ ε
      (tripleQuarter< ε)
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
    R.lim (R.ι ∘ diagonalTerms approximations)
      (diagonalRegular x xc approximations)
      R.∼[ ε /4₊ ]
    R.ι (diagonalTerms approximations (sample ε))
  limit-to-sample ε = RP.isSym∼ _ _ (ε /4₊)
    (RP.subst∼ _ _ (/2+/2≡id (fst (ε /4₊)))
      (RP.isLimitLim (R.ι ∘ diagonalTerms approximations)
        (diagonalRegular x xc approximations) (sample ε) (sample ε)))

  sample-to-source : ∀ ε →
    R.ι (diagonalTerms approximations (sample ε))
      R.∼[ ε /4₊ ] x (outer ε)
  sample-to-source ε =
    RPremetric.isMonotone≈< _ _ (outer ε) (ε /4₊)
      (outer<quarter ε)
      (RP.subst∼ _ _ (/2+/2≡id (fst (outer ε)))
        (representative-close (approximations (outer ε))
          ((outer ε) /2₊) ((outer ε) /2₊)))

  source-to-limit : ∀ ε →
    x (outer ε) R.∼[ ε /4₊ ] R.lim x xc
  source-to-limit ε =
    RPremetric.isMonotone≈< _ _ (outer ε +₊ outer ε) (ε /4₊)
      (halfOuterSum<quarter ε)
      (RP.isLimitLim x xc (outer ε) (outer ε))


-- Quotient surjectivity recovers only a truncated representative.  Applying
-- it independently to the induction hypotheses therefore gives the left
-- side of `RationalCauchyRepresentativeChoice` below, not its right side.

merelyRepresentative : ∀ {x} →
  RationalCauchyApproximationOf x →
  ∥ RationalCauchyRepresentativeOf x ∥₁
merelyRepresentative (a , realizes) = PT.map
  (λ (raw , raw→a) →
    raw , cong classLimit raw→a ∙ realizes)
  (SQ.[]surjective a)


pointwiseMerelyRepresentative : ∀ {x : ℚ₊ → R.ℭ} →
  (∀ ρ → RationalCauchyApproximationOf (x ρ)) →
  ∀ ρ → ∥ RationalCauchyRepresentativeOf (x ρ) ∥₁
pointwiseMerelyRepresentative IH ρ = merelyRepresentative (IH ρ)


-- This is the precise choice map required by the raw diagonal.  The index
-- type is `ℚ₊`, and `xc` restricts the family to the Cauchy families which
-- can occur as the first argument of the completion constructor `R.lim`.

RationalCauchyRepresentativeChoice : Type₀
RationalCauchyRepresentativeChoice =
  (x : ℚ₊ → R.ℭ) →
  (xc : ∀ ε δ → x ε R.∼[ ε +₊ δ ] x δ) →
  (∀ ρ → ∥ RationalCauchyRepresentativeOf (x ρ) ∥₁) →
  ∥ (∀ ρ → RationalCauchyRepresentativeOf (x ρ)) ∥₁


-- This quotient-level closure is exactly, and only, what the proposition
-- eliminator's `limA` field asks us to construct.

record RationalApproximationLimitClosure : Type₀ where

  no-eta-equality

  field
    diagonal : ∀ x xc →
      (∀ ρ → RationalCauchyApproximationOf (x ρ)) →
      RationalCauchyApproximationOf (R.lim x xc)

open RationalApproximationLimitClosure public


representativeChoice→limitClosure :
  RationalCauchyRepresentativeChoice →
  RationalApproximationLimitClosure
representativeChoice→limitClosure choose .diagonal x xc IH =
  PT.rec
    (isPropRationalCauchyApproximationOf (R.lim x xc))
    (representative→class ∘ diagonalRepresentative x xc)
    (choose x xc (pointwiseMerelyRepresentative IH))


rationalApproximationEliminator :
  RationalApproximationLimitClosure →
  RE.Elimℭ-Prop RationalCauchyApproximationOf
rationalApproximationEliminator closure .RE.Elimℭ-Prop.ιA =
  rationalHasApproximation
rationalApproximationEliminator closure .RE.Elimℭ-Prop.limA x xc IH =
  closure .diagonal x xc IH
rationalApproximationEliminator closure .RE.Elimℭ-Prop.isPropA =
  isPropRationalCauchyApproximationOf


eliminator→limitClosure :
  RE.Elimℭ-Prop RationalCauchyApproximationOf →
  RationalApproximationLimitClosure
eliminator→limitClosure eliminator .diagonal x xc IH =
  eliminator .RE.Elimℭ-Prop.limA x xc IH


allRealsHaveRationalApproximation :
  RationalApproximationLimitClosure →
  ∀ x → RationalCauchyApproximationOf x
allRealsHaveRationalApproximation closure =
  RE.Elimℭ-Prop.go (rationalApproximationEliminator closure)


allRealsHaveRationalApproximationWithChoice :
  RationalCauchyRepresentativeChoice →
  ∀ x → RationalCauchyApproximationOf x
allRealsHaveRationalApproximationWithChoice choose =
  allRealsHaveRationalApproximation
    (representativeChoice→limitClosure choose)
