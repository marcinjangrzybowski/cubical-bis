open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Completion.UniversalProperty.Base

module Cubical.Relation.Premetric.Completion.UniversalProperty.Extensionality
  {ℓM ℓM' ℓC ℓC' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (P : CompletionPresentation M' ℓC ℓC')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures

private
  M = M' .fst
  C' = P .completionSpace
  C = C' .fst
  N = N' .fst
  ι = P .injection

module PC = PremetricStr (C' .snd)
module PN = PremetricStr (N' .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


private
  twoQuarter< : ∀ ε → (ε /4₊ +₊ ε /4₊) <₊ ε
  twoQuarter< ε = begin<
    fst (ε /4₊ +₊ ε /4₊)
      ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
    fst (ε /2₊)
      <⟨ /2₊<id ε ⟩
    fst ε ◾


-- Quantitative density determines every continuous map by its values on
-- the presented base.  No completeness or extension operation is needed.

continuousMap-ext :
  ∀ (F G : C → N) →
  isContinuous (C' .snd) F (N' .snd) →
  isContinuous (C' .snd) G (N' .snd) →
  (∀ q → F (ι q) ≡ G (ι q)) →
  F ≡ G
continuousMap-ext F G F-cont G-cont agree =
  funExt λ x → PN.isSeparated≈ (F x) (G x) (close x)
  where
  close : ∀ x ε → F x PN.≈[ ε ] G x
  close x ε =
    PT.rec2 (PN.isProp≈ (F x) (G x) ε) withRadii
      (F-cont x .IsContinuousAt.pres≈ (ε /4₊))
      (G-cont x .IsContinuousAt.pres≈ (ε /4₊))
    where
    withRadii :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ y → x PC.≈[ δ ] y →
          F x PN.≈[ ε /4₊ ] F y)) →
      (Σ[ η ∈ ℚ₊ ]
        (∀ y → x PC.≈[ η ] y →
          G x PN.≈[ ε /4₊ ] G y)) →
      F x PN.≈[ ε ] G x
    withRadii (δ , F-near) (η , G-near) =
      PT.rec (PN.isProp≈ (F x) (G x) ε) withApproximation
        (P .dense x sourceRadius)
      where
      sourceRadius = min₊ δ η /2₊

      withApproximation :
        (Σ[ q ∈ M ] (ι q PC.≈[ sourceRadius ] x)) →
        F x PN.≈[ ε ] G x
      withApproximation (q , ιq≈x) =
        PN.isMonotone≈< (F x) (G x)
          (ε /4₊ +₊ ε /4₊) ε (twoQuarter< ε)
          (PN.isTriangular≈ (F x) (F (ι q)) (G x)
            (ε /4₊) (ε /4₊)
            (F-near (ι q)
              (PC.isMonotone≈< x (ι q) sourceRadius δ
                (min/2₊<L δ η)
                (PC.isSym≈ (ι q) x sourceRadius ιq≈x)))
            (subst (λ z → z PN.≈[ ε /4₊ ] G x)
              (sym (agree q))
              (PN.isSym≈ (G x) (G (ι q)) (ε /4₊)
                (G-near (ι q)
                  (PC.isMonotone≈< x (ι q) sourceRadius η
                    (min/2₊<R δ η)
                    (PC.isSym≈ (ι q) x sourceRadius ιq≈x))))))


nonExpandingMap-ext :
  ∀ (F G : NE[ C' , N' ]) →
  (∀ q → fst F (ι q) ≡ fst G (ι q)) →
  F ≡ G
nonExpandingMap-ext F G agree =
  NE≡ (continuousMap-ext (fst F) (fst G)
    (isNonExpanding→isContinuous
      (C' .snd) (fst F) (N' .snd) (snd F))
    (isNonExpanding→isContinuous
      (C' .snd) (fst G) (N' .snd) (snd G))
    agree)
