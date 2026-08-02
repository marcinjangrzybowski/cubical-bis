module Cubical.HITs.CauchyRealsP.Analysis.Pasting.StrictLower where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open CategoryStructures

-- The strict lower endpoint is deliberately not filled in.  Both min and
-- max act directly on the open half-line, so continuity requires no choice
-- of a value at b.
pasteAboveC : ∀ b junction →
  b <ℝ junction →
  C[ LeftOpenRightClosedIntervalPremetricSpace b junction
    , ℝPremetricSpace ] →
  C[ LowerClosedHalfLinePremetricSpace junction , ℝPremetricSpace ] →
  C[ LowerOpenHalfLinePremetricSpace b , ℝPremetricSpace ]
pasteAboveC b junction b<junction left right =
  subtract-endpoint ∘C sum-of-pieces
  where
  left-on-domain :
    C[ LowerOpenHalfLinePremetricSpace b , ℝPremetricSpace ]
  left-on-domain =
    left ∘C NE→C
      (minToLeftOpenRightClosedIntervalNE b junction b<junction)

  right-on-domain :
    C[ LowerOpenHalfLinePremetricSpace b , ℝPremetricSpace ]
  right-on-domain =
    right ∘C NE→C
      (maxFromLowerOpenToLowerClosedHalfLineNE b junction)

  sum-of-pieces :
    C[ LowerOpenHalfLinePremetricSpace b , ℝPremetricSpace ]
  fst sum-of-pieces point =
    fst right-on-domain point + fst left-on-domain point
  snd sum-of-pieces =
    addOfContinuousIsContinuous
      (snd (LowerOpenHalfLinePremetricSpace b))
      (fst right-on-domain)
      (fst left-on-domain)
      (snd right-on-domain)
      (snd left-on-domain)

  subtract-endpoint : C[ ℝPremetricSpace , ℝPremetricSpace ]
  subtract-endpoint =
    NE→C
      ( ( _- fst left
            (junction , b<junction , ≤ℝ-refl junction))
      , subIsNonExpanding₁
          (fst left
            (junction , b<junction , ≤ℝ-refl junction))
      )

pasteAboveC-left : ∀ b junction b<junction left right →
  fst left (junction , b<junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  ∀ x (b<x : b <ℝ x) (x≤junction : x ≤ℝ junction) →
  fst (pasteAboveC b junction b<junction left right) (x , b<x)
    ≡ fst left (x , b<x , x≤junction)
pasteAboveC-left
  b junction b<junction left right agrees x b<x x≤junction =
    cong₂
      (λ right-value left-value →
        (right-value + left-value) - endpoint)
      (cong (fst right)
        (maxFromLowerOpenToLowerClosedHalfLineOnLeft
          b junction x b<x x≤junction))
      (cong (fst left)
        (minToLeftOpenRightClosedIntervalSection
          b junction b<junction
          (x , b<x , x≤junction)))
    ∙ cong (_- endpoint)
        (addComm
          (fst right (junction , ≤ℝ-refl junction))
          (fst left (x , b<x , x≤junction)))
    ∙ cong
        (λ value →
          (fst left (x , b<x , x≤junction) + value) - endpoint)
        (sym agrees)
    ∙ addSubCancel
        (fst left (x , b<x , x≤junction)) endpoint
  where
  endpoint : ℝ
  endpoint =
    fst left (junction , b<junction , ≤ℝ-refl junction)

pasteAboveC-right : ∀ b junction b<junction left right →
  ∀ x (b<x : b <ℝ x) (junction≤x : junction ≤ℝ x) →
  fst (pasteAboveC b junction b<junction left right) (x , b<x)
    ≡ fst right (x , junction≤x)
pasteAboveC-right
  b junction b<junction left right x b<x junction≤x =
    cong₂
      (λ right-value left-value →
        (right-value + left-value) - endpoint)
      (cong (fst right)
        (maxFromLowerOpenToLowerClosedHalfLineOnRight
          b junction x b<x junction≤x))
      (cong (fst left)
        (minToLeftOpenRightClosedIntervalOnRight
          b junction b<junction x b<x junction≤x))
    ∙ addSubCancel (fst right (x , junction≤x)) endpoint
  where
  endpoint : ℝ
  endpoint =
    fst left (junction , b<junction , ≤ℝ-refl junction)

pasteAboveC-properties : ∀ b junction b<junction left right →
  fst left (junction , b<junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  (∀ x (b<x : b <ℝ x) (x≤junction : x ≤ℝ junction) →
    fst (pasteAboveC b junction b<junction left right) (x , b<x)
      ≡ fst left (x , b<x , x≤junction))
  ×
  (∀ x (b<x : b <ℝ x) (junction≤x : junction ≤ℝ x) →
    fst (pasteAboveC b junction b<junction left right) (x , b<x)
      ≡ fst right (x , junction≤x))
pasteAboveC-properties b junction b<junction left right agrees =
  pasteAboveC-left b junction b<junction left right agrees
  , pasteAboveC-right b junction b<junction left right
