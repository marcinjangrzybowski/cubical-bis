module Cubical.HITs.CauchyRealsP.Analysis.Pasting.ClosedLower where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval
open import Cubical.HITs.CauchyRealsP.Analysis.Pasting.Continuous

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open CategoryStructures

-- Paste a continuous bounded piece [b,junction] to a continuous right-hand
-- piece [junction,∞), returning a map on [b,∞).  The lower clamp turns the
-- bounded piece into exactly the upper-half-line input expected by pasteAtC.
pasteAboveClosedC : ∀ b junction →
  b ≤ℝ junction →
  C[ ClosedIntervalPremetricSpace b junction , ℝPremetricSpace ] →
  C[ LowerClosedHalfLinePremetricSpace junction , ℝPremetricSpace ] →
  C[ LowerClosedHalfLinePremetricSpace b , ℝPremetricSpace ]
pasteAboveClosedC b junction b≤junction left right =
  pasteAtC junction left-on-upper right
    ∘C NE→C (lowerClosedHalfLineInclusionNE b)
  where
  left-on-upper :
    C[ UpperClosedHalfLinePremetricSpace junction , ℝPremetricSpace ]
  left-on-upper =
    left ∘C NE→C
      (lowerClampToClosedIntervalNE b junction b≤junction)

pasteAboveClosedC-left : ∀ b junction b≤junction left right →
  fst left (junction , b≤junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  ∀ x (b≤x : b ≤ℝ x) (x≤junction : x ≤ℝ junction) →
  fst (pasteAboveClosedC b junction b≤junction left right)
      (x , b≤x)
    ≡ fst left (x , b≤x , x≤junction)
pasteAboveClosedC-left
  b junction b≤junction left right agrees x b≤x x≤junction =
    pasteAtC-left
      junction left-on-upper right clamped-agrees x x≤junction
    ∙ cong (fst left)
        (lowerClampToClosedIntervalSection
          b junction b≤junction
          (x , b≤x , x≤junction))
  where
  left-on-upper :
    C[ UpperClosedHalfLinePremetricSpace junction , ℝPremetricSpace ]
  left-on-upper =
    left ∘C NE→C
      (lowerClampToClosedIntervalNE b junction b≤junction)

  clamped-agrees :
    fst left-on-upper (junction , ≤ℝ-refl junction)
      ≡ fst right (junction , ≤ℝ-refl junction)
  clamped-agrees =
    cong (fst left)
      (lowerClampToClosedIntervalSection
        b junction b≤junction
        (junction , b≤junction , ≤ℝ-refl junction))
    ∙ agrees

pasteAboveClosedC-right : ∀ b junction b≤junction left right →
  fst left (junction , b≤junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  ∀ x (b≤x : b ≤ℝ x) (junction≤x : junction ≤ℝ x) →
  fst (pasteAboveClosedC b junction b≤junction left right)
      (x , b≤x)
    ≡ fst right (x , junction≤x)
pasteAboveClosedC-right
  b junction b≤junction left right agrees x b≤x junction≤x =
    pasteAtC-right
      junction left-on-upper right clamped-agrees x junction≤x
  where
  left-on-upper :
    C[ UpperClosedHalfLinePremetricSpace junction , ℝPremetricSpace ]
  left-on-upper =
    left ∘C NE→C
      (lowerClampToClosedIntervalNE b junction b≤junction)

  clamped-agrees :
    fst left-on-upper (junction , ≤ℝ-refl junction)
      ≡ fst right (junction , ≤ℝ-refl junction)
  clamped-agrees =
    cong (fst left)
      (lowerClampToClosedIntervalSection
        b junction b≤junction
        (junction , b≤junction , ≤ℝ-refl junction))
    ∙ agrees

pasteAboveClosedC-properties : ∀ b junction b≤junction left right →
  fst left (junction , b≤junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  (∀ x (b≤x : b ≤ℝ x) (x≤junction : x ≤ℝ junction) →
    fst (pasteAboveClosedC b junction b≤junction left right)
        (x , b≤x)
      ≡ fst left (x , b≤x , x≤junction))
  ×
  (∀ x (b≤x : b ≤ℝ x) (junction≤x : junction ≤ℝ x) →
    fst (pasteAboveClosedC b junction b≤junction left right)
        (x , b≤x)
      ≡ fst right (x , junction≤x))
pasteAboveClosedC-properties b junction b≤junction left right agrees =
  pasteAboveClosedC-left
    b junction b≤junction left right agrees
  , pasteAboveClosedC-right
      b junction b≤junction left right agrees
