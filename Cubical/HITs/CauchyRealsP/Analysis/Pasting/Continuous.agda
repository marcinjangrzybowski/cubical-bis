module Cubical.HITs.CauchyRealsP.Analysis.Pasting.Continuous where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Metric.Interval
open import Cubical.HITs.CauchyRealsP.Analysis.Pasting.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open CategoryStructures

pasteAtC :
  (junction : ℝ) →
  C[ UpperClosedHalfLinePremetricSpace junction , ℝPremetricSpace ] →
  C[ LowerClosedHalfLinePremetricSpace junction , ℝPremetricSpace ] →
  C[ ℝPremetricSpace , ℝPremetricSpace ]
pasteAtC junction left right =
  subtract-endpoint ∘C sum-of-clamped-pieces
  where
  left-on-line : C[ ℝPremetricSpace , ℝPremetricSpace ]
  left-on-line =
    left ∘C NE→C (minToUpperClosedHalfLineNE junction)

  right-on-line : C[ ℝPremetricSpace , ℝPremetricSpace ]
  right-on-line =
    right ∘C NE→C (maxToLowerClosedHalfLineNE junction)

  sum-of-clamped-pieces : C[ ℝPremetricSpace , ℝPremetricSpace ]
  fst sum-of-clamped-pieces x =
    fst right-on-line x + fst left-on-line x
  snd sum-of-clamped-pieces =
    addOfContinuousIsContinuous
      (snd ℝPremetricSpace)
      (fst right-on-line)
      (fst left-on-line)
      (snd right-on-line)
      (snd left-on-line)

  subtract-endpoint : C[ ℝPremetricSpace , ℝPremetricSpace ]
  subtract-endpoint =
    NE→C
      ( ( _- fst left (junction , ≤ℝ-refl junction))
      , subIsNonExpanding₁
          (fst left (junction , ≤ℝ-refl junction))
      )

pasteAtC-function : ∀ junction left right x →
  fst (pasteAtC junction left right) x
    ≡
  pasteAt junction
    (λ y y≤junction → fst left (y , y≤junction))
    (λ y junction≤y → fst right (y , junction≤y))
    x
pasteAtC-function junction left right x = refl

pasteAtC-left : ∀ junction left right →
  fst left (junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  ∀ x (x≤junction : x ≤ℝ junction) →
  fst (pasteAtC junction left right) x
    ≡ fst left (x , x≤junction)
pasteAtC-left junction left right agrees x x≤junction =
  pasteAt-left
    junction
    (λ y y≤junction → fst left (y , y≤junction))
    (λ y junction≤y → fst right (y , junction≤y))
    agrees x x≤junction

pasteAtC-right : ∀ junction left right →
  fst left (junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  ∀ x (junction≤x : junction ≤ℝ x) →
  fst (pasteAtC junction left right) x
    ≡ fst right (x , junction≤x)
pasteAtC-right junction left right agrees x junction≤x =
  pasteAt-right
    junction
    (λ y y≤junction → fst left (y , y≤junction))
    (λ y junction≤y → fst right (y , junction≤y))
    agrees x junction≤x

pasteAtC-properties : ∀ junction left right →
  fst left (junction , ≤ℝ-refl junction)
    ≡ fst right (junction , ≤ℝ-refl junction) →
  (∀ x (x≤junction : x ≤ℝ junction) →
    fst (pasteAtC junction left right) x
      ≡ fst left (x , x≤junction))
  ×
  (∀ x (junction≤x : junction ≤ℝ x) →
    fst (pasteAtC junction left right) x
      ≡ fst right (x , junction≤x))
pasteAtC-properties junction left right agrees =
  pasteAtC-left junction left right agrees
  , pasteAtC-right junction left right agrees
