module Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup


-- Prove these paths once on real variables.  Opaque boundaries keep clients
-- from normalizing completed functions or proof-dependent interval points.
opaque
  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x

  negSub : ∀ x y → - (x - y) ≡ y - x
  negSub x y =
    negAdd x (- y)
    ∙ cong ((- x) +_) (negInvol y)
    ∙ addComm (- x) y

  differenceOfSums : ∀ a b c d →
    (a + b) - (c + d) ≡ (a - c) + (b - d)
  differenceOfSums a b c d =
    cong ((a + b) +_) (negAdd c d)
    ∙ sym (addAssoc a b ((- c) + (- d)))
    ∙ cong (a +_) (addAssoc b (- c) (- d))
    ∙ cong (λ value → a + (value + (- d))) (addComm b (- c))
    ∙ cong (a +_) (sym (addAssoc (- c) b (- d)))
    ∙ addAssoc a (- c) (b + (- d))

  differenceOfNegatives : ∀ a b →
    (- a) - (- b) ≡ - (a - b)
  differenceOfNegatives a b =
    cong ((- a) +_) (negInvol b)
    ∙ addComm (- a) b
    ∙ sym (negSub a b)
