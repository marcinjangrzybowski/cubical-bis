module Cubical.Analysis.Real.Extensionality where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Analysis.Completion.Extensionality
  as ExtensionalityDefinition

private module Ext = ExtensionalityDefinition ℚPremetricSpace


-- Metric extensionality for the sequence-backed real presentation.  Keeping
-- this surface separate prevents algebraic laws from importing the stronger
-- graph-Cauchy mapping-space universal property.

continuousExtensionality :
  (f g : ℝ → ℝ) →
  isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
  isContinuous (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
  (∀ q → f (rat q) ≡ g (rat q)) →
  f ≡ g
continuousExtensionality = Ext.continuousExtensionality ℝPremetricSpace

continuousExtensionality₂ :
  (f g : ℝ → ℝ → ℝ) →
  (∀ y → isContinuous (ℝPremetricSpace .snd)
    (λ x → f x y) (ℝPremetricSpace .snd)) →
  (∀ x → isContinuous (ℝPremetricSpace .snd)
    (f x) (ℝPremetricSpace .snd)) →
  (∀ y → isContinuous (ℝPremetricSpace .snd)
    (λ x → g x y) (ℝPremetricSpace .snd)) →
  (∀ x → isContinuous (ℝPremetricSpace .snd)
    (g x) (ℝPremetricSpace .snd)) →
  (∀ p q → f (rat p) (rat q) ≡ g (rat p) (rat q)) →
  ∀ x y → f x y ≡ g x y
continuousExtensionality₂ =
  Ext.continuousExtensionality₂ ℝPremetricSpace

continuousExtensionality₃ :
  (f g : ℝ → ℝ → ℝ → ℝ) →
  (∀ y z → isContinuous (ℝPremetricSpace .snd)
    (λ x → f x y z) (ℝPremetricSpace .snd)) →
  (∀ x z → isContinuous (ℝPremetricSpace .snd)
    (λ y → f x y z) (ℝPremetricSpace .snd)) →
  (∀ x y → isContinuous (ℝPremetricSpace .snd)
    (f x y) (ℝPremetricSpace .snd)) →
  (∀ y z → isContinuous (ℝPremetricSpace .snd)
    (λ x → g x y z) (ℝPremetricSpace .snd)) →
  (∀ x z → isContinuous (ℝPremetricSpace .snd)
    (λ y → g x y z) (ℝPremetricSpace .snd)) →
  (∀ x y → isContinuous (ℝPremetricSpace .snd)
    (g x y) (ℝPremetricSpace .snd)) →
  (∀ p q r →
    f (rat p) (rat q) (rat r) ≡
    g (rat p) (rat q) (rat r)) →
  ∀ x y z → f x y z ≡ g x y z
continuousExtensionality₃ =
  Ext.continuousExtensionality₃ ℝPremetricSpace
