module Cubical.Analysis.Complex.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Complex.Base

-- The product premetric measures both coordinates at the same radius.
-- Completeness therefore needs only the two native real Cauchy witnesses;
-- no square-root construction or Euclidean-modulus comparison is needed.
ℂPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℂPremetricSpace = PremetricProduct ℝPremetricSpace ℝPremetricSpace

infix 4 _∼ℂ[_]_
_∼ℂ[_]_ : ℂ → ℚ₊ → ℂ → Type₀
z ∼ℂ[ ε ] w = (re z ∼[ ε ] re w) × (im z ∼[ ε ] im w)

reℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) re (ℝPremetricSpace .snd)
reℂ-isContinuous = snd productFstC

imℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) im (ℝPremetricSpace .snd)
imℂ-isContinuous = snd productSndC

pairℂ-isContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (f g : A → ℝ) →
  isContinuous source f (ℝPremetricSpace .snd) →
  isContinuous source g (ℝPremetricSpace .snd) →
  isContinuous source (λ x → f x , g x) (ℂPremetricSpace .snd)
pairℂ-isContinuous source f g fc gc = snd (pairC (f , fc) (g , gc))
