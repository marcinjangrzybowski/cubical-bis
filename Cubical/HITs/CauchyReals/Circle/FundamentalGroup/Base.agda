module Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast using (ℤ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval public
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.LoopGroup
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (_∘UC_)

basepoint : Circle
basepoint = injCircle 0

open Loops CirclePremetricSpace basepoint public

-- Constant extension lets the earlier winding machinery read our paths.
extendedLoop : Loop → UC[ ℝPremetricSpace , distCirclePremetricSpace ]
extendedLoop p = Circle→distCircleUC ∘UC (fst p ∘UC clipUC)

extended-start : (p : Loop) → fst (extendedLoop p) 0 ≡ Circle→distCircle basepoint
extended-start p = cong Circle→distCircle (cong (at p) (clip-fixes 𝟘) ∙ fst (snd p))

extended-end : (p : Loop) → fst (extendedLoop p) 1 ≡ Circle→distCircle basepoint
extended-end p = cong Circle→distCircle (cong (at p) (clip-fixes 𝟙) ∙ snd (snd p))

extended-closes : (p : Loop) → fst (extendedLoop p) 0 ≡ fst (extendedLoop p) 1
extended-closes p = extended-start p ∙ sym (extended-end p)

loopWinding : Loop → ℤ
loopWinding p = windingLoop (extendedLoop p) (extended-closes p)
