module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.ReflexiveGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; false; true)
import Cubical.HITs.S1.Base as Circle

-- A first-stage prototype, not the full cubical singular realization.
-- The chosen identity edges are collapsed without deciding whether
-- an arbitrary edge is an identity. There is no truncation constructor.
data ReflexiveRealization {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ')
  (ρ : (x : A) → R x x) : Type (ℓ-max ℓ ℓ') where
  vertex : A → ReflexiveRealization A R ρ
  edge : {x y : A} → R x y → vertex x ≡ vertex y
  refl-edge : (x : A) → edge (ρ x) ≡ refl

-- Elimination permits arbitrary higher types as targets.
module _ {ℓ ℓ' ℓB} {A : Type ℓ} {R : A → A → Type ℓ'}
  {ρ : (x : A) → R x x} {B : Type ℓB}
  (v : A → B) (e : {x y : A} → R x y → v x ≡ v y)
  (identity : (x : A) → e (ρ x) ≡ refl) where

  rec : ReflexiveRealization A R ρ → B
  rec (vertex x) = v x
  rec (edge r i) = e r i
  rec (refl-edge x i j) = identity x i j

-- For the terminal reflexive graph, the formerly spurious loop and
-- its chosen filling form a contractible disk.
TerminalRealization : Type
TerminalRealization = ReflexiveRealization Unit (λ _ _ → Unit) (λ _ → tt)

terminal-contraction : (z : TerminalRealization) → vertex tt ≡ z
terminal-contraction (vertex tt) = refl
terminal-contraction (edge {x = tt} {y = tt} tt j) i = refl-edge tt (~ i) j
terminal-contraction (refl-edge tt j k) i = refl-edge tt (j ∨ ~ i) k

isContrTerminalRealization : isContr TerminalRealization
isContrTerminalRealization = vertex tt , terminal-contraction

-- A control example: retain one additional loop. Collapsing the chosen
-- identity edge preserves precisely the synthetic circle in this case.
LoopRealization : Type
LoopRealization = ReflexiveRealization Unit (λ _ _ → Bool) (λ _ → false)

toCircle : LoopRealization → Circle.S¹
toCircle (vertex tt) = Circle.base
toCircle (edge false i) = Circle.base
toCircle (edge true i) = Circle.loop i
toCircle (refl-edge tt i j) = Circle.base

fromCircle : Circle.S¹ → LoopRealization
fromCircle Circle.base = vertex tt
fromCircle (Circle.loop i) = edge true i

to-from : (z : Circle.S¹) → toCircle (fromCircle z) ≡ z
to-from Circle.base = refl
to-from (Circle.loop j) = refl

from-to : (z : LoopRealization) → fromCircle (toCircle z) ≡ z
from-to (vertex tt) = refl
from-to (edge false j) i = refl-edge tt (~ i) j
from-to (edge true j) = refl
from-to (refl-edge tt j k) i = refl-edge tt (j ∨ ~ i) k

loopRealizationIsoCircle : Iso LoopRealization Circle.S¹
Iso.fun loopRealizationIsoCircle = toCircle
Iso.inv loopRealizationIsoCircle = fromCircle
Iso.sec loopRealizationIsoCircle = to-from
Iso.ret loopRealizationIsoCircle = from-to
