module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.LatchingAttachment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (EquivJ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (PushoutAlongEquiv)
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)

-- A latching attachment glues each degenerate cell together with its
-- whole interior, as well as the boundary of every cell. The overlaps
-- are retained by PushProd, so no complement of degenerate cells is used.
module _ {ℓD ℓC} {B D : Type ℓD}
  (boundary : B → D) (C : Type ℓC) where

  private
    cancel : (z : PushProd boundary (idfun C)) →
      inr ((boundary ×̂ idfun C) z) ≡ z
    cancel (inl (b , c)) = sym (push (b , c))
    cancel (inr (d , c)) = refl
    cancel (push (b , c) i) j = push (b , c) (i ∨ ~ j)

  identityLatchingIso : Iso (PushProd boundary (idfun C)) (D × C)
  Iso.fun identityLatchingIso = boundary ×̂ idfun C
  Iso.inv identityLatchingIso = inr
  Iso.sec identityLatchingIso _ = refl
  Iso.ret identityLatchingIso = cancel

-- When the latching map is an equivalence, its pushout-product is an
-- equivalence for any boundary map, in every dimension.
module _ {ℓD ℓC} {B D : Type ℓD} {C : Type ℓC}
  (boundary : B → D) where

  isEquivLatchingProduct : {L : Type ℓC} (e : L ≃ C) →
    isEquiv (boundary ×̂ fst e)
  isEquivLatchingProduct = EquivJ
    (λ L e → isEquiv (boundary ×̂ fst e))
    (isoToIsEquiv (identityLatchingIso boundary C))

  degenerateAttachmentIso : ∀ {ℓR} {L : Type ℓC} {R : Type ℓR}
    (e : L ≃ C) (attach : PushProd boundary (fst e) → R) →
    Iso (Pushout (boundary ×̂ fst e) attach) R
  degenerateAttachmentIso e attach =
    PushoutAlongEquiv ((boundary ×̂ fst e) , isEquivLatchingProduct e) attach

-- The two degeneracy families of the terminal square meet in the
-- doubly constant point. Keep this overlap as an actual pushout.
TerminalLatching₂ : Type
TerminalLatching₂ = Pushout (idfun Unit) (idfun Unit)

terminalLatchingMap : TerminalLatching₂ → Unit
terminalLatchingMap _ = tt

terminalLatchingIso : Iso TerminalLatching₂ Unit
Iso.fun terminalLatchingIso = terminalLatchingMap
Iso.inv terminalLatchingIso _ = inl tt
Iso.sec terminalLatchingIso tt = refl
Iso.ret terminalLatchingIso (inl tt) = refl
Iso.ret terminalLatchingIso (inr tt) = push tt
Iso.ret terminalLatchingIso (push tt i) j = push tt (i ∧ j)

-- This is a checked cancellation theorem for the terminal degree-two
-- latching object. It applies to arbitrary higher types R, not just sets.
terminalAttachmentIso : ∀ {ℓD ℓR} {B D : Type ℓD} {R : Type ℓR}
  (boundary : B → D) (attach : PushProd boundary terminalLatchingMap → R) →
  Iso (Pushout (boundary ×̂ terminalLatchingMap) attach) R
terminalAttachmentIso boundary =
  degenerateAttachmentIso boundary (isoToEquiv terminalLatchingIso)
