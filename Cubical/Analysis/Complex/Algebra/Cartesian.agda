module Cubical.Analysis.Complex.Algebra.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

-- Coordinate algebra is independent of the construction of the real numbers.
-- Proving it over an abstract ring also keeps completion terms out of the
-- normalization performed by the ring solver.
module Cartesian {ℓ} (R : CommRing ℓ) where
  private
    A = fst R
  open CommRingStr (snd R)

  Pair : Type ℓ
  Pair = A × A

  infixl 6 _+ℂ_ _-ℂ_
  infixl 7 _·ℂ_
  infix 8 -ℂ_

  0ℂ 1ℂ iℂ : Pair
  0ℂ = 0r , 0r
  1ℂ = 1r , 0r
  iℂ = 0r , 1r

  embed : A → Pair
  embed x = x , 0r

  _+ℂ_ : Pair → Pair → Pair
  (a , b) +ℂ (c , d) = (a + c) , (b + d)

  -ℂ_ : Pair → Pair
  -ℂ (a , b) = (- a) , (- b)

  _-ℂ_ : Pair → Pair → Pair
  z -ℂ w = z +ℂ (-ℂ w)

  _·ℂ_ : Pair → Pair → Pair
  (a , b) ·ℂ (c , d) = (a · c - b · d) , (a · d + b · c)

  +ℂAssoc : ∀ z w u → z +ℂ (w +ℂ u) ≡ (z +ℂ w) +ℂ u
  +ℂAssoc (a , b) (c , d) (e , f) = cong₂ _,_ (+Assoc a c e) (+Assoc b d f)

  +ℂIdR : ∀ z → z +ℂ 0ℂ ≡ z
  +ℂIdR (a , b) = cong₂ _,_ (+IdR a) (+IdR b)

  +ℂInvR : ∀ z → z +ℂ (-ℂ z) ≡ 0ℂ
  +ℂInvR (a , b) = cong₂ _,_ (+InvR a) (+InvR b)

  +ℂComm : ∀ z w → z +ℂ w ≡ w +ℂ z
  +ℂComm (a , b) (c , d) = cong₂ _,_ (+Comm a c) (+Comm b d)

  ·ℂAssoc : ∀ z w u → z ·ℂ (w ·ℂ u) ≡ (z ·ℂ w) ·ℂ u
  ·ℂAssoc (a , b) (c , d) (e , f) =
    cong₂ _,_ (solve! R) (solve! R)

  ·ℂIdR : ∀ z → z ·ℂ 1ℂ ≡ z
  ·ℂIdR (a , b) = cong₂ _,_ (solve! R) (solve! R)

  ·ℂDistR+ : ∀ z w u → z ·ℂ (w +ℂ u) ≡ (z ·ℂ w) +ℂ (z ·ℂ u)
  ·ℂDistR+ (a , b) (c , d) (e , f) =
    cong₂ _,_ (solve! R) (solve! R)

  ·ℂComm : ∀ z w → z ·ℂ w ≡ w ·ℂ z
  ·ℂComm (a , b) (c , d) = cong₂ _,_ (solve! R) (solve! R)

  pairCommRing : CommRing ℓ
  pairCommRing = makeCommRing 0ℂ 1ℂ _+ℂ_ _·ℂ_ -ℂ_
    (isSet× is-set is-set)
    +ℂAssoc +ℂIdR +ℂInvR +ℂComm
    ·ℂAssoc ·ℂIdR ·ℂDistR+ ·ℂComm

  i²≡-1 : iℂ ·ℂ iℂ ≡ -ℂ 1ℂ
  i²≡-1 = cong₂ _,_ (solve! R) (solve! R)

  embed-pres+ : ∀ x y → embed (x + y) ≡ embed x +ℂ embed y
  embed-pres+ x y = cong₂ _,_ refl (sym (+IdR 0r))

  embed-pres· : ∀ x y → embed (x · y) ≡ embed x ·ℂ embed y
  embed-pres· x y = cong₂ _,_ (solve! R) (solve! R)

  embedHom : CommRingHom R pairCommRing
  embedHom = embed , makeIsCommRingHom refl embed-pres+ embed-pres·
