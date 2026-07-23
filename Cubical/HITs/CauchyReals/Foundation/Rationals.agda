module Cubical.HITs.CauchyReals.Foundation.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Rationals.Order.AbsoluteValue


open import Cubical.Tactics.CommRingSolver.Specialised.Rationals public

open import Cubical.Tactics.CommRingSolver.OrderedReflection public


open import Cubical.Tactics.CommRingSolver public

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals public
open import Cubical.Tactics.CommRingSolver.OrderedReflection  public


open import Cubical.Algebra.CommRing.Instances.Rationals public
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing public
open import Cubical.Algebra.OrderedCommRing.Properties public
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals public

import Cubical.Algebra.CommRing as CR
open import Cubical.Algebra.CommRing.Properties public

open import Cubical.Data.Sigma
open PositiveRationals public
open PositiveHalvesℚ public
open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_) public
module ℚExponentiation = Exponentiation ℚCommRing

open import Cubical.Data.Rationals.Base public

module ℚ where
 
 open import Cubical.Data.Rationals.Base public
 open import Cubical.Data.Rationals.Properties public
 open import Cubical.Data.Rationals.Order public
 open import Cubical.Data.Rationals.Order.AbsoluteValue public
 open import Cubical.Data.Rationals.Order.Floor public
 open import Cubical.Data.Rationals.Order.Algebra public
 open import Cubical.Data.Rationals.Inverse public


ℚmax-min-minus : ∀ x y → ℚ.max (ℚ.- x) (ℚ.- y) ≡ ℚ.- (ℚ.min x y)
ℚmax-min-minus = ℚ.maxNeg≡negMin


m·n/m : ∀ m n → [ pos (suc m) / 1 ] ℚ.· [ pos n / 1+ m ] ≡ [ pos n / 1 ]
m·n/m m n = ℚ.[c/1]·[n/c]≡[n/1] (1+ m) n


abs'q≤Δ₁' : ∀ q n → ℚ.abs' q ℚ.≤ [ pos (suc n) / 1+ 0 ]
  → ℚ.abs' q ℚ.≤ ([ pos (suc (suc n)) / 1 ] ℚ.- [ 1 / 4 ])
abs'q≤Δ₁' q n q≤n = ℚ.isTrans≤ (ℚ.abs' q) (fromNat (suc n)) _
  q≤n
  (subst2 ℚ._≤_ (ℚ.+IdR _) ℚ!
    (ℚ.≤-o+ 0 [ 3 / 4 ] (fromNat (suc n))
      (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 3 / 4 ]} _)))


ℚabs-abs≤abs- : (x y : ℚ) → (abs x ℚ.- abs y) ℚ.≤ abs (x ℚ.- y)
ℚabs-abs≤abs- = abs-abs≤abs-


module Rℚ where
 ℚRing = (CR.CommRing→Ring ℚCommRing)
 open CR.CommRingStr (snd (ℚCommRing)) public
 open RingTheory ℚRing public
 open CR.CommRingTheory ℚCommRing public

 
