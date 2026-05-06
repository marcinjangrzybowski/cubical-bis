module Cubical.Tactics.CommRingSolver.RationalsExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals hiding (_+_ ; _·_ ; _-_; -_)
open import Cubical.Data.Rationals.Inverse renaming (_/_ to _/₊_)

open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.CommAlgebra

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

-- -- imports to obtain `fromNat` instances
open import Cubical.Data.NatPlusOne
import Cubical.Data.Int as ℤ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

-- private
--   variable
--     ℓ ℓ' : Level

-- open ℚRingSolver


module TestWithℚ (v : ℕ → ℚ) where
 open CommRingStr (ℚCommRing .snd)

 _ : 5 · v 0 + 190 · v 1 +  6 · v 0 ≡ (v 1 · 100 + 11 · v 0 +  v 1 · 90)
 _ = ℚ!!


 e0 : ∀ ((x , y , z) : ℚ × ℚ × ℚ)  → 4 · (([ 1 / 6 ] · x) + (x · [ 1 / 3 ])) + (z · (2 - [ 8 / 4 ]))  + y ≡ x + y + x + z - z
 e0 _ = ℚ!!


 zzz : ((ε , δ , (η , _)) : ℚ₊ × ℚ₊ × (ℚ₊ × Unit)) → 
        fst ε + [ ℤ.negsuc 0 , (1+ 0) ] · fst δ +
                       [ -1 , 1 ] · fst η ≡
                        fst ε + [ -1 , 1 ] · (fst η + fst δ)
 zzz _ = ℚ!!


 ex13 :  (x y : ℚ) → ((x · y) · 1r) + x ≡ ((y · x) · 1r) + (x)
 ex13 x y = ℚ!


 ex13'' :  (x y : ℚ) → ((x · y) · 1r) + max x (- x) ≡ ((y · x) · 1r) + abs x
 ex13'' x y = ℚ!


 -- -- ex13' :  (x : ℚ₊) (y : ℚ) → ((abs (fst x) · y) · 1r) ≡ ((y · (fst x)) · 1r) · (fst x) · fst (x ⁻¹₊)
 -- -- ex13' x y = ℚ!
