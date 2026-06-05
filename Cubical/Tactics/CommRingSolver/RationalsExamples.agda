module Cubical.Tactics.CommRingSolver.RationalsExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals hiding (_+_ ; _·_ ; _-_; -_)
open import Cubical.Data.Rationals.Inverse -- renaming (_/_ to _/₊_)

open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.CommAlgebra

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Data.NatPlusOne
import Cubical.Data.Int as ℤ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open PositiveRationals




module TestWithℚ (v : ℕ → ℚ) where
 open CommRingStr (ℚCommRing .snd)

 

 testS : ∀ m p →  [ m , p ] ≡ [ m / p ] + [ m / p ] - [ m / p ]
 testS m p = ℚ!!
 
 testS' : ∀ m p → - [ 26 , 2 ] + [ m , p ] ≡ [ 1 , 1 ] + [ 2 , 1 ] · (- [ 7 , 1 ]) + [ m / p ] + [ m / p ] - [ m / p ]
 testS' m p = ℚ!!

 linearCombination : 5 · v 0 + 190 · v 1 + 6 · v 0 ≡ v 1 · 100 + 11 · v 0 + v 1 · 90
 linearCombination = ℚ!!

 e0 : ∀ ((x , y , z) : ℚ × ℚ × ℚ) →
      4 · (([ 1 / 6 ] · x) + (x · [ 1 / 3 ])) + (z · (2 - [ 8 / 4 ])) + y
      ≡ x + y + x + z - z
 e0 _ = ℚ!!

 positiveCancellation : (ε δ η : ℚ₊) →
                        fst ε + [ ℤ.negsuc 0 , 1+ 0 ] · fst δ + [ -1 , 1 ] · fst η
                        ≡ fst ε + [ -1 , 1 ] · (fst η + fst δ)
 positiveCancellation ε δ η = ℚ!!

 commutedProductWithExtraTerm : (x y : ℚ) → (x · y) · 1r + x ≡ (y · x) · 1r + x
 commutedProductWithExtraTerm x y = ℚ!!

 fractionLiterals : [ 2 / 3 ] + [ 1 / 6 ] ≡ [ 5 / 6 ]
 fractionLiterals = ℚ!!

 negativeFractionLiterals : - [ 1 / 2 ] + [ 3 / 2 ] ≡ 1
 negativeFractionLiterals = ℚ!!

 distributeOverFraction : (x y : ℚ) →
                          (x + y) · [ 1 / 2 ] ≡ x · [ 1 / 2 ] + y · [ 1 / 2 ]
 distributeOverFraction x y = ℚ!!

 inverseSubtermAsVariable : (ε : ℚ₊) →
                            fst (ε ⁻¹₊) + 0 ≡ fst (ε ⁻¹₊)
 inverseSubtermAsVariable ε = ℚ!!

 positiveInverseMixedWithPlainVar : (ε : ℚ₊) (x : ℚ) →
                                   x · fst (ε ⁻¹₊) + x · fst ε
                                   ≡ x · (fst ε + fst (ε ⁻¹₊))
 positiveInverseMixedWithPlainVar ε x = ℚ!!



