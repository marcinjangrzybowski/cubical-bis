{-# OPTIONS --quote-metas #-}
module Cubical.Tactics.CommRingSolver.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Int.Base hiding (_+_ ; _·_ ; _-_ ; -_)
open import Cubical.Data.List
open import Cubical.Data.List.Dependent using (_∷_; P[_]; [])
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Nat using (ℕ; suc; zero)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommAlgebra

open import Cubical.Relation.Binary

open import Cubical.Tactics.CommRingSolver renaming (solve! to generic-solve!)

private
  variable
    ℓ ℓ' : Level

















module Test0intDom (R : CommRing ℓ) (isIntDom : _) where
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R) renaming (fromℤ to scalar)

  open SolveOverℤ.Reasonable R isIntDom

  relTrans : BinaryRelation.isTrans {A = ((fst R) × (Σ[ b ∈ (fst R) ] (b ≡ 0r → ⊥)))}
               λ  (a , (b , _)) (c , (d , _)) → a · d ≡ c · b
  relTrans (a , (b , _)) (a' , (b' , b'≢0)) (a'' , (b'' , _)) p q =
    sym (equalByDifference _ _ (solve! ∙ w))
   where
    w : - (a · b'') + b · a'' ≡ 0r
    w = eliminate! a' p q P[ b'≢0 ]
    
module Test (R : CommRing ℓ) (x y z w v : fst R) where
  open CommRingStr (snd R)
  open RingTheory (CommRing→Ring R) using () renaming (fromℤ to scalar ; fromℕ to ⟨_⟩ₙ)
  open Exponentiation R using (_^_)

  open SolveOverℤ.Generic

  _ : 0r ≡ 0r
  _ = solve! R

  _ : 1r ≡ 1r
  _ = solve! R


  _ :   1r · (1r + 0r)
      ≡ (1r · 0r) + 1r
  _ = solve! R

  _ :   1r · 0r + (1r - 1r)
      ≡ 0r - 0r
  _ = solve! R

  ex1 : x ≡ x
  ex1 = solve! R

  ex2 : (0r - 1r) · x ≡ 0r - x
  ex2 = solve! R

  ex3 : x + y ≡ y + x
  ex3 = solve! R

  ex4 : y ≡ (y - x) + x
  ex4 = solve! R


  ex5 : x ≡ (x - y) + y
  ex5 = solve! R

  ex6 : (x + y) · (x - y) ≡ x · x - y · y
  ex6 = solve! R

  exDistrib4 : (x + y) · (z + w) ≡ x · z + x · w + y · z + y · w
  exDistrib4 = solve! R

  exNestedMinus : - (x - y) ≡ y - x
  exNestedMinus = solve! R

  exScalarCollect : scalar 3 · x + scalar 4 · x ≡ scalar 7 · x
  exScalarCollect = solve! R

  exScalarMixedSigns : scalar 5 · x - scalar 2 · x ≡ scalar 3 · x
  exScalarMixedSigns = solve! R


  ex8 : x · 0r ≡ 0r
  ex8 = solve! R

  ex9 : x · (y - z) ≡ x · y - x · z
  ex9 = solve! R

  pow : ℕ → fst R → fst R
  pow zero a = 1r
  pow (suc n) a = a · pow n a

  module NonPolynomialSubterms (f : fst R → fst R) (n : ℕ) where
    ex10 : (a : fst R) → pow n a + 0r ≡ pow n a
    ex10 a = solve! R

    ex11 : (a : fst R) → f a + 0r ≡ f a
    ex11 a = solve! R

    ex12 : (a : fst R) → (f a + x) · y ≡ y · f a + y · x
    ex12 a = solve! R

  testWithTwoVariables : x + y ≡ y + x
  testWithTwoVariables =
    x + y ≡⟨ solve! R ⟩
    y + x ∎

  testEquationalReasoning : x + 0r ≡ 0r + x
  testEquationalReasoning =
    x + 0r ≡⟨ solve! R ⟩
    0r + x ∎

  testEquationalReasoning' : (p : 0r + x ≡ 1r) → x + 0r ≡ 1r
  testEquationalReasoning' p =
    x + 0r ≡⟨ solve! R ⟩
    0r + x ≡⟨ p ⟩
    1r ∎

  ex7 : (x + y) · (x + y) · (x + y) · (x + y)
                ≡ x · x · x · x + (scalar 4) · x · x · x · y + (scalar 6) · x · x · y · y
                  + (scalar 4) · x · y · y · y + y · y · y · y
  ex7 = solve! R

  exCube : (x + y) · (x + y) · (x + y)
           ≡ x · x · x + scalar 3 · x · x · y + scalar 3 · x · y · y + y · y · y
  exCube = solve! R

  module _ (p : _)
           (p1 : _) where
   ex7' : v + z · x + y + w · x + (- w) + v ≡ (scalar 2 · v) + x + y + x + scalar 2
   ex7' =
    ring! R (v ∷ y ∷ x ∷ [])
       (p ∷ P[ p1 ])

  exNorm0 : (x + y + y + x - y  + scalar 5  -  x + (- scalar 1)) · x · (scalar 3) ≡
            (⟨ 3 ⟩ₙ · x · (⟨ 4 ⟩ₙ + y + x))
  exNorm0 = normalize! R


  exNorm : (x + y) · ((x + x) - y - y) + scalar 5 + (- scalar 1) ≡
            (⟨ 2 ⟩ₙ · (⟨ 2 ⟩ₙ + x ^ 2 - y ^ 2))
  exNorm = normalize! R


  exNorm2 : v + z · x + y + w · x + (- w) + v + (scalar 2 · v) + x + y + x + scalar 2 ≡
             (⟨ 2 ⟩ₙ - w + ⟨ 4 ⟩ₙ · v + ⟨ 2 ⟩ₙ · y + ⟨ 2 ⟩ₙ · x + z · x + w · x)
  exNorm2 = normalize! R


  exNorm3 : - (y + z) + ( - y - z)  - x - x · ⟨ 3 ⟩ₙ ≡
               (- ⟨ 2 ⟩ₙ · (y + z + ⟨ 2 ⟩ₙ · x))
  exNorm3 = normalize! R

  exNorm4 : (x - x) + y · 0r + (scalar 4) ≡ ⟨ 4 ⟩ₙ
  exNorm4 = normalize! R

  module SolveForExamples
    (eq1 : y · y + v + z · x + w · x + (- w) + v + scalar 2 · v ≡ - (y · y) - x - x - scalar 2)
    (eq2 : y + x · x · x ≡ scalar 2)
    (eq3 : y · scalar 2 · y · v + v + z · x + w · x + (- w) + v + scalar 2 · v
         ≡ - (y · w · y · scalar 4) · v - x - x - scalar 2)
    where

    solveForEx : ⟨ 2 ⟩ₙ · y ^ 2 ≡
                 - ⟨ 2 ⟩ₙ + w - ⟨ 4 ⟩ₙ · v - ⟨ 2 ⟩ₙ · x - z · x - w · x
    solveForEx = solveFor! R y eq1

    solveForEx2 : y ≡ ⟨ 2 ⟩ₙ - x ^ 3
    solveForEx2 = solveFor! R y eq2

    solveForEx3 : ⟨ 2 ⟩ₙ · v · (⟨ 1 ⟩ₙ + ⟨ 2 ⟩ₙ · w) · y ^ 2 ≡
                  - ⟨ 2 ⟩ₙ + w - ⟨ 4 ⟩ₙ · v - ⟨ 2 ⟩ₙ · x - z · x - w · x
    solveForEx3 = solveFor! R y eq3
















