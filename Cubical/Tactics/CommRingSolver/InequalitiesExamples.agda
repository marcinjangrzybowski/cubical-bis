{-# OPTIONS --quote-metas #-}

module Cubical.Tactics.CommRingSolver.InequalitiesExamples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Int.Base hiding (_+_ ; _·_ ; _-_; -_)
open import Cubical.Data.Int.Fast.Order
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (true ; false)
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Agda.Builtin.String

import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast
open import Cubical.Algebra.CommAlgebra

open import Cubical.Data.Int.Fast

open import Cubical.Relation.Binary

open import Cubical.Tactics.CommRingSolver.OrderedReflection

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚ
module ℚ₊ = PositiveRationals 









bb : ℚ.ℚ → ℚ.ℚ
bb a = a ℚ.+ a

module RatExamples where

 open OrderedCommRingReasoning ℚOrderedCommRing
 open OrderedCommRingTheory ℚOrderedCommRing

 open PositiveRationals
 open PositiveHalvesℚ


 module T0
          (a₊ : ℚ₊.ℚ₊)
          (a₊' : ℚ₊.ℚ₊ × ℚ₊.ℚ₊ )
          
          (a b c d e : ℚ.ℚ)
          (b<a : 2 ℚ.· b ℚ.< 2 ℚ.· a)   
          (d≤e : d ℚ.≤ e) 
          (0≤e : ℚ.- e ℚ.≤ 0)
          (0≤d : 0 ℚ.≤ d)
          where
 
  _ : 1 ℚ.· (2 ℚ.· b ℚ.+ ℚ.[ (1 , 1) ] ℚ.· c) ℚ.+ 3 ℚ.· d ℚ.< (2 ℚ.· a ℚ.+ c) ℚ.+ (fst a₊) ℚ.+ 5 ℚ.· e
  _ = <≤ℚ![ b<a ][ d≤e ]


  _ : 1 ℚ.· (2 ℚ.· b ℚ.+ ℚ.[ (1 , 1) ] ℚ.· c) ℚ.+ 3 ℚ.· d ℚ.< (2 ℚ.· a ℚ.+ c) ℚ.+ (fst (fst a₊')) ℚ.+ 5 ℚ.· e
  _ = <≤ℚ![ b<a ][ d≤e ]

  _ : 2 ℚ.· b ℚ.+ d ℚ.< 2 ℚ.· a ℚ.+ e ℚ.+ fst a₊
  _ = <≤ℚ![ b<a ][ d≤e ]

  _ : d ℚ.+ 2 ℚ.· b ℚ.≤ e ℚ.+ 2 ℚ.· a
  _ = <≤ℚ![ b<a ][ d≤e ]

  _ : 0 ℚ.≤ d ℚ.+ e
  _ = <≤ℚ![ 0≤d ][ 0≤e ]


 module  TestFromClosensess (ε θ δ : ℚ₊.ℚ₊) (δ<θ : fst δ ℚ.< fst θ) where
 

  η = [ θ -₊ δ ]⟨ δ<θ ⟩
  
  test1 : 0 ℚ.< (ε +₊ θ) -₊ (η /4₊ +₊ ε)

  test1 = <≤ℚ!


 module SimpleAssumptionExamples (a b c d : ℚ.ℚ)
                                (a≤b : a ℚ.≤ b)
                                (b<c : b ℚ.< c)
                                (0≤d : 0 ℚ.≤ d) where

  _ : a ℚ.+ a ℚ.≤ b ℚ.+ b
  _ = <≤ℚ![ a≤b ]

  _ : a ℚ.+ d ℚ.≤ b ℚ.+ d
  _ = <≤ℚ![ a≤b ]

  _ : a ℚ.+ b ℚ.< c ℚ.+ b
  _ = <≤ℚ![ a≤b ][ b<c ]

  explicit≤ : a ℚ.+ d ℚ.≤ b ℚ.+ d
  explicit≤ = <≤ℚ![ a≤b ]

  explicit< : a ℚ.+ d ℚ.< c ℚ.+ d
  explicit< = <≤ℚ![ a≤b ][ b<c ]

  strictAndNonStrict : a ℚ.+ b ℚ.+ d ℚ.< c ℚ.+ b ℚ.+ d
  strictAndNonStrict = <≤ℚ![ a≤b ][ b<c ]


 module PositiveSlackExamples (ε : ℚ₊.ℚ₊)
                              (a b d : ℚ.ℚ)
                              (a≤b : a ℚ.≤ b)
                              (0≤d : 0 ℚ.≤ d) where

  _ : a ℚ.< b ℚ.+ fst ε
  _ = <≤ℚ![ a≤b ]

  _ : a ℚ.+ d ℚ.< b ℚ.+ d ℚ.+ fst ε
  _ = <≤ℚ![ a≤b ]
  

























































































