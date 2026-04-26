module Cubical.Tactics.CommRingSolver.OrderedConfig where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Tactics.CommRingSolver.Config public
open import Agda.Builtin.Reflection hiding (Type)
open import Cubical.Data.Maybe
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Order.Poset.Base

record OrderedCommRingSolverConfig : Typeω where
 
 field
  commRingSolverConfig : CommRingSolverConfig
 open CommRingSolverConfig commRingSolverConfig public
 field
  {oℓ oℓ`} : Level
  _<_ _≤_ : _
  iocr : IsOrderedCommRing {ℓ' = oℓ} 0r 1r _+_ _·_ -_ _<_ _≤_
  _<?_ : ∀ x y → Dec (x < y) 
  _≤?_ : ∀ x y → Dec (x ≤ y)
  _<`_ _≤`_ : _
  ≡<>? : ∀ x y → (x ≡ y) ⊎ ((x < y) ⊎ (y < x)) 
  iocr` : IsOrderedCommRing {ℓ' = oℓ`} 0r` 1r` _+`_ _·`_ -`_ _<`_ _≤`_
  pres<         : ∀ x y → x < y → scalar` x <` scalar` y
  pres≤         : ∀ x y → x ≤ y → scalar` x ≤` scalar` y
  reflect<      : ∀ x y → scalar` x <` scalar` y → x < y
  mbInverses    : Maybe
    ((∀ x y k → 0r < k → (scalar` k ·` x) <` y → Σ[ 1/k ∈ _ ] (x <` (scalar` 1/k ·` y)))
     × (∀ x y k → 0r < k → (scalar` k ·` x) ≤` y → Σ[ 1/k ∈ _ ] (x ≤` (scalar` 1/k ·` y))))
  mbPureMatchZero : Term → TC Bool  
  mkMatchInequalityGoalTC :
    Term → TC (Maybe (Bool × (Term × Term)))
    -- it accept type, and maybe produce sides of inequality,
    -- false will be returned for non strict, and true for strict inequality

 module OCR where
  open IsOrderedCommRing iocr public
  open OrderedCommRingTheory (_ , orderedcommringstr 0r 1r _+_ _·_ -_ _<_ _≤_ iocr) public

 open OCR using (_#_) public
 module OCR` where
  OR = (_ , orderedcommringstr 0r` 1r` _+`_ _·`_ -`_ _<`_ _≤`_ iocr`)
  open IsOrderedCommRing iocr` public
  open OrderedCommRingTheory OR public
  open PosetStr (snd (OrderedCommRing→Poset OR ))
 open OCR` using () renaming (_#_ to _#`_) public
