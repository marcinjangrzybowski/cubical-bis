-- oboslete module to be deleted during celanup

module Cubical.HITs.CauchyReals.BisectionAprox where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.RationalsImports

open import Cubical.Data.Rationals.Bisection as ℚB
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (_／₊_; _⁻¹₊)

open import Cubical.HITs.CauchyReals.Aproximations

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
