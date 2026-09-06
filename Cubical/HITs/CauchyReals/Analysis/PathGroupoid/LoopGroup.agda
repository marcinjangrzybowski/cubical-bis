module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.LoopGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group.Base
open import Cubical.Relation.Premetric.Base
open import Cubical.HITs.SetQuotients using (squash/)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Quotient

-- The automorphism group of a point in the path groupoid.
module Loops {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') (x : fst X) where
  open FundamentalGroupoid X public

  Loop : Type (ℓ-max ℓ ℓ')
  Loop = UCPath x x

  LoopClass : Type (ℓ-max ℓ ℓ')
  LoopClass = PathClass x x

  loopGroup : Group (ℓ-max ℓ ℓ')
  loopGroup = makeGroup (identityClass x) composeClass inverseClass squash/
    (λ p q r → sym (composeClass-assoc p q r))
    composeClass-unit-right composeClass-unit-left
    composeClass-inverse-right composeClass-inverse-left
