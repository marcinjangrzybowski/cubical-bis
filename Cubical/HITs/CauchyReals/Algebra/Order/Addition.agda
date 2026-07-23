module Cubical.HITs.CauchyReals.Algebra.Order.Addition where

open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base public hiding
  (a≤b-c⇒c≤b-a-bootstrap)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict public using
  (<ᵣ-+o; <ᵣ-o+)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Bootstrap public
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Properties public using
  (a≤b-c⇒c≤b-a; a<b-c⇒c<b-a; a<b-c⇒a+c<b; a+c<b⇒a<b-c
  ; a-b<c⇒a-c<b; x<y→0<y-x; a-b<c⇒a<c+b)
