module Cubical.HITs.CauchyRealsP.Foundation.Closeness where

open import Cubical.HITs.CauchyRealsP.Foundation.Base public
open import Cubical.HITs.CauchyRealsP.Foundation.Rationals

-- These are generic completion theorems specialised to rational closeness.
-- The aliases name only genuinely real-specific boundary objects; the rest of
-- the generic theorem vocabulary remains available unchanged.
open import
  Cubical.Relation.Premetric.Completion.Properties.Closeness ℚPremetricSpace
  public
  renaming
    ( isRefl∼         to refl∼
    ; isSym∼          to sym∼
    ; isSetℭ          to isSetℝ
    ; isTriangular∼   to triangle∼
    ; isRounded∼      to rounded∼
    ; isInjectiveι    to isInjectiveRat
    ; ι-ι→≈           to rat-rat-toAbs
    ; ℭPremetricSpace to ℝPremetricSpace
    ; isCompleteℭ     to isCompleteℝ
    )
