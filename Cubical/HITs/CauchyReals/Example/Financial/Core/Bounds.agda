{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Core.Bounds where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public

-- Closed bounds describe an entire family of constructive real inputs.
-- Membership is supplied evidence, never a decision procedure on reals.
record Bound : Type₀ where
  constructor bound
  field
    lo hi : ℝ
    lo-nonnegative : 0 ≤ᵣ lo
    lo≤hi : lo ≤ᵣ hi
open Bound public

hi-nonnegative : (B : Bound) → 0 ≤ᵣ hi B
hi-nonnegative B = isTrans≤ᵣ 0 (lo B) (hi B) (lo-nonnegative B) (lo≤hi B)

record InInterval (B : Bound) (x : ℝ) : Type₀ where
  constructor within
  field
    aboveLo : lo B ≤ᵣ x
    belowHi : x ≤ᵣ hi B
open InInterval public

interval-nonnegative : ∀ B x → InInterval B x → 0 ≤ᵣ x
interval-nonnegative B x member = isTrans≤ᵣ 0 (lo B) x (lo-nonnegative B) (aboveLo member)

product-lower : ∀ A B x y → InInterval A x → InInterval B y → lo A ·ᵣ lo B ≤ᵣ x ·ᵣ y
product-lower A B x y memberX memberY = ≤ᵣ₊Monotone·ᵣ (lo A) x (lo B) y
  (interval-nonnegative A x memberX) (lo-nonnegative B) (aboveLo memberX) (aboveLo memberY)

product-upper : ∀ A B x y → InInterval A x → InInterval B y → x ·ᵣ y ≤ᵣ hi A ·ᵣ hi B
product-upper A B x y memberX memberY = ≤ᵣ₊Monotone·ᵣ x (hi A) y (hi B)
  (hi-nonnegative A) (interval-nonnegative B y memberY) (belowHi memberX) (belowHi memberY)

