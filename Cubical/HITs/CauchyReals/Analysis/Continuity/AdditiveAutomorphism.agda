module Cubical.HITs.CauchyReals.Analysis.Continuity.AdditiveAutomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Infrastructure using
  ( +Groupℝ
  ; ℝ₋₊
  ; Aut[_]ᵣ
  ; module +GrAutomorphism
  )

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

scalarAdditiveAutomorphism : ℝ₋₊ → Aut[ snd +Groupℝ ]ᵣ .fst
scalarAdditiveAutomorphism (α , 0＃α) =
  (i , makeIsGroupHom λ x y → ·DistR+ x y α) ,
  IsContinuous·ᵣR α , IsContinuous·ᵣR (invℝ α 0＃α)
  where
  i : Iso ℝ ℝ
  i .Iso.fun = _·ᵣ α
  i .Iso.inv = _·ᵣ invℝ α 0＃α
  i .Iso.sec x = [x/y]·yᵣ x α 0＃α
  i .Iso.ret x = [x·y]/yᵣ x α 0＃α

automorphismScalar : Aut[ snd +Groupℝ ]ᵣ .fst → ℝ
automorphismScalar a = Iso.fun (fst (fst a)) 1

automorphismActsByScalar :
  (a : Aut[ snd +Groupℝ ]ᵣ .fst) →
  ∀ x → x ·ᵣ automorphismScalar a ≡ Iso.fun (fst (fst a)) x
automorphismActsByScalar a =
  ≡Continuous _ _
    (IsContinuous·ᵣR (automorphismScalar a))
    (fst (snd a))
    (sym ∘ +GrAutomorphism.fun-rat (fst a))
