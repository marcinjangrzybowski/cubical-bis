module Cubical.HITs.CauchyReals.Circle.Homotopy.Integers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos; negsuc)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; distrℤ·; homPresℤ·)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom; compGroupHom)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Examples using (winding-identity)
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (idᵘᶜ)

private
  MapGroup = AbGroup→Group CircleMapAbGroup
  IntegerGroup = AbGroup→Group IntegerAbGroup

-- Positive integers give repeated pointwise sums of the identity map;
-- negative integers give the corresponding inverses.
integerMap : ℤ → CircleMap
integerMap k = k ℤ[ MapGroup ]· idᵘᶜ

integerMapHom : AbGroupHom IntegerAbGroup CircleMapAbGroup
integerMapHom = integerMap , makeIsGroupHom (λ m n →
  cong integerMap (sym (ℤ.+≡+f m n)) ∙ distrℤ· MapGroup idᵘᶜ m n)

private
  integer-power-one : ∀ k → k ℤ[ IntegerGroup ]· 1 ≡ k
  integer-power-one (pos zero) = refl
  integer-power-one (pos (suc n)) = cong (ℤ._+_ 1) (integer-power-one (pos n))
  integer-power-one (negsuc zero) = refl
  integer-power-one (negsuc (suc n)) = cong (ℤ._+_ -1) (integer-power-one (negsuc n))

winding-integerMap : ∀ k → windingNumber (integerMap k) ≡ k
winding-integerMap k = homPresℤ· windingHom idᵘᶜ k
  ∙ cong (k ℤ[ IntegerGroup ]·_) winding-identity
  ∙ integer-power-one k

integerClass : ℤ → CircleHomotopyClasses
integerClass k = class (integerMap k)

integerClassHom : AbGroupHom IntegerAbGroup CircleHomotopyAbGroup
integerClassHom = compGroupHom integerMapHom classHom

winding-integerClass : ∀ k → classWinding (integerClass k) ≡ k
winding-integerClass = winding-integerMap

integerClass-injective : ∀ m n → integerClass m ≡ integerClass n → m ≡ n
integerClass-injective m n p = sym (winding-integerClass m)
  ∙ cong classWinding p ∙ winding-integerClass n
