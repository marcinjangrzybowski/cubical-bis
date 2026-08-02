module Cubical.Relation.Premetric.Instances.Rationals.MySignedSquareIdentity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.Rationals.SignedSquareCompletion

-- import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base as RealMultiplication
-- import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue as RealAbsoluteValue

-- -- Unlike completionSignedRootⁿ, this map preserves the rational coordinate.
-- -- It is not packaged as a non-expanding map: real signed squaring is not
-- -- globally non-expanding for the ordinary metric.
-- signedSquareOnOrdinaryCompletion : OrdinaryCompletion.ℭ → OrdinaryCompletion.ℭ
-- signedSquareOnOrdinaryCompletion x =
--   RealMultiplication._·_ x (RealAbsoluteValue.absℝ x)

-- signedSquareOnOrdinaryCompletion-ι : ∀ q →
--   signedSquareOnOrdinaryCompletion (OrdinaryCompletion.ι q)
--     ≡ OrdinaryCompletion.ι (signedSquareℚ q)
-- signedSquareOnOrdinaryCompletion-ι q =
--   cong (RealMultiplication._·_ (OrdinaryCompletion.ι q))
--     (RealAbsoluteValue.abs-rat q)
--   ∙ RealMultiplication.mul-rat q _
--   ∙ cong OrdinaryCompletion.ι (sym (signedSquareℚ≡·abs q))

ordinaryToSignedSameRational : OrdinaryCompletion.ℭ → SignedCompletion.ℭ
ordinaryToSignedSameRational = {!Elimℭ!}


-- ordinaryToSignedSameRational-ι : ∀ q →
--   ordinaryToSignedSameRational (OrdinaryCompletion.ι q)
--     ≡ SignedCompletion.ι q
-- ordinaryToSignedSameRational-ι q =
--   cong (fst completionSignedRootⁿ)
--     (signedSquareOnOrdinaryCompletion-ι q)
--   ∙ completionSignedRoot-ι (signedSquareℚ q)
--   ∙ approximateSignedRoot-signedSquareℚ q
