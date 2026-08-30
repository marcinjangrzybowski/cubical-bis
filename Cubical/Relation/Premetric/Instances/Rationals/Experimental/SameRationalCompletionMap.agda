module Cubical.Relation.Premetric.Instances.Rationals.Experimental.SameRationalCompletionMap where

-- Unfinished experiment: unlike the proved signed-square equivalence, this
-- map is required to preserve the underlying rational coordinate.  It is
-- kept out of the established SignedSquare modules until its eliminator
-- obstruction is resolved.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.Rationals.SignedSquare.Completion

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
