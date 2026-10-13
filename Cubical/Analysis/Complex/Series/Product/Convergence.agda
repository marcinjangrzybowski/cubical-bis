module Cubical.Analysis.Complex.Series.Product.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.Product.Native as Real
import Cubical.Analysis.Real.Series.Product.Finite as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.Product.Finite

-- Native Mertens: only the first factor needs absolute convergence. The
-- second supplies a native Cauchy witness. Supplied sums are kept explicit,
-- so the result applies to any proof-independent representatives of them.
opaque
  mertensCauchyProductℂHasSum : ∀ a b x y →
    IsComplexAbsolutelyCauchySeries a → IsComplexCauchySeries b →
    HasComplexSum a x → HasComplexSum b y → HasComplexSum (cauchyProductℂ a b) (x ·ℂ y)
  mertensCauchyProductℂHasSum a b x y absolute cauchy first second =
    subst (λ terms → Real.HasSum terms (re (x ·ℂ y)))
      (sym (funExt (cauchyProductℂ-re a b)))
      (snd (Real.subSummable
        (Real.cauchyProduct (re ∘ a) (re ∘ b)) (Real.cauchyProduct (im ∘ a) (im ∘ b))
        (re x · re y , Real.nativeMertensCauchyProductHasSum (re ∘ a) (re ∘ b) (re x) (re y)
          (fst coordinates) (fst cauchy) (fst first) (fst second))
        (im x · im y , Real.nativeMertensCauchyProductHasSum (im ∘ a) (im ∘ b) (im x) (im y)
          (snd coordinates) (snd cauchy) (snd first) (snd second)))) ,
    subst (λ terms → Real.HasSum terms (im (x ·ℂ y)))
      (sym (funExt (cauchyProductℂ-im a b)))
      (snd (Real.addSummable
        (Real.cauchyProduct (re ∘ a) (im ∘ b)) (Real.cauchyProduct (im ∘ a) (re ∘ b))
        (re x · im y , Real.nativeMertensCauchyProductHasSum (re ∘ a) (im ∘ b) (re x) (im y)
          (fst coordinates) (snd cauchy) (fst first) (snd second))
        (im x · re y , Real.nativeMertensCauchyProductHasSum (im ∘ a) (re ∘ b) (im x) (re y)
          (snd coordinates) (fst cauchy) (snd first) (fst second))))
    where
    coordinates : Real.IsAbsolutelyCauchySeries (re ∘ a) × Real.IsAbsolutelyCauchySeries (im ∘ a)
    coordinates = absoluteComplexCauchyCoordinates a absolute

mertensCauchyProductℂSummable : ∀ a b →
  IsComplexAbsolutelyCauchySeries a → IsComplexCauchySeries b → ComplexSummable (cauchyProductℂ a b)
mertensCauchyProductℂSummable a b absolute cauchy =
  seriesSumℂ a first ·ℂ seriesSumℂ b second ,
  mertensCauchyProductℂHasSum a b (seriesSumℂ a first) (seriesSumℂ b second)
    absolute cauchy (snd first) (snd second)
  where
  first : ComplexSummable a
  first = absoluteComplexCauchySeriesIsSummable a absolute
  second : ComplexSummable b
  second = complexCauchySeriesIsSummable b cauchy

seriesSumℂ-cauchyProduct : ∀ a b →
  IsComplexAbsolutelyCauchySeries a → IsComplexCauchySeries b →
  (first : ComplexSummable a) (second : ComplexSummable b) (product : ComplexSummable (cauchyProductℂ a b)) →
  seriesSumℂ (cauchyProductℂ a b) product ≡ seriesSumℂ a first ·ℂ seriesSumℂ b second
seriesSumℂ-cauchyProduct a b absolute cauchy first second product =
  complexSumUnique (cauchyProductℂ a b) (fst product) (fst first ·ℂ fst second) (snd product)
    (mertensCauchyProductℂHasSum a b (fst first) (fst second) absolute cauchy (snd first) (snd second))

-- The symmetric form avoids requiring absolute convergence on both sides.
mertensCauchyProductℂHasSumRight : ∀ a b x y →
  IsComplexCauchySeries a → IsComplexAbsolutelyCauchySeries b →
  HasComplexSum a x → HasComplexSum b y → HasComplexSum (cauchyProductℂ a b) (x ·ℂ y)
mertensCauchyProductℂHasSumRight a b x y cauchy absolute first second =
  subst (HasComplexSum (cauchyProductℂ a b)) (·ℂComm y x)
    (complexHasSumPointwise (cauchyProductℂ b a) (cauchyProductℂ a b) (cauchyProductℂ-comm b a) (y ·ℂ x)
      (mertensCauchyProductℂHasSum b a y x absolute cauchy second first))
