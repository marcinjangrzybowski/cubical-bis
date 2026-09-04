module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Identities where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Laws


private
  fourFactorInterchange : ∀ a b c d →
    (a · b) · (c · d) ≡ (a · c) · (b · d)
  fourFactorInterchange a b c d =
      mulAssoc (a · b) c d
    ∙ cong (_· d) (sym (mulAssoc a b c))
    ∙ cong (λ middle → (a · middle) · d) (mulComm b c)
    ∙ cong (_· d) (mulAssoc a c b)
    ∙ sym (mulAssoc (a · c) b d)


opaque
  tanℝ≡sinℝ-mul-secℝ : ∀ point →
    tanℝ point ≡ sinℝ (fst point) · secℝ point
  tanℝ≡sinℝ-mul-secℝ point =
    mul-cancel-right-apart
      (tanℝ point)
      (sinℝ (fst point) · secℝ point)
      (cosℝ (fst point))
      (snd point)
      ( tanℝ-mul-cosℝ point
      ∙ sym
          ( sym
              (mulAssoc
                (sinℝ (fst point))
                (secℝ point)
                (cosℝ (fst point)))
          ∙ cong
              (sinℝ (fst point) ·_)
              (secℝ-mul-cosℝ point)
          ∙ mulIdR (sinℝ (fst point))
          )
      )


  onePlusTanℝSquared≡secℝSquared : ∀ point →
    1ℝ + (tanℝ point · tanℝ point)
      ≡ secℝ point · secℝ point
  onePlusTanℝSquared≡secℝSquared point =
    mul-cancel-right-apart
      (1ℝ + (tanℝ point · tanℝ point))
      (secℝ point · secℝ point)
      cosine-square
      cosine-square-apart
      ( mulDistL
          1ℝ (tanℝ point · tanℝ point) cosine-square
      ∙ cong₂ _+_
          (mulIdL cosine-square)
          tan-square-times-cosine-square
      ∙ addComm cosine-square sine-square
      ∙ sin²+cos²≡1 (fst point)
      ∙ sym sec-square-times-cosine-square
      )
    where
    sine-square : ℝ
    sine-square = sinℝ (fst point) · sinℝ (fst point)

    cosine-square : ℝ
    cosine-square = cosℝ (fst point) · cosℝ (fst point)

    cosine-square-apart : 0ℝ #ℝ cosine-square
    cosine-square-apart =
      apartMul
        (cosℝ (fst point)) (cosℝ (fst point))
        (snd point) (snd point)

    tan-square-times-cosine-square :
      (tanℝ point · tanℝ point) · cosine-square
        ≡ sine-square
    tan-square-times-cosine-square =
      fourFactorInterchange
        (tanℝ point) (tanℝ point)
        (cosℝ (fst point)) (cosℝ (fst point))
      ∙ cong₂ _·_
          (tanℝ-mul-cosℝ point)
          (tanℝ-mul-cosℝ point)

    sec-square-times-cosine-square :
      (secℝ point · secℝ point) · cosine-square ≡ 1ℝ
    sec-square-times-cosine-square =
      fourFactorInterchange
        (secℝ point) (secℝ point)
        (cosℝ (fst point)) (cosℝ (fst point))
      ∙ cong₂ _·_
          (secℝ-mul-cosℝ point)
          (secℝ-mul-cosℝ point)
      ∙ mulIdL 1ℝ


  secℝSquared≡onePlusTanℝSquared : ∀ point →
    secℝ point · secℝ point
      ≡ 1ℝ + (tanℝ point · tanℝ point)
  secℝSquared≡onePlusTanℝSquared point =
    sym (onePlusTanℝSquared≡secℝSquared point)


  secℝSquaredSubTanℝSquared≡one : ∀ point →
    (secℝ point · secℝ point) -
      (tanℝ point · tanℝ point)
      ≡ 1ℝ
  secℝSquaredSubTanℝSquared≡one point =
    cong
      (_- (tanℝ point · tanℝ point))
      (secℝSquared≡onePlusTanℝSquared point)
    ∙ sym
        (addAssoc
          1ℝ
          (tanℝ point · tanℝ point)
          (- (tanℝ point · tanℝ point)))
    ∙ cong
        (1ℝ +_)
        (addInvR (tanℝ point · tanℝ point))
    ∙ addIdR 1ℝ
