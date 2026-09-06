module Cubical.Analysis.Real.Functions.Logarithm.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (ℝAbGroup; _-_)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.MultiplicativeGroup
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Exponential.Inverse
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition


-- Multiplication on the positive reals is the ordinary real multiplication;
-- the group was constructed independently of the exponential equivalence.
opaque
  expPositive-add : ∀ x y →
    expPositive (x + y) ≡ expPositive x ·>0 expPositive y
  expPositive-add x y =
    Σ≡Prop isPropIsPositive
      (expPositive-value (x + y)
      ∙ exponentialEntireValue-add x y
      ∙ cong₂ _·_ (sym (expPositive-value x)) (sym (expPositive-value y)))

  expPositive-isGroupHom :
    IsGroupHom (AbGroup→Group ℝAbGroup .snd) expPositive (ℝ>0Group .snd)
  expPositive-isGroupHom = makeIsGroupHom expPositive-add

  logℝ-isGroupHom :
    IsGroupHom (ℝ>0Group .snd) logℝ (AbGroup→Group ℝAbGroup .snd)
  logℝ-isGroupHom = makeIsGroupHom logℝ-product


expPositiveGroupHom : GroupHom (AbGroup→Group ℝAbGroup) ℝ>0Group
expPositiveGroupHom = expPositive , expPositive-isGroupHom

logℝGroupHom : GroupHom ℝ>0Group (AbGroup→Group ℝAbGroup)
logℝGroupHom = logℝ , logℝ-isGroupHom


-- Keep both maps explicit: the inverse of this group isomorphism is the
-- established global logarithm, not an opaque inverse extracted from a proof.
expPositiveGroupIso : GroupIso (AbGroup→Group ℝAbGroup) ℝ>0Group
expPositiveGroupIso =
  iso expPositive logℝ expPositive-logℝ logℝ-expPositive
  , expPositive-isGroupHom

logℝGroupIso : GroupIso ℝ>0Group (AbGroup→Group ℝAbGroup)
logℝGroupIso =
  iso logℝ expPositive logℝ-expPositive expPositive-logℝ
  , logℝ-isGroupHom


expPositiveGroupEquiv : GroupEquiv (AbGroup→Group ℝAbGroup) ℝ>0Group
expPositiveGroupEquiv = expPositiveEquiv , expPositive-isGroupHom

logℝGroupEquiv : GroupEquiv ℝ>0Group (AbGroup→Group ℝAbGroup)
logℝGroupEquiv = logPositiveEquiv , logℝ-isGroupHom

expPositiveAbGroupEquiv : AbGroupEquiv ℝAbGroup ℝ>0AbGroup
expPositiveAbGroupEquiv = expPositiveGroupEquiv

logℝAbGroupEquiv : AbGroupEquiv ℝ>0AbGroup ℝAbGroup
logℝAbGroupEquiv = logℝGroupEquiv


opaque
  expPositive-zero : expPositive 0ℝ ≡ 1>0
  expPositive-zero = IsGroupHom.pres1 expPositive-isGroupHom

  expPositive-negative : ∀ x →
    expPositive (- x) ≡ positiveInverse (expPositive x)
  expPositive-negative = IsGroupHom.presinv expPositive-isGroupHom

  logℝ-one : logℝ 1>0 ≡ 0ℝ
  logℝ-one = IsGroupHom.pres1 logℝ-isGroupHom

  logℝ-positiveInverse : ∀ value →
    logℝ (positiveInverse value) ≡ - logℝ value
  logℝ-positiveInverse = IsGroupHom.presinv logℝ-isGroupHom

  expPositive-sub : ∀ x y →
    expPositive (x - y) ≡ expPositive x />0 expPositive y
  expPositive-sub x y =
    expPositive-add x (- y)
    ∙ cong (expPositive x ·>0_) (expPositive-negative y)

  logℝ-quotient : ∀ x y →
    logℝ (x />0 y) ≡ logℝ x - logℝ y
  logℝ-quotient x y =
    logℝ-product x (positiveInverse y)
    ∙ cong (logℝ x +_) (logℝ-positiveInverse y)
