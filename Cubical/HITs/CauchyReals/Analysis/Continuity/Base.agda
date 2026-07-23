module Cubical.HITs.CauchyReals.Analysis.Continuity.Base where

open import Cubical.HITs.CauchyReals.Foundation.Order.Base public using
  (rexprTest)
open import Cubical.HITs.CauchyReals.Foundation.Order.RationalBounds public using
  (abs'q≤Δ₁)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core public
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Predicate public
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp public using
  (IsContinuousClamp; IsContinuousClamp₂; IsContinuousClamp₂∘
  ; IsContinuousClamp₂∘'; ≤clampᵣ; clamp≤ᵣ; ∈ℚintervalℙ→clampᵣ≡)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order public using
  (≤Cont₂; ≤Cont; ≤Cont₂Pos; ≤ContPos'; <→≤ContPos'; ≤ContPos)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base public
  using (IsUContinuousℙ; IsUContinuousℚℙ)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Approximation public
  using (ℚApproxℙ; ℚApprox; ℚApproxℙ'Num; ℚApproxℙ'
  ; Iso-ℚApproxℙ'-ℚApproxℙ; ℚApproxℙ'≃ℚApproxℙ; ℚApproxℙ''
  ; ℚApproxℙ'→ℚApproxℙ''; ℚApproxℙ∘)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Limit public
  using (≤lim; limConstRat; lim≤)
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Extension public
  using (fromLipschitz')
open import Cubical.HITs.CauchyReals.Analysis.Order.Functions public using
  (isIncrasingℙ; isNondecrasingℙ)



open import Cubical.HITs.CauchyReals.Foundation.Rationals public using
  (m·n/m; abs'q≤Δ₁'; ℚabs-abs≤abs-)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base public hiding
  (a≤b-c⇒c≤b-a-bootstrap)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict public hiding
  (a<b-c⇒c<b-a-bootstrap; a<b-c⇒a+c<b-bootstrap
  ; a+c<b⇒a<b-c-bootstrap; a-b<c⇒a-c<b-bootstrap
  ; x<y→0<y-x-bootstrap; a-b<c⇒a<c+b-bootstrap)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Properties public using
  (a≤b-c⇒c≤b-a; a<b-c⇒c<b-a; a<b-c⇒a+c<b; a+c<b⇒a<b-c
  ; a-b<c⇒a-c<b; x<y→0<y-x; a-b<c⇒a<c+b)
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice public
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue public using
  (absᵣ-triangle; absᵣ-triangle''; abs-max
  ; ℚabs-min-max; absᵣ-min-max
  ; absᵣNonNeg; absᵣ-monotoneOnNonNeg; absᵣPos; absᵣ≡0→≡0)
