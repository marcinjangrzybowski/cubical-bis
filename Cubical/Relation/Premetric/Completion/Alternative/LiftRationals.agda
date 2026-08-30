module Cubical.Relation.Premetric.Completion.Alternative.LiftRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Empty
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Nullary
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.Rationals.SignedSquare.Completion

open import Cubical.Relation.Premetric.Completion.Alternative ℚPremetricSpace
open import Cubical.Relation.Premetric.Completion.Alternative.Lift
  ℚPremetricSpace ℚPremetricSpace

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing
open PositiveRationals
open PositiveHalvesℚ

private
  module Pℚ = PremetricStr (snd ℚPremetricSpace)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- For nonlinear maps the useful constant often depends on a bound for the
-- particular Cauchy family, rather than being global.

record IsLipschitzOnBallWith
  (f : ℚ → ℚ) (B L : ℚ₊) : Type₀ where
  no-eta-equality
  field
    pres≈ : ∀ x y ε
      → abs x ≤ fst B
      → abs y ≤ fst B
      → x Pℚ.≈[ ε ] y
      → f x Pℚ.≈[ L ·₊ ε ] f y

open IsLipschitzOnBallWith

IsLocallyLipschitz : (ℚ → ℚ) → Type₀
IsLocallyLipschitz f = ∀ B →
  Σ[ L ∈ ℚ₊ ] IsLipschitzOnBallWith f B L


-- Signed squaring is Lipschitz on the ball of radius B with constant 2B.
-- It is the basic example where no single global constant is appropriate.

signedSquareℚ-locallyLipschitz : IsLocallyLipschitz signedSquareℚ
signedSquareℚ-locallyLipschitz B = B +₊ B , local
  where
  local : IsLipschitzOnBallWith signedSquareℚ B (B +₊ B)
  local .pres≈ x y ε absx≤B absy≤B x≈y =
    ℚ.isTrans≤<
      (abs (signedSquareℚ x - signedSquareℚ y))
      (fst (B +₊ B) ℚ.· abs (x - y))
      (fst (B +₊ B) ℚ.· fst ε)
      (signedSquareℚ-bounded B x y absx≤B absy≤B)
      (·MonoL< (abs (x - y)) (fst ε) (fst (B +₊ B))
        (snd (B +₊ B)) x≈y)


signedSquareℚ-notLipschitzWith : ∀ L →
  ¬ IsLipschitzWith (snd ℚPremetricSpace) signedSquareℚ
      (snd ℚPremetricSpace) L
signedSquareℚ-notLipschitzWith L f-lip =
  ℚ.isAsym< (fst (L +₊ L)) output-distance
    lower-bound upper-bound
  where
  two : ℚ₊
  two = 1 +₊ 1

  x₊ : ℚ₊
  x₊ = (L +₊ L) +₊ 1

  x y : ℚ
  x = fst x₊
  y = x ℚ.+ 1

  0<x : 0 ℚ.< x
  0<x = snd x₊

  x<y : x ℚ.< y
  x<y = <₊SumLeft x₊ 1

  0<y : 0 ℚ.< y
  0<y = ℚ.isTrans< 0 x y 0<x x<y

  twoL<y : fst (L +₊ L) ℚ.< y
  twoL<y = ℚ.isTrans< (fst (L +₊ L)) x y
    (<₊SumLeft (L +₊ L) 1) x<y

  y-x≡1 : y ℚ.- x ≡ 1
  y-x≡1 =
    cong (ℚ._- x) (ℚ.+Comm x 1) ∙ ℚRing.plusMinus 1 x

  input-distance≡1 : abs (x ℚ.- y) ≡ 1
  input-distance≡1 =
      <0→abs≡- (x ℚ.- y) (<→Δ<0 x y x<y)
    ∙ ℚ.-[x-y]≡y-x x y
    ∙ y-x≡1

  input-close : x Pℚ.≈[ two ] y
  input-close = subst (_< fst two) (sym input-distance≡1)
    (<₊SumLeft 1 1)

  square-x : signedSquareℚ x ≡ x ℚ.· x
  square-x = signedSquareℚ≡·abs x
    ∙ cong (x ℚ.·_) (0<→abs≡id x 0<x)

  square-y : signedSquareℚ y ≡ y ℚ.· y
  square-y = signedSquareℚ≡·abs y
    ∙ cong (y ℚ.·_) (0<→abs≡id y 0<y)

  x²<x·y : x ℚ.· x ℚ.< x ℚ.· y
  x²<x·y = ·MonoL< x y x 0<x x<y

  x²+y<y² : x ℚ.· x ℚ.+ y ℚ.< y ℚ.· y
  x²+y<y² = begin<
    x ℚ.· x ℚ.+ y
      <⟨ +MonoR< _ _ y x²<x·y ⟩
    x ℚ.· y ℚ.+ y
      ≡→≤⟨ cong (x ℚ.· y ℚ.+_) (sym (ℚ.·IdL y))
        ∙ sym (ℚ.·DistR+ x 1 y) ⟩
    y ℚ.· y ◾

  y<difference : y ℚ.< (y ℚ.· y) ℚ.- (x ℚ.· x)
  y<difference = ℚ.<-+o-cancel y
    ((y ℚ.· y) ℚ.- (x ℚ.· x)) (x ℚ.· x)
    (subst2 ℚ._<_
      (ℚ.+Comm (x ℚ.· x) y)
      (sym (ℚRing.minusPlus (y ℚ.· y) (x ℚ.· x)))
      x²+y<y²)

  output-distance≡difference :
    abs (signedSquareℚ x ℚ.- signedSquareℚ y)
      ≡ (y ℚ.· y) ℚ.- (x ℚ.· x)
  output-distance≡difference =
      <0→abs≡- _ (<→Δ<0 _ _ (signedSquareℚ-strictMono x<y))
    ∙ ℚ.-[x-y]≡y-x (signedSquareℚ x) (signedSquareℚ y)
    ∙ cong₂ ℚ._-_ square-y square-x

  output-distance : ℚ
  output-distance = abs (signedSquareℚ x ℚ.- signedSquareℚ y)

  lower-bound : fst (L +₊ L) ℚ.< output-distance
  lower-bound = subst (fst (L +₊ L) <_)
    (sym output-distance≡difference)
    (ℚ.isTrans< _ y _ twoL<y y<difference)

  radius≡twoL : fst (L ·₊ two) ≡ fst (L +₊ L)
  radius≡twoL = ℚ.·DistL+ (fst L) 1 1
    ∙ cong₂ ℚ._+_ (ℚ.·IdR (fst L)) (ℚ.·IdR (fst L))

  upper-bound : output-distance ℚ.< fst (L +₊ L)
  upper-bound = subst (output-distance <_) radius≡twoL
    (f-lip .IsLipschitzWith.pres≈ x y two input-close)


signedSquareℚ-notUniformlyContinuousWith : ∀ μ →
  ¬ IsUniformlyContinuousWith (snd ℚPremetricSpace) signedSquareℚ
      (snd ℚPremetricSpace) μ
signedSquareℚ-notUniformlyContinuousWith μ f-uc =
  ℚ.isAsym< 1 output-distance lower-bound upper-bound
  where
  d h : ℚ₊
  d = μ 1
  h = d /2₊

  x₊ : ℚ₊
  x₊ = h ⁻¹₊

  x y : ℚ
  x = fst x₊
  y = x ℚ.+ fst h

  0<x : 0 ℚ.< x
  0<x = snd x₊

  x<y : x ℚ.< y
  x<y = <₊SumLeft x₊ h

  0<y : 0 ℚ.< y
  0<y = ℚ.isTrans< 0 x y 0<x x<y

  y-x≡h : y ℚ.- x ≡ fst h
  y-x≡h =
    cong (ℚ._- x) (ℚ.+Comm x (fst h))
    ∙ ℚRing.plusMinus (fst h) x

  input-distance≡h : abs (x ℚ.- y) ≡ fst h
  input-distance≡h =
      <0→abs≡- (x ℚ.- y) (<→Δ<0 x y x<y)
    ∙ ℚ.-[x-y]≡y-x x y
    ∙ y-x≡h

  input-close : x Pℚ.≈[ d ] y
  input-close = subst (_< fst d) (sym input-distance≡h) (/2₊<id d)

  square-x : signedSquareℚ x ≡ x ℚ.· x
  square-x = signedSquareℚ≡·abs x
    ∙ cong (x ℚ.·_) (0<→abs≡id x 0<x)

  square-y : signedSquareℚ y ≡ y ℚ.· y
  square-y = signedSquareℚ≡·abs y
    ∙ cong (y ℚ.·_) (0<→abs≡id y 0<y)

  x²<x·y : x ℚ.· x ℚ.< x ℚ.· y
  x²<x·y = ·MonoL< x y x 0<x x<y

  x²+yh<y² : x ℚ.· x ℚ.+ y ℚ.· fst h ℚ.< y ℚ.· y
  x²+yh<y² = begin<
    x ℚ.· x ℚ.+ y ℚ.· fst h
      <⟨ +MonoR< _ _ (y ℚ.· fst h) x²<x·y ⟩
    x ℚ.· y ℚ.+ y ℚ.· fst h
      ≡→≤⟨ cong (x ℚ.· y ℚ.+_) (ℚ.·Comm y (fst h))
        ∙ sym (ℚ.·DistR+ x (fst h) y) ⟩
    y ℚ.· y ◾

  yh<difference : y ℚ.· fst h ℚ.<
      (y ℚ.· y) ℚ.- (x ℚ.· x)
  yh<difference = ℚ.<-+o-cancel (y ℚ.· fst h)
    ((y ℚ.· y) ℚ.- (x ℚ.· x)) (x ℚ.· x)
    (subst2 ℚ._<_
      (ℚ.+Comm (x ℚ.· x) (y ℚ.· fst h))
      (sym (ℚRing.minusPlus (y ℚ.· y) (x ℚ.· x)))
      x²+yh<y²)

  xh≡1 : x ℚ.· fst h ≡ 1
  xh≡1 = ℚ.·Comm x (fst h) ∙ ⁻¹inverse h

  1<yh : 1 ℚ.< y ℚ.· fst h
  1<yh = subst (_< y ℚ.· fst h) xh≡1
    (·MonoR< x y (fst h) (snd h) x<y)

  output-distance≡difference :
    abs (signedSquareℚ x ℚ.- signedSquareℚ y)
      ≡ (y ℚ.· y) ℚ.- (x ℚ.· x)
  output-distance≡difference =
      <0→abs≡- _ (<→Δ<0 _ _ (signedSquareℚ-strictMono x<y))
    ∙ ℚ.-[x-y]≡y-x (signedSquareℚ x) (signedSquareℚ y)
    ∙ cong₂ ℚ._-_ square-y square-x

  output-distance : ℚ
  output-distance = abs (signedSquareℚ x ℚ.- signedSquareℚ y)

  lower-bound : 1 ℚ.< output-distance
  lower-bound = subst (1 <_) (sym output-distance≡difference)
    (ℚ.isTrans< 1 (y ℚ.· fst h) _ 1<yh yh<difference)

  upper-bound : output-distance ℚ.< 1
  upper-bound = f-uc .IsUniformlyContinuousWith.pres≈ x y 1 input-close


signedSquareℚ-noΓModulus : ∀ g →
  ¬ IsΓModulusWith g signedSquareℚ
signedSquareℚ-noΓModulus g f-mod =
  signedSquareℚ-notUniformlyContinuousWith
    (λ ε → g .Γ.γ (ε /2₊) +₊ g .Γ.γ (ε /2₊))
    (ΓModulus→uniformlyContinuousWith g signedSquareℚ f-mod)


IsBoundedBy : ℚ₊ → (ℚ₊ → ℚ) → Type₀
IsBoundedBy B x = ∀ ε → abs (x ε) ≤ fst B


-- Large indices of a Cauchy family carry no useful approximation data.  By
-- clamping every index to 1 we obtain an equivalent tail whose values lie in
-- one explicit ball around x 1.

cauchyTail : (ℚ₊ → ℚ) → ℚ₊ → ℚ
cauchyTail x ε = x (min₊ ε 1)

cauchyTailCauchy : ∀ x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → PremetricTheory.isCauchy ℚPremetricSpace (cauchyTail x)
cauchyTailCauchy x xc ε δ =
  Pℚ.isMonotone≈≤ (x (min₊ ε 1)) (x (min₊ δ 1))
    (min₊ ε 1 +₊ min₊ δ 1) (ε +₊ δ)
    (+Mono≤ _ _ _ _ (min₊≤L ε 1) (min₊≤L δ 1))
    (xc (min₊ ε 1) (min₊ δ 1))

cauchyTailBound : (ℚ₊ → ℚ) → ℚ₊
cauchyTailBound x = (1 +₊ 1) +₊ maxWithPos 1 (abs (x 1))

cauchyTailBounded : ∀ x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → IsBoundedBy (cauchyTailBound x) (cauchyTail x)
cauchyTailBounded x xc ε = begin≤
  abs (cauchyTail x ε)
    ≡→≤⟨ sym (cong abs
      (cong (x (min₊ ε 1) ℚ.+_) ℚRing.0Selfinverse
        ∙ ℚ.+IdR (x (min₊ ε 1)))) ⟩
  abs (x (min₊ ε 1) - 0)
    ≤⟨ triangularInequality- (x (min₊ ε 1)) 0 (x 1) ⟩
  abs (x (min₊ ε 1) - x 1) + abs (x 1 - 0)
    ≡→≤⟨ cong (abs (x (min₊ ε 1) - x 1) ℚ.+_)
      (cong abs
        (cong (x 1 ℚ.+_) ℚRing.0Selfinverse ∙ ℚ.+IdR (x 1))) ⟩
  abs (x (min₊ ε 1) - x 1) + abs (x 1)
    <⟨ +MonoR< _ _ (abs (x 1)) (xc (min₊ ε 1) 1) ⟩
  fst (min₊ ε 1 +₊ 1) + abs (x 1)
    ≤⟨ +Mono≤ _ _ _ _
      (+MonoR≤ _ _ 1 (min₊≤R ε 1))
      (ℚ.≤max' 1 (abs (x 1))) ⟩
  fst (cauchyTailBound x) ◾


-- A family whose output distances are multiplied by L can be stored directly
-- in the alternative completion.  Its Γ remembers that scale; no reindexing
-- of the family is needed at construction time.

imageScaleΓ : ℚ₊ → Γ
imageScaleΓ L .Γ.γ ε = L ·₊ ε
imageScaleΓ L .Γ.mon-γ ε δ ε<δ =
  ·MonoL< (fst ε) (fst δ) (fst L) (snd L) ε<δ
imageScaleΓ L .Γ.τ ε = ε ₊／₊ L
imageScaleΓ L .Γ.γ∘τ≤id ε =
  subst (_≤ fst ε) (sym (·／ L ε)) (ℚ.isRefl≤ (fst ε))

boundedCauchyImageScaled : ∀ f B L
  → IsLipschitzOnBallWith f B L
  → (x : ℚ₊ → ℚ)
  → IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ∀ ε δ →
      f (x ε) Pℚ.≈[
        imageScaleΓ L .Γ.γ ε +₊ imageScaleΓ L .Γ.γ δ
      ] f (x δ)
boundedCauchyImageScaled f B L f-local x x-bounded xc ε δ =
  Pℚ.subst≈ (f (x ε)) (f (x δ))
    {ε = L ·₊ (ε +₊ δ)}
    {ε' = (L ·₊ ε) +₊ (L ·₊ δ)}
    (ℚ.·DistL+ (fst L) (fst ε) (fst δ))
    (f-local .pres≈ (x ε) (x δ) (ε +₊ δ)
      (x-bounded ε) (x-bounded δ) (xc ε δ))

boundedCauchyImageScaled̂ : ∀ f B L
  → IsLipschitzOnBallWith f B L
  → (x : ℚ₊ → ℚ)
  → IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ∀ ε δ →
      ι (f (x ε)) ∼̂[
        imageScaleΓ L .Γ.γ ε +₊ imageScaleΓ L .Γ.γ δ
      ] ι (f (x δ))
boundedCauchyImageScaled̂ f B L f-local x x-bounded xc ε δ =
  ι-ι (f (x ε)) (f (x δ)) _
    (boundedCauchyImageScaled f B L f-local x x-bounded xc ε δ)

boundedCauchyLimitDirect : ∀ f B L
  → IsLipschitzOnBallWith f B L
  → (x : ℚ₊ → ℚ)
  → IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
boundedCauchyLimitDirect f B L f-local x x-bounded xc =
  lim (ι ∘ f ∘ x) (imageScaleΓ L)
    (boundedCauchyImageScaled̂ f B L f-local x x-bounded xc)

boundedCauchyLimitDirect-regularForm : ∀ f B L f-local x x-bounded xc →
  ←̂ (boundedCauchyLimitDirect f B L f-local x x-bounded xc) ≡
    RegularBase.lim
      (λ ε → RegularBase.ι (f (x (ε ₊／₊ L))))
      (←̂Cauchy (ι ∘ f ∘ x) (imageScaleΓ L)
        (boundedCauchyImageScaled̂ f B L f-local x x-bounded xc))
boundedCauchyLimitDirect-regularForm f B L f-local x x-bounded xc = refl


-- A local Lipschitz estimate is enough on a bounded Cauchy family.  The
-- input family is rescaled by the locally chosen constant before applying f.

boundedCauchyImage : ∀ f B L
  → IsLipschitzOnBallWith f B L
  → (x : ℚ₊ → ℚ)
  → IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → PremetricTheory.isCauchy ℚPremetricSpace
      (f ∘ x ∘ (λ ε → ε ₊／₊ L))
boundedCauchyImage f B L f-local x x-bounded xc ε δ =
  Pℚ.subst≈ (f (x (ε ₊／₊ L))) (f (x (δ ₊／₊ L)))
    {ε = L ·₊ ((ε ₊／₊ L) +₊ (δ ₊／₊ L))}
    {ε' = ε +₊ δ}
    (ℚ.·DistL+ (fst L) (fst (ε ₊／₊ L)) (fst (δ ₊／₊ L))
      ∙ cong₂ ℚ._+_ (·／ L ε) (·／ L δ))
    (f-local .pres≈
      (x (ε ₊／₊ L)) (x (δ ₊／₊ L))
      ((ε ₊／₊ L) +₊ (δ ₊／₊ L))
      (x-bounded (ε ₊／₊ L)) (x-bounded (δ ₊／₊ L))
      (xc (ε ₊／₊ L) (δ ₊／₊ L)))


-- This is the part of a prospective lifting operation contributed by one
-- bounded rational Cauchy family.  Its output is an alternative-completion
-- limit, using the identity scale after the local rescaling above.

boundedCauchyLimit : ∀ f B L
  → IsLipschitzOnBallWith f B L
  → (x : ℚ₊ → ℚ)
  → IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
boundedCauchyLimit f B L f-local x x-bounded xc =
  lim image Γid image-cauchy
  where
  fx : ℚ₊ → ℚ
  fx = f ∘ x ∘ (λ ε → ε ₊／₊ L)

  image : ℚ₊ → ℭ̂
  image = ι ∘ fx

  fxc : PremetricTheory.isCauchy ℚPremetricSpace fx
  fxc = boundedCauchyImage f B L f-local x x-bounded xc

  image-cauchy : ∀ ε δ → image ε ∼̂[ ε +₊ δ ] image δ
  image-cauchy ε δ = ι-ι (fx ε) (fx δ) (ε +₊ δ) (fxc ε δ)

boundedCauchyLimitDirect≡rescaled : ∀ f B L f-local x x-bounded xc →
  boundedCauchyLimitDirect f B L f-local x x-bounded xc ≡
  boundedCauchyLimit f B L f-local x x-bounded xc
boundedCauchyLimitDirect≡rescaled f B L f-local x x-bounded xc =
    sym (→̂←̂ direct)
  ∙ cong →̂ regular-eq
  ∙ →̂←̂ rescaled
  where
  direct rescaled : ℭ̂
  direct = boundedCauchyLimitDirect f B L f-local x x-bounded xc
  rescaled = boundedCauchyLimit f B L f-local x x-bounded xc

  family : ℚ₊ → RegularBase.ℭ
  family ε = RegularBase.ι (f (x (ε ₊／₊ L)))

  direct-image : ℚ₊ → ℭ̂
  direct-image = ι ∘ f ∘ x

  direct-image-cauchy : ∀ ε δ →
    direct-image ε ∼̂[
      imageScaleΓ L .Γ.γ ε +₊ imageScaleΓ L .Γ.γ δ
    ] direct-image δ
  direct-image-cauchy =
    boundedCauchyImageScaled̂ f B L f-local x x-bounded xc

  direct-regular-cauchy : ∀ ε δ →
    family ε RegularPremetric.≈[ ε +₊ δ ] family δ
  direct-regular-cauchy =
    ←̂Cauchy direct-image (imageScaleΓ L) direct-image-cauchy

  rescaled-image : ℚ₊ → ℭ̂
  rescaled-image ε = ι (f (x (ε ₊／₊ L)))

  rescaled-image-cauchy : ∀ ε δ →
    rescaled-image ε ∼̂[ ε +₊ δ ] rescaled-image δ
  rescaled-image-cauchy ε δ = ι-ι _ _ _
    (boundedCauchyImage f B L f-local x x-bounded xc ε δ)

  rescaled-regular-cauchy : ∀ ε δ →
    family ε RegularPremetric.≈[ ε +₊ δ ] family δ
  rescaled-regular-cauchy =
    ←̂Cauchy rescaled-image Γid rescaled-image-cauchy

  direct-form : ←̂ direct ≡
    RegularBase.lim family direct-regular-cauchy
  direct-form =
    boundedCauchyLimitDirect-regularForm
      f B L f-local x x-bounded xc

  rescaled-form : ←̂ rescaled ≡
    RegularBase.lim family rescaled-regular-cauchy
  rescaled-form = refl

  regular-eq : ←̂ direct ≡ ←̂ rescaled
  regular-eq =
      direct-form
    ∙ cong (RegularBase.lim family)
        ((isPropΠ2 λ ε δ →
          RegularPremetric.isProp≈ (family ε) (family δ) (ε +₊ δ))
          direct-regular-cauchy rescaled-regular-cauchy)
    ∙ sym rescaled-form


signedSquareBoundedCauchyLimit : ∀ B
  → (x : ℚ₊ → ℚ)
  → IsBoundedBy B x
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
signedSquareBoundedCauchyLimit B x x-bounded xc =
  boundedCauchyLimit signedSquareℚ B (B +₊ B)
    (snd (signedSquareℚ-locallyLipschitz B)) x x-bounded xc


-- Consequently local Lipschitzness, rather than global Lipschitzness, is
-- enough to interpret every rational Cauchy family as a target limit.

locallyLipschitzCauchyLimit : ∀ f
  → IsLocallyLipschitz f
  → (x : ℚ₊ → ℚ)
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
locallyLipschitzCauchyLimit f f-local x xc =
  boundedCauchyLimit f B L local tail tail-bounded tail-cauchy
  where
  tail : ℚ₊ → ℚ
  tail = cauchyTail x

  B : ℚ₊
  B = cauchyTailBound x

  local-data : Σ[ L ∈ ℚ₊ ] IsLipschitzOnBallWith f B L
  local-data = f-local B

  L : ℚ₊
  L = fst local-data

  local : IsLipschitzOnBallWith f B L
  local = snd local-data

  tail-bounded : IsBoundedBy B tail
  tail-bounded = cauchyTailBounded x xc

  tail-cauchy : PremetricTheory.isCauchy ℚPremetricSpace tail
  tail-cauchy = cauchyTailCauchy x xc


locallyLipschitzCauchyLimitDirect : ∀ f
  → IsLocallyLipschitz f
  → (x : ℚ₊ → ℚ)
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
locallyLipschitzCauchyLimitDirect f f-local x xc =
  boundedCauchyLimitDirect f B L local tail tail-bounded tail-cauchy
  where
  tail : ℚ₊ → ℚ
  tail = cauchyTail x

  B : ℚ₊
  B = cauchyTailBound x

  local-data : Σ[ L ∈ ℚ₊ ] IsLipschitzOnBallWith f B L
  local-data = f-local B

  L : ℚ₊
  L = fst local-data

  local : IsLipschitzOnBallWith f B L
  local = snd local-data

  tail-bounded : IsBoundedBy B tail
  tail-bounded = cauchyTailBounded x xc

  tail-cauchy : PremetricTheory.isCauchy ℚPremetricSpace tail
  tail-cauchy = cauchyTailCauchy x xc

signedSquareCauchyLimit : (x : ℚ₊ → ℚ)
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
signedSquareCauchyLimit =
  locallyLipschitzCauchyLimit signedSquareℚ
    signedSquareℚ-locallyLipschitz

signedSquareCauchyLimitDirect : (x : ℚ₊ → ℚ)
  → PremetricTheory.isCauchy ℚPremetricSpace x
  → ℭ̂
signedSquareCauchyLimitDirect =
  locallyLipschitzCauchyLimitDirect signedSquareℚ
    signedSquareℚ-locallyLipschitz


-- The direct scaled constructor is a concrete advantage of the alternative
-- presentation: a per-family local constant is stored in Γ, while the regular
-- presentation must normalize the family explicitly.  This still does not
-- define a map ℭ̂ → ℭ̂; the remaining recursor clauses must show that the
-- chosen local bounds and constants are coherent for close families and for
-- nested limits.
