module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.UniformlyContinuousRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Properties as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  as MoreRefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Properties
  as MoreRefinedPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.ToRefined
  as ToRefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Refined
  as RefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative
  as AlternativeDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularClosenessDefinition

module S = MoreRefinedDefinition ℚPremetricSpace
module SP = MoreRefinedPropertiesDefinition ℚPremetricSpace
module ST = ToRefinedDefinition ℚPremetricSpace
module R = RefinedDefinition ℚPremetricSpace
module A = AlternativeDefinition ℚPremetricSpace
module C = RegularClosenessDefinition ℚPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module PC = PremetricStr (C.ℭPremetricSpace .snd)


-- The composite comparison with the regular completion is used only to
-- reflect a relation between two injected rationals back to their original
-- rational distance.  The lifting construction itself stays in ℭ̂ₛ.

toRegular : S.ℭ̂ₛ → A.RegularBase.ℭ
toRegular = A.←̂ ∘ R.fromRefined ∘ ST.toRefined

toRegular∼ : ∀ x y ε →
  x S.∼̂ₛ[ ε ] y → toRegular x A.RegularBase.∼[ ε ] toRegular y
toRegular∼ x y ε p =
  A.←̂~ _ _ ε
    (R.fromRefined∼ _ _ ε (ST.toRefined∼ x y ε p))

ι-ι-reflects∼ : ∀ x y ε →
  S.ι x S.∼̂ₛ[ ε ] S.ι y → x Pℚ.≈[ ε ] y
ι-ι-reflects∼ x y ε p = C.ι-ι→≈ x y ε (toRegular∼ _ _ ε p)


private
  tripleQuarter< : ∀ ε → ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
           (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾


-- This graph predicate is continuity-agnostic.  Different hypotheses on f
-- are used below only to prove that its fibers exist and are unique.

JointlyApproximableFor : (ℚ → ℚ) → S.ℭ̂ₛ → S.ℭ̂ₛ → Type₀
JointlyApproximableFor f x y = ∀ α β →
  ∃[ q ∈ ℚ ]
    (S.ι q S.∼̂ₛ[ α ] x) ×
    (S.ι (f q) S.∼̂ₛ[ β ] y)

isPropJointlyApproximableFor : ∀ f x y →
  isProp (JointlyApproximableFor f x y)
isPropJointlyApproximableFor f x y = isPropΠ2 λ _ _ → squash₁


module WithModulus
  (f : ℚ → ℚ)
  (μ : ℚ₊ → ℚ₊)
  (f-uc : IsUniformlyContinuousWith
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd) μ) where

  inputBudget : ℚ₊ → ℚ₊
  inputBudget ε = μ (ε /4₊) /4₊

  JointlyApproximable : S.ℭ̂ₛ → S.ℭ̂ₛ → Type₀
  JointlyApproximable = JointlyApproximableFor f

  isPropJointlyApproximable : ∀ x y →
    isProp (JointlyApproximable x y)
  isPropJointlyApproximable = isPropJointlyApproximableFor f

  jointlyApproximable-pres∼ : ∀ x x' y y' ε →
    JointlyApproximable x y →
    JointlyApproximable x' y' →
    x S.∼̂ₛ[ inputBudget ε ] x' →
    y S.∼̂ₛ[ ε ] y'
  jointlyApproximable-pres∼ x x' y y' ε xy x'y' x∼x' =
    PT.rec2 (S.isProp∼ y ε y') step
      (xy sourceRadius outputRadius)
      (x'y' sourceRadius outputRadius)
    where
    outputRadius = ε /4₊
    sourceRadius = inputBudget ε

    step :
      (Σ[ q ∈ ℚ ]
        (S.ι q S.∼̂ₛ[ sourceRadius ] x) ×
        (S.ι (f q) S.∼̂ₛ[ outputRadius ] y)) →
      (Σ[ q ∈ ℚ ]
        (S.ι q S.∼̂ₛ[ sourceRadius ] x') ×
        (S.ι (f q) S.∼̂ₛ[ outputRadius ] y')) →
      y S.∼̂ₛ[ ε ] y'
    step (q , ιq∼x , ιfq∼y) (r , ιr∼x' , ιfr∼y') =
      S.isMonotone∼̂ₛ< y y' _ ε (tripleQuarter< ε)
        (S.tri∼ y (S.ι (f r)) y'
          (outputRadius +₊ outputRadius) outputRadius
          (S.tri∼ y (S.ι (f q)) (S.ι (f r))
            outputRadius outputRadius
            (S.sym∼ _ _ outputRadius ιfq∼y)
            (S.ι-ι (f q) (f r) outputRadius f-q∼f-r))
          ιfr∼y')
      where
      q∼r-small : S.ι q S.∼̂ₛ[
          (sourceRadius +₊ sourceRadius) +₊ sourceRadius
        ] S.ι r
      q∼r-small =
        S.tri∼ (S.ι q) x' (S.ι r)
          (sourceRadius +₊ sourceRadius) sourceRadius
          (S.tri∼ (S.ι q) x x'
            sourceRadius sourceRadius ιq∼x x∼x')
          (S.sym∼ _ _ sourceRadius ιr∼x')

      q∼r : q Pℚ.≈[ μ outputRadius ] r
      q∼r = ι-ι-reflects∼ q r (μ outputRadius)
        (S.isMonotone∼̂ₛ< _ _ _ (μ outputRadius)
          (tripleQuarter< (μ outputRadius)) q∼r-small)

      f-q∼f-r : f q Pℚ.≈[ outputRadius ] f r
      f-q∼f-r =
        f-uc .IsUniformlyContinuousWith.pres≈ q r outputRadius q∼r

  jointlyApproximable-equal : ∀ x y y' →
    JointlyApproximable x y →
    JointlyApproximable x y' → y ≡ y'
  jointlyApproximable-equal x y y' xy xy' =
    S.eqℭ y y' λ ε →
      jointlyApproximable-pres∼ x x y y' ε xy xy'
        (S.isRefl∼̂ₛ x (inputBudget ε))

  Fiber : S.ℭ̂ₛ → Type₀
  Fiber x = Σ[ y ∈ S.ℭ̂ₛ ] JointlyApproximable x y

  isPropFiber : ∀ x → isProp (Fiber x)
  isPropFiber x (y , xy) (y' , xy') =
    Σ≡Prop (isPropJointlyApproximable x)
      (jointlyApproximable-equal x y y' xy xy')

  baseFiber : (q : ℚ) → Fiber (S.ι q)
  baseFiber q .fst = S.ι (f q)
  baseFiber q .snd α β =
    ∣ q , S.isRefl∼̂ₛ (S.ι q) α
        , S.isRefl∼̂ₛ (S.ι (f q)) β ∣₁


  -- The natural-number Cauchy modulus is exactly what makes arbitrary
  -- uniform moduli compositional here.  No monotonicity of μ is needed.

  imageCauchySeq : ∀ x y →
    (∀ n → JointlyApproximable (x n) (y n)) →
    S.CauchySeq x → S.CauchySeq y
  imageCauchySeq x y joint (N , xc) .fst ε = N (inputBudget ε)
  imageCauchySeq x y joint (N , xc) .snd ε m n Nε≤m Nε≤n =
    jointlyApproximable-pres∼ (x m) (x n) (y m) (y n) ε
      (joint m) (joint n)
      (xc (inputBudget ε) m n Nε≤m Nε≤n)

  imageSeqWitness : ∀ x y →
    (∀ n → JointlyApproximable (x n) (y n)) →
    S.SeqWitness x → S.SeqWitness y
  imageSeqWitness x y joint = PT.map (imageCauchySeq x y joint)


  -- A sufficiently late term of a represented sequence can be connected to
  -- its limit when the left endpoint is injected.  This asymmetric form is
  -- precisely what JointlyApproximable needs and avoids choosing a rational
  -- approximation to an arbitrary completion point.

  ι-close-lim-from-late : ∀ q x gx N xc ε n →
    N (ε /4₊) ℕ.≤ n →
    S.ι q S.∼̂ₛ[ ε /4₊ ] x n →
    S.ι q S.∼̂ₛ[ ε ] S.lim x gx
  ι-close-lim-from-late q x gx N xc ε n Nδ≤n ιq∼xn =
    subst (S.ι q S.∼̂ₛ[ ε ]_)
      (cong (S.lim x) (squash₁ ∣ N , xc ∣₁ gx)) concrete
    where
    δ = ε /4₊

    x-n∼x-Nδ : x n S.∼̂ₛ[ δ ] x (N δ)
    x-n∼x-Nδ = xc δ n (N δ) Nδ≤n ℕ.≤-refl

    small : S.ι q S.∼̂ₛ[ δ +₊ δ ] x (N δ)
    small = S.tri∼ (S.ι q) (x n) (x (N δ)) δ δ
      ιq∼xn x-n∼x-Nδ

    δ<ε : δ <₊ ε
    δ<ε = /4₊<id ε

    Δ : 0 <ℚ ε -₊ δ
    Δ = <→0<Δ (fst δ) (fst ε) δ<ε

    target = (ε -₊ δ , Δ)

    small<target : (δ +₊ δ) <₊ target
    small<target = +CancelR<
      (fst (δ +₊ δ)) (fst target) (fst δ)
      (subst (fst (δ +₊ δ) ℚ.+ fst δ <ℚ_)
        (sym (minusPlus₊ ε δ)) (tripleQuarter< ε))

    enlarged : S.ι q S.∼̂ₛ[ target ] x (N δ)
    enlarged = S.isMonotone∼̂ₛ< _ _ _ target small<target small

    concrete : S.ι q S.∼̂ₛ[ ε ] S.lim x ∣ N , xc ∣₁
    concrete = S.ι-lim q x N ε δ xc Δ enlarged


  limitJointlyApproximable : ∀ x gx y
    (joint : ∀ n → JointlyApproximable (x n) (y n)) →
    JointlyApproximable
      (S.lim x gx)
      (S.lim y (imageSeqWitness x y joint gx))
  limitJointlyApproximable x gx y joint α β =
    PT.rec squash₁ withCauchy gx
    where
    withCauchy : S.CauchySeq x →
      ∃[ q ∈ ℚ ]
        (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
        (S.ι (f q) S.∼̂ₛ[ β ]
          S.lim y (imageSeqWitness x y joint gx))
    withCauchy sourceCauchy@(N , xc) =
      PT.map makeLateApproximation (joint n (α /4₊) (β /4₊))
      where
      targetCauchy : S.CauchySeq y
      targetCauchy = imageCauchySeq x y joint sourceCauchy

      K : ℚ₊ → ℕ
      K = targetCauchy .fst

      yc : ∀ ε m n → K ε ℕ.≤ m → K ε ℕ.≤ n →
        y m S.∼̂ₛ[ ε ] y n
      yc = targetCauchy .snd

      n : ℕ
      n = ℕ.max (N (α /4₊)) (K (β /4₊))

      makeLateApproximation :
        (Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ α /4₊ ] x n) ×
          (S.ι (f q) S.∼̂ₛ[ β /4₊ ] y n)) →
        Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
          (S.ι (f q) S.∼̂ₛ[ β ]
            S.lim y (imageSeqWitness x y joint gx))
      makeLateApproximation (q , ιq∼xn , ιfq∼yn) = q ,
        ι-close-lim-from-late q x gx N xc α n
          (ℕ.left-≤-max
            {m = N (α /4₊)} {n = K (β /4₊)}) ιq∼xn ,
        ι-close-lim-from-late (f q) y
          (imageSeqWitness x y joint gx) K yc β n
          (ℕ.right-≤-max
            {n = K (β /4₊)} {m = N (α /4₊)}) ιfq∼yn


  limitFiber : ∀ x gx → (∀ n → Fiber (x n)) → Fiber (S.lim x gx)
  limitFiber x gx IH =
    S.lim y (imageSeqWitness x y joint gx) ,
    limitJointlyApproximable x gx y joint
    where
    y : ℕ → S.ℭ̂ₛ
    y n = IH n .fst

    joint : ∀ n → JointlyApproximable (x n) (y n)
    joint n = IH n .snd


  private
    fiberElim : S.Elimℭ̂ₛ-Prop Fiber
    fiberElim .S.Elimℭ̂ₛ-Prop.ιA = baseFiber
    fiberElim .S.Elimℭ̂ₛ-Prop.limA = limitFiber
    fiberElim .S.Elimℭ̂ₛ-Prop.isPropA = isPropFiber

  liftFiber : ∀ x → Fiber x
  liftFiber = S.Elimℭ̂ₛ-Prop.go fiberElim

  liftUniformlyContinuousWith : S.ℭ̂ₛ → S.ℭ̂ₛ
  liftUniformlyContinuousWith x = liftFiber x .fst

  liftUniformlyContinuousWith-joint : ∀ x →
    JointlyApproximable x (liftUniformlyContinuousWith x)
  liftUniformlyContinuousWith-joint x = liftFiber x .snd

  liftUniformlyContinuousWith-pres∼ : ∀ x y ε →
    x S.∼̂ₛ[ inputBudget ε ] y →
    liftUniformlyContinuousWith x S.∼̂ₛ[ ε ]
      liftUniformlyContinuousWith y
  liftUniformlyContinuousWith-pres∼ x y ε =
    jointlyApproximable-pres∼ x y
      (liftUniformlyContinuousWith x) (liftUniformlyContinuousWith y) ε
      (liftUniformlyContinuousWith-joint x)
      (liftUniformlyContinuousWith-joint y)

  liftUniformlyContinuousWith-isUniformlyContinuousWith :
    IsUniformlyContinuousWith
      (SP.ℭ̂ₛPremetricSpace .snd) liftUniformlyContinuousWith
      (SP.ℭ̂ₛPremetricSpace .snd) inputBudget
  liftUniformlyContinuousWith-isUniformlyContinuousWith =
    isuniformlycontinuouswith liftUniformlyContinuousWith-pres∼

  liftUniformlyContinuousWith-ι : ∀ q →
    liftUniformlyContinuousWith (S.ι q) ≡ S.ι (f q)
  liftUniformlyContinuousWith-ι q = refl


-- The ordinary notion of uniform continuity merely asserts the existence of
-- a modulus.  Since functions into ℭ̂ₛ form a set, the set-recursion
-- principle for propositional truncation packages the explicit construction.
-- Its coherence is supplied by JointlyApproximable, which does not mention
-- the chosen modulus.

UniformContinuityData : (ℚ → ℚ) → Type₀
UniformContinuityData f =
  Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
    IsUniformlyContinuousWith
      (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd) μ

private
  liftWithData : ∀ f → UniformContinuityData f → S.ℭ̂ₛ → S.ℭ̂ₛ
  liftWithData f (μ , f-uc) =
    WithModulus.liftUniformlyContinuousWith f μ f-uc

  liftWithData-independent : ∀ f
    (u v : UniformContinuityData f) →
    liftWithData f u ≡ liftWithData f v
  liftWithData-independent f (μ , f-uc) (ν , f-uc') = funExt λ x →
    WithModulus.jointlyApproximable-equal f μ f-uc x _ _
      (WithModulus.liftUniformlyContinuousWith-joint f μ f-uc x)
      (WithModulus.liftUniformlyContinuousWith-joint f ν f-uc' x)

  liftRec : ∀ f → PT.Rec→Set {A = UniformContinuityData f}
    (S.ℭ̂ₛ → S.ℭ̂ₛ)
  liftRec f .PT.Rec→Set.isSetB = isSetΠ λ _ → S.isSetℭ̂ₛ
  liftRec f .PT.Rec→Set.f = liftWithData f
  liftRec f .PT.Rec→Set.fconst = liftWithData-independent f


liftUniformlyContinuous : (f : ℚ → ℚ) →
  isUniformlyContinuous
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd) →
  S.ℭ̂ₛ → S.ℭ̂ₛ
liftUniformlyContinuous f = PT.Rec→Set.go (liftRec f)

liftUniformlyContinuous-β : ∀ f μ f-uc →
  liftUniformlyContinuous f ∣ μ , f-uc ∣₁ ≡
    WithModulus.liftUniformlyContinuousWith f μ f-uc
liftUniformlyContinuous-β f μ f-uc =
  PT.Rec→Set.β-go (liftRec f) (μ , f-uc)

liftUniformlyContinuous-ι : ∀ f f-uc q →
  liftUniformlyContinuous f f-uc (S.ι q) ≡ S.ι (f q)
liftUniformlyContinuous-ι f = PT.elim motive onData
  where
  motive : ∀ f-uc → isProp
    (∀ q → liftUniformlyContinuous f f-uc (S.ι q) ≡ S.ι (f q))
  motive f-uc = isPropΠ λ q →
    S.isSetℭ̂ₛ (liftUniformlyContinuous f f-uc (S.ι q)) (S.ι (f q))

  onData : ∀ d q →
    liftUniformlyContinuous f ∣ d ∣₁ (S.ι q) ≡ S.ι (f q)
  onData (μ , f-uc) q =
    cong (_$ S.ι q) (liftUniformlyContinuous-β f μ f-uc)
    ∙ WithModulus.liftUniformlyContinuousWith-ι f μ f-uc q


-- This is the uniform-continuity package before installing the derived
-- premetric record for ℭ̂ₛ: mere existence of a modulus preserving its
-- primitive closeness relation.

Preserves∼With : (S.ℭ̂ₛ → S.ℭ̂ₛ) → (ℚ₊ → ℚ₊) → Type₀
Preserves∼With F μ = ∀ x y ε →
  x S.∼̂ₛ[ μ ε ] y → F x S.∼̂ₛ[ ε ] F y

isUniformlyContinuous∼ : (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
isUniformlyContinuous∼ F = ∃[ μ ∈ (ℚ₊ → ℚ₊) ] Preserves∼With F μ

liftUniformlyContinuous-isUniformlyContinuous∼ : ∀ f
  (f-uc : isUniformlyContinuous
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd)) →
  isUniformlyContinuous∼ (liftUniformlyContinuous f f-uc)
liftUniformlyContinuous-isUniformlyContinuous∼ f f-uc =
  PT.map makeModulus f-uc
  where
  makeModulus : UniformContinuityData f →
    Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      Preserves∼With (liftUniformlyContinuous f f-uc) μ
  makeModulus (μ , f-uc-with) =
    WithModulus.inputBudget f μ f-uc-with , preserve
    where
    explicit = WithModulus.liftUniformlyContinuousWith f μ f-uc-with

    packaged≡explicit : liftUniformlyContinuous f f-uc ≡ explicit
    packaged≡explicit = PT.elim
      (λ t → (isSetΠ λ _ → S.isSetℭ̂ₛ)
        (liftUniformlyContinuous f t) explicit)
      (λ { (ν , f-uc-ν) →
          liftUniformlyContinuous-β f ν f-uc-ν
        ∙ liftWithData-independent f
            (ν , f-uc-ν) (μ , f-uc-with) })
      f-uc

    preserve : Preserves∼With (liftUniformlyContinuous f f-uc)
      (WithModulus.inputBudget f μ f-uc-with)
    preserve x y ε x∼y = subst2 (S._∼̂ₛ[ ε ]_)
      (sym (funExt⁻ packaged≡explicit x))
      (sym (funExt⁻ packaged≡explicit y))
      (WithModulus.liftUniformlyContinuousWith-pres∼
        f μ f-uc-with x y ε x∼y)


liftUniformlyContinuous-isUniformlyContinuous : ∀ f
  (f-uc : isUniformlyContinuous
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd)) →
  isUniformlyContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) (liftUniformlyContinuous f f-uc)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftUniformlyContinuous-isUniformlyContinuous f f-uc =
  PT.map
    (λ { (μ , pres) → μ , isuniformlycontinuouswith pres })
    (liftUniformlyContinuous-isUniformlyContinuous∼ f f-uc)
