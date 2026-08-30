module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Lift.MapsCauchySequencesRelational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)

open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition

module S = SequentialDefinition ℚPremetricSpace

open PositiveRationals


MapsRationalCauchySequencesToReals : (ℚ → S.ℭ̂ₛ) → Type₀
MapsRationalCauchySequencesToReals f =
  ∀ q → S.SeqWitness (S.ι ∘ q) → S.SeqWitness (f ∘ q)


ImageRel : Type₁
ImageRel = ∀ {x y : S.ℭ̂ₛ} →
  S.ℭ̂ₛ → S.ℭ̂ₛ → ∀ ε → x S.∼̂ₛ[ ε ] y → Type₀


-- The part of the construction relevant at a limit.  In particular,
-- `imageCauchy` receives the relation induction hypotheses attached to an
-- explicit source Cauchy witness.  It does not receive, and cannot call, the
-- original base-map premise.

record RelationalCauchyCore
  (f : ℚ → S.ℭ̂ₛ)
  (maps : MapsRationalCauchySequencesToReals f) : Type₁ where

  no-eta-equality

  field
    R : ImageRel

    isPropR : ∀ {x y} a b ε r →
      isProp (R {x} {y} a b ε r)

    ι-ι-R : ∀ q r ε q≈r →
      R (f q) (f r) ε (S.ι-ι q r ε q≈r)

    imageCauchy :
      ∀ (x a : ℕ → S.ℭ̂ₛ) (μ : ℚ₊ → ℕ) →
      (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
        Σ[ r ∈ x m S.∼̂ₛ[ ε ] x n ]
          R (a m) (a n) ε r) →
      S.SeqWitness a


targetSeqWitness : ∀ {f maps}
  (c : RelationalCauchyCore f maps)
  {x : ℕ → S.ℭ̂ₛ} (a : ℕ → S.ℭ̂ₛ) →
  S.ElimSeqWitness (λ _ → S.ℭ̂ₛ)
    (RelationalCauchyCore.R c) a →
  S.SeqWitness a
targetSeqWitness c {x} a = PT.rec squash₁ λ where
  (μ , decorated) →
    c .RelationalCauchyCore.imageCauchy x a μ decorated


-- This is the proposed limit clause.  Its Cauchy proof is obtained solely
-- from the decorated relation data via `targetSeqWitness`; `maps` is not used
-- here.  The original truncated source witness remains only in the source
-- endpoint of the dependent motive.

relationalLimit : ∀ {f maps}
  (c : RelationalCauchyCore f maps)
  (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x)
  (a : ℕ → S.ℭ̂ₛ) →
  S.ElimSeqWitness (λ _ → S.ℭ̂ₛ)
    (RelationalCauchyCore.R c) a →
  S.ℭ̂ₛ
relationalLimit c x gx a decorated =
  S.lim a (targetSeqWitness c {x = x} a decorated)


-- Closure under the remaining constructors is kept separate from the core.
-- This makes `imageCauchy` the isolated experiment: a candidate `R` can be
-- tested there before doing the outer relation-constructor bookkeeping.

record RelationalCauchyClosure
  {f : ℚ → S.ℭ̂ₛ}
  {maps : MapsRationalCauchySequencesToReals f}
  (c : RelationalCauchyCore f maps) : Type₁ where

  no-eta-equality

  private
    R : ImageRel
    R = RelationalCauchyCore.R c

  field
    eq-R : ∀ {x y : S.ℭ̂ₛ}
      (p : ∀ ε → x S.∼̂ₛ[ ε ] y) (a b : S.ℭ̂ₛ) →
      (∀ ε δ → R a b (ε +₊ δ) (p (ε +₊ δ))) →
      (∀ ε → R a b ε (p ε)) →
      PathP (λ _ → S.ℭ̂ₛ) a b

    ι-lim-R : ∀ q y μ ε δ yc Δ r
      (a : ℕ → S.ℭ̂ₛ)
      (ydc : ∀ θ m n μθ≤m μθ≤n →
        R (a m) (a n) θ (yc θ m n μθ≤m μθ≤n)) →
      R (f q) (a (μ δ)) (ε -₊ δ , Δ) r →
      R (f q)
        (relationalLimit c y ∣ μ , yc ∣₁ a
          (S.decorateElimSeqWitness
            {A = λ _ → S.ℭ̂ₛ} {B = R} {x = y}
            a μ yc ydc))
        ε (S.ι-lim q y μ ε δ yc Δ r)

    lim-ι-R : ∀ x μ q ε δ xc Δ r
      (a : ℕ → S.ℭ̂ₛ)
      (xdc : ∀ θ m n μθ≤m μθ≤n →
        R (a m) (a n) θ (xc θ m n μθ≤m μθ≤n)) →
      R (a (μ δ)) (f q) (ε -₊ δ , Δ) r →
      R
        (relationalLimit c x ∣ μ , xc ∣₁ a
          (S.decorateElimSeqWitness
            {A = λ _ → S.ℭ̂ₛ} {B = R} {x = x}
            a μ xc xdc))
        (f q) ε (S.lim-ι x μ q ε δ xc Δ r)

    lim-lim-R : ∀ x μ y ν ε δ η xc yc Δ r
      (a : ℕ → S.ℭ̂ₛ)
      (xdc : ∀ θ m n μθ≤m μθ≤n →
        R (a m) (a n) θ (xc θ m n μθ≤m μθ≤n))
      (b : ℕ → S.ℭ̂ₛ)
      (ydc : ∀ θ m n νθ≤m νθ≤n →
        R (b m) (b n) θ (yc θ m n νθ≤m νθ≤n)) →
      R (a (μ δ)) (b (ν η))
        (ε -₊ (δ +₊ η) , Δ) r →
      R
        (relationalLimit c x ∣ μ , xc ∣₁ a
          (S.decorateElimSeqWitness
            {A = λ _ → S.ℭ̂ₛ} {B = R} {x = x}
            a μ xc xdc))
        (relationalLimit c y ∣ ν , yc ∣₁ b
          (S.decorateElimSeqWitness
            {A = λ _ → S.ℭ̂ₛ} {B = R} {x = y}
            b ν yc ydc))
        ε (S.lim-lim x μ y ν ε δ η xc yc Δ r)

    tri-R : ∀ x y z ε δ r s
      (a b d : S.ℭ̂ₛ) →
      R {x} {y} a b ε r → R {y} {z} b d δ s →
      R {x} {z} a d (ε +₊ δ) (S.tri∼ x y z ε δ r s)


relationalEliminator : ∀ {f maps}
  (c : RelationalCauchyCore f maps) →
  RelationalCauchyClosure c →
  S.Elimℭ̂ₛ (λ _ → S.ℭ̂ₛ) (RelationalCauchyCore.R c)
relationalEliminator {f} c k .S.Elimℭ̂ₛ.ιA = f
relationalEliminator c k .S.Elimℭ̂ₛ.limA = relationalLimit c
relationalEliminator c k .S.Elimℭ̂ₛ.eqA =
  RelationalCauchyClosure.eq-R k
relationalEliminator c k .S.Elimℭ̂ₛ.ι-ι-B =
  RelationalCauchyCore.ι-ι-R c
relationalEliminator c k .S.Elimℭ̂ₛ.ι-lim-B =
  RelationalCauchyClosure.ι-lim-R k
relationalEliminator c k .S.Elimℭ̂ₛ.lim-ι-B =
  RelationalCauchyClosure.lim-ι-R k
relationalEliminator c k .S.Elimℭ̂ₛ.lim-lim-B =
  RelationalCauchyClosure.lim-lim-R k
relationalEliminator c k .S.Elimℭ̂ₛ.tri-B =
  RelationalCauchyClosure.tri-R k
relationalEliminator c k .S.Elimℭ̂ₛ.isPropB =
  RelationalCauchyCore.isPropR c


liftRelationally : ∀ {f maps}
  (c : RelationalCauchyCore f maps) →
  RelationalCauchyClosure c →
  S.ℭ̂ₛ → S.ℭ̂ₛ
liftRelationally c k = S.Elimℭ̂ₛ.go (relationalEliminator c k)

liftRelationally-ι : ∀ {f maps}
  (c : RelationalCauchyCore f maps)
  (k : RelationalCauchyClosure c) q →
  liftRelationally c k (S.ι q) ≡ f q
liftRelationally-ι c k q = refl

liftRelationally-lim : ∀ {f maps}
  (c : RelationalCauchyCore f maps)
  (k : RelationalCauchyClosure c) x gx →
  liftRelationally c k (S.lim x gx) ≡
    relationalLimit c x gx (liftRelationally c k ∘ x)
      (S.Elimℭ̂ₛ.mapWitness (relationalEliminator c k) gx)
liftRelationally-lim c k x gx = refl


-- First concrete candidate -------------------------------------------------
--
-- Instead of asking a relation proof to give a target-radius estimate, ask
-- it to carry Cauchy preservation for the two-point graph determined by its
-- endpoints.  This is genuinely obtainable in the `ι-ι` case from `maps`:
-- an untruncated pointwise two-point graph determines an actual rational
-- sequence, so no countable choice is used.

TwoPointGraph :
  (x a y b : S.ℭ̂ₛ) →
  (ℕ → S.ℭ̂ₛ) → (ℕ → S.ℭ̂ₛ) → Type₀
TwoPointGraph x a y b z w = ∀ n →
  ((z n ≡ x) × (w n ≡ a)) ⊎
  ((z n ≡ y) × (w n ≡ b))

TwoPointCauchyRel : (f : ℚ → S.ℭ̂ₛ) → ImageRel
TwoPointCauchyRel f {x} {y} a b ε r =
  ∀ (z w : ℕ → S.ℭ̂ₛ) →
  TwoPointGraph x a y b z w →
  S.SeqWitness z → S.SeqWitness w

isPropTwoPointCauchyRel : ∀ f {x y} a b ε r →
  isProp (TwoPointCauchyRel f {x} {y} a b ε r)
isPropTwoPointCauchyRel f a b ε r =
  isPropΠ2 λ _ _ → isPropΠ λ _ → isPropΠ λ _ → squash₁


twoPoint-ι-ι : ∀ (f : ℚ → S.ℭ̂ₛ)
  (maps : MapsRationalCauchySequencesToReals f)
  q r ε q≈r →
  TwoPointCauchyRel f (f q) (f r) ε
    (S.ι-ι q r ε q≈r)
twoPoint-ι-ι f maps q r ε q≈r z w graph gz =
  subst S.SeqWitness (sym w≡f∘u)
    (maps u (subst S.SeqWitness z≡ι∘u gz))
  where
  u : ℕ → ℚ
  u n with graph n
  ... | inl _ = q
  ... | inr _ = r

  z≡ι∘u : z ≡ S.ι ∘ u
  z≡ι∘u = funExt pointwise
    where
    pointwise : ∀ n → z n ≡ S.ι (u n)
    pointwise n with graph n
    ... | inl left = left .fst
    ... | inr right = right .fst

  w≡f∘u : w ≡ f ∘ u
  w≡f∘u = funExt pointwise
    where
    pointwise : ∀ n → w n ≡ f (u n)
    pointwise n with graph n
    ... | inl left = left .snd
    ... | inr right = right .snd


-- What remains for this candidate is now stated without any eliminator
-- bookkeeping.  Each decorated relation proof carries a two-point Cauchy
-- action, but `imageCauchy` needs one action for the entire varying graph.
-- This implication is the place to strengthen the definition of `R`.

TwoPointImageCauchy : (f : ℚ → S.ℭ̂ₛ) → Type₀
TwoPointImageCauchy f =
  ∀ (x a : ℕ → S.ℭ̂ₛ) (μ : ℚ₊ → ℕ) →
  (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
    Σ[ r ∈ x m S.∼̂ₛ[ ε ] x n ]
      TwoPointCauchyRel f (a m) (a n) ε r) →
  S.SeqWitness a


twoPointCore : ∀ (f : ℚ → S.ℭ̂ₛ)
  (maps : MapsRationalCauchySequencesToReals f) →
  TwoPointImageCauchy f →
  RelationalCauchyCore f maps
twoPointCore f maps image .RelationalCauchyCore.R =
  TwoPointCauchyRel f
twoPointCore f maps image .RelationalCauchyCore.isPropR =
  isPropTwoPointCauchyRel f
twoPointCore f maps image .RelationalCauchyCore.ι-ι-R =
  twoPoint-ι-ι f maps
twoPointCore f maps image .RelationalCauchyCore.imageCauchy = image


-- Shared-graph candidate --------------------------------------------------
--
-- The two-point relation above loses coherence between different pairs of
-- indices.  A stronger relation can say that all endpoint pairs belong to
-- one fixed graph.  Its proofs also carry (propositionally) the fact that
-- this graph sends Cauchy sequences to Cauchy sequences.  The latter fact is
-- deliberately extracted from a relation proof in `graphImageCauchy`.

shiftSeq : ℕ → (ℕ → S.ℭ̂ₛ) → ℕ → S.ℭ̂ₛ
shiftSeq N x n = x (n ℕ.+ N)


shiftSeqWitness : ∀ N x →
  S.SeqWitness x → S.SeqWitness (shiftSeq N x)
shiftSeqWitness N x = PT.map λ where
  (μ , xc) →
    μ , λ ε m n με≤m με≤n →
      xc ε (m ℕ.+ N) (n ℕ.+ N)
        (ℕ.≤-trans με≤m ℕ.≤SumLeft)
        (ℕ.≤-trans με≤n ℕ.≤SumLeft)


unshiftSeqWitness : ∀ N x →
  S.SeqWitness (shiftSeq N x) → S.SeqWitness x
unshiftSeqWitness N x = PT.map λ where
  (μ , xc) →
    (λ ε → μ ε ℕ.+ N) , λ ε m n μN≤m μN≤n →
      let
        dm = μN≤m .fst
        dn = μN≤n .fst

        m-path : (dm ℕ.+ μ ε) ℕ.+ N ≡ m
        m-path = sym (ℕ.+-assoc dm (μ ε) N) ∙ μN≤m .snd

        n-path : (dn ℕ.+ μ ε) ℕ.+ N ≡ n
        n-path = sym (ℕ.+-assoc dn (μ ε) N) ∙ μN≤n .snd
      in
      subst2 (λ u v → x u S.∼̂ₛ[ ε ] x v)
        m-path n-path
        (xc ε (dm ℕ.+ μ ε) (dn ℕ.+ μ ε)
          ℕ.≤SumRight ℕ.≤SumRight)


GraphPreservesCauchy :
  (S.ℭ̂ₛ → S.ℭ̂ₛ → Type₀) → Type₀
GraphPreservesCauchy G =
  ∀ x a → (∀ n → G (x n) (a n)) →
  S.SeqWitness x → S.SeqWitness a


record CauchyGraph (f : ℚ → S.ℭ̂ₛ) : Type₁ where

  no-eta-equality

  field
    G : S.ℭ̂ₛ → S.ℭ̂ₛ → Type₀
    isPropG : ∀ x a → isProp (G x a)
    ι-G : ∀ q → G (S.ι q) (f q)
    preservesCauchy : GraphPreservesCauchy G


GraphCauchyRel : ∀ {f} → CauchyGraph f → ImageRel
GraphCauchyRel g {x} {y} a b ε r =
  CauchyGraph.G g x a ×
  CauchyGraph.G g y b ×
  GraphPreservesCauchy (CauchyGraph.G g)


isPropGraphCauchyRel : ∀ {f} (g : CauchyGraph f)
  {x y} a b ε r →
  isProp (GraphCauchyRel g {x} {y} a b ε r)
isPropGraphCauchyRel g {x} {y} a b ε r =
  isProp× (CauchyGraph.isPropG g x a)
    (isProp× (CauchyGraph.isPropG g y b)
      (isPropΠ2 λ _ _ → isPropΠ λ _ → isPropΠ λ _ → squash₁))


graph-ι-ι : ∀ {f} (g : CauchyGraph f) q r ε q≈r →
  GraphCauchyRel g (f q) (f r) ε
    (S.ι-ι q r ε q≈r)
graph-ι-ι g q r ε q≈r =
  CauchyGraph.ι-G g q ,
  CauchyGraph.ι-G g r ,
  CauchyGraph.preservesCauchy g


-- The target Cauchy proof below uses only `decorated`.  At the fixed radius
-- 1, its diagonal entries provide graph membership for a common tail and
-- one copy of the graph-preservation operation.  The source witness is
-- reconstructed from the source components of the same decorated data.

graphImageCauchy : ∀ {f} (g : CauchyGraph f)
  (x a : ℕ → S.ℭ̂ₛ) (μ : ℚ₊ → ℕ) →
  (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
    Σ[ r ∈ x m S.∼̂ₛ[ ε ] x n ]
      GraphCauchyRel g (a m) (a n) ε r) →
  S.SeqWitness a
graphImageCauchy g x a μ decorated =
  unshiftSeqWitness N a
    (preserves tail-x tail-a graph-tail
      (shiftSeqWitness N x source-witness))
  where
  N : ℕ
  N = μ 1

  source-witness : S.SeqWitness x
  source-witness =
    ∣ μ , (λ ε m n με≤m με≤n →
      decorated ε m n με≤m με≤n .fst) ∣₁

  tail-x tail-a : ℕ → S.ℭ̂ₛ
  tail-x = shiftSeq N x
  tail-a = shiftSeq N a

  at : ∀ n →
    GraphCauchyRel g (tail-a n) (tail-a n) 1
      (decorated 1 (n ℕ.+ N) (n ℕ.+ N)
        ℕ.≤SumRight ℕ.≤SumRight .fst)
  at n =
    decorated 1 (n ℕ.+ N) (n ℕ.+ N)
      ℕ.≤SumRight ℕ.≤SumRight .snd

  graph-tail : ∀ n → CauchyGraph.G g (tail-x n) (tail-a n)
  graph-tail n = at n .fst

  preserves : GraphPreservesCauchy (CauchyGraph.G g)
  preserves = at 0 .snd .snd


graphCore : ∀ (f : ℚ → S.ℭ̂ₛ)
  (maps : MapsRationalCauchySequencesToReals f) →
  CauchyGraph f → RelationalCauchyCore f maps
graphCore f maps g .RelationalCauchyCore.R = GraphCauchyRel g
graphCore f maps g .RelationalCauchyCore.isPropR =
  isPropGraphCauchyRel g
graphCore f maps g .RelationalCauchyCore.ι-ι-R = graph-ι-ι g
graphCore f maps g .RelationalCauchyCore.imageCauchy =
  graphImageCauchy g


-- The graph relation is also stable under all relation constructors once
-- the graph is single-valued and closed under the particular limit operation
-- above.  Keeping these two obligations in a separate record exposes what
-- is still needed to turn the relational core into a complete lifting.

record ClosedCauchyGraph
  {f : ℚ → S.ℭ̂ₛ}
  (maps : MapsRationalCauchySequencesToReals f)
  (g : CauchyGraph f) : Type₁ where

  no-eta-equality

  private
    G = CauchyGraph.G g
    c = graphCore f maps g

  field
    functional : ∀ x a b → G x a → G x b → a ≡ b

    lim-G : ∀ x μ xc (a : ℕ → S.ℭ̂ₛ)
      (xdc : ∀ θ m n μθ≤m μθ≤n →
        GraphCauchyRel g (a m) (a n) θ
          (xc θ m n μθ≤m μθ≤n)) →
      G (S.lim x ∣ μ , xc ∣₁)
        (relationalLimit c x ∣ μ , xc ∣₁ a
          (S.decorateElimSeqWitness
            {A = λ _ → S.ℭ̂ₛ} {B = GraphCauchyRel g} {x = x}
            a μ xc xdc))


graphClosure : ∀ {f}
  (maps : MapsRationalCauchySequencesToReals f)
  (g : CauchyGraph f) →
  ClosedCauchyGraph maps g →
  RelationalCauchyClosure (graphCore f maps g)
graphClosure {f} maps g closed .RelationalCauchyClosure.eq-R
  {x} {y} p a b broad direct =
  ClosedCauchyGraph.functional closed x a b
    (direct 1 .fst)
    (subst (λ z → CauchyGraph.G g z b)
      (sym (S.eqℭ x y p)) (direct 1 .snd .fst))
graphClosure maps g closed .RelationalCauchyClosure.ι-lim-R
  q y μ ε δ yc Δ r a ydc inner =
  CauchyGraph.ι-G g q ,
  ClosedCauchyGraph.lim-G closed y μ yc a ydc ,
  CauchyGraph.preservesCauchy g
graphClosure maps g closed .RelationalCauchyClosure.lim-ι-R
  x μ q ε δ xc Δ r a xdc inner =
  ClosedCauchyGraph.lim-G closed x μ xc a xdc ,
  CauchyGraph.ι-G g q ,
  CauchyGraph.preservesCauchy g
graphClosure maps g closed .RelationalCauchyClosure.lim-lim-R
  x μ y ν ε δ η xc yc Δ r a xdc b ydc inner =
  ClosedCauchyGraph.lim-G closed x μ xc a xdc ,
  ClosedCauchyGraph.lim-G closed y ν yc b ydc ,
  CauchyGraph.preservesCauchy g
graphClosure maps g closed .RelationalCauchyClosure.tri-R
  x y z ε δ r s a b d ab bd =
  ab .fst , bd .snd .fst , ab .snd .snd


liftByClosedCauchyGraph : ∀ {f}
  (maps : MapsRationalCauchySequencesToReals f)
  (g : CauchyGraph f) →
  ClosedCauchyGraph maps g →
  S.ℭ̂ₛ → S.ℭ̂ₛ
liftByClosedCauchyGraph {f} maps g closed =
  liftRelationally (graphCore f maps g) (graphClosure maps g closed)


liftByClosedCauchyGraph-ι : ∀ {f}
  (maps : MapsRationalCauchySequencesToReals f)
  (g : CauchyGraph f)
  (closed : ClosedCauchyGraph maps g) q →
  liftByClosedCauchyGraph maps g closed (S.ι q) ≡ f q
liftByClosedCauchyGraph-ι maps g closed q = refl
