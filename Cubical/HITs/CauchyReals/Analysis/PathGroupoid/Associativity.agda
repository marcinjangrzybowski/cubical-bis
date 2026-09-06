module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Associativity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Pasting
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Factorization
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Subdivision
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (_∘UC_)

private
  a : Clocks.UCPath 𝟘 half
  a = firstClock , first-0 , first-1
  b : Clocks.UCPath half fiveSixths
  b = middleClock , middle-0 , middle-1
  c : Clocks.UCPath fiveSixths 𝟙
  c = lastClock , last-0 , last-1

  ρa ρb ρc : UC[ Interval , Interval ]
  ρa = early ∘UC firstClock
  ρb = early ∘UC (late ∘UC middleClock)
  ρc = late ∘UC (late ∘UC lastClock)

  ρa-0 : fst ρa 𝟘 ≡ 𝟘
  ρa-0 = cong (fst early) first-0 ∙ early-0
  ρa-1 : fst ρa 𝟙 ≡ 𝟙
  ρa-1 = cong (fst early) first-1 ∙ early-half
  ρb-0 : fst ρb 𝟘 ≡ 𝟘
  ρb-0 = cong (fst early) (cong (fst late) middle-0 ∙ late-half) ∙ early-0
  ρb-1 : fst ρb 𝟙 ≡ 𝟙
  ρb-1 = cong (fst early) (cong (fst late) middle-1 ∙ late-fiveSixths) ∙ early-half
  ρc-0 : fst ρc 𝟘 ≡ 𝟘
  ρc-0 = cong (fst late) (cong (fst late) last-0 ∙ late-fiveSixths) ∙ late-half
  ρc-1 : fst ρc 𝟙 ≡ 𝟙
  ρc-1 = cong (fst late) (cong (fst late) last-1 ∙ late-1) ∙ late-1

module Laws {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Factorization X public

  concat-assoc : ∀ {x y z w} (p : UCPath x y) (q : UCPath y z) (r : UCPath z w) →
    PathHomotopy (concatPath (concatPath p q) r) (concatPath p (concatPath q r))
  concat-assoc p q r = homotopy-trans
    {p = concatPath (concatPath p q) r}
    {q = concatPath (concatPath p' q') r'}
    {r = concatPath p (concatPath q r)}
    leftStep
    (homotopy-trans
      {p = concatPath (concatPath p' q') r'}
      {q = concatPath p' (concatPath q' r')}
      {r = concatPath p (concatPath q r)}
      commonCurve (homotopy-sym
        {p = concatPath p (concatPath q r)}
        {q = concatPath p' (concatPath q' r')} rightStep))
    where
    p' = reparametrize p ρa ρa-0 ρa-1
    q' = reparametrize q ρb ρb-0 ρb-1
    r' = reparametrize r ρc ρc-0 ρc-1

    hp : PathHomotopy p p'
    hp = reparametrize-homotopy p ρa ρa-0 ρa-1
    hq : PathHomotopy q q'
    hq = reparametrize-homotopy q ρb ρb-0 ρb-1
    hr : PathHomotopy r r'
    hr = reparametrize-homotopy r ρc ρc-0 ρc-1

    leftStep : PathHomotopy (concatPath (concatPath p q) r) (concatPath (concatPath p' q') r')
    leftStep = concat-homotopy
      {p = concatPath p q} {p' = concatPath p' q'} {q = r} {q' = r'}
      (concat-homotopy {p = p} {p' = p'} {q = q} {q' = q'} hp hq) hr

    rightStep : PathHomotopy (concatPath p (concatPath q r)) (concatPath p' (concatPath q' r'))
    rightStep = concat-homotopy
      {p = p} {p' = p'} {q = concatPath q r} {q' = concatPath q' r'}
      hp (concat-homotopy {p = q} {p' = q'} {q = r} {q' = r'} hq hr)

    F : UC[ Interval , X ]
    F = fst (concatPath p (concatPath q r))

    pa : ∀ t → at p' t ≡ fst F (Clocks.at a t)
    pa t = sym (concat-left p (concatPath q r) (fst firstClock t)
      (left-of-half (fst firstClock t) (first≤half t)))
    qb : ∀ t → at q' t ≡ fst F (Clocks.at b t)
    qb t = sym (concat-right p (concatPath q r) (fst middleClock t)
      (right-of-half (fst middleClock t) (half≤middle t)) ∙
      concat-left q r (fst late (fst middleClock t))
        (left-of-half (fst late (fst middleClock t)) (middle-late≤half t)))
    rc : ∀ t → at r' t ≡ fst F (Clocks.at c t)
    rc t = sym (concat-right p (concatPath q r) (fst lastClock t)
      (right-of-half (fst lastClock t) (half≤last t)) ∙
      concat-right q r (fst late (fst lastClock t))
        (right-of-half (fst late (fst lastClock t)) (half≤last-late t)))

    commonCurve : PathHomotopy (concatPath (concatPath p' q') r') (concatPath p' (concatPath q' r'))
    commonCurve = factor-assoc F a b c p' q' r' pa qb rc
