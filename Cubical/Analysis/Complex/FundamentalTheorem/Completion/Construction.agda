open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Construction
  (M : PremetricSpace ℓ-zero ℓ-zero) (n : ℕ) where

-- This constructs all fields of the catalogue's MatchingCompletion.
-- The sequential HIT is applied to a separated finite matching space,
-- never to an assumed sequence of rational approximations of native roots.

open import Cubical.Foundations.Equiv using (propBiimpl→Equiv; equivFun; invEq)
open import Cubical.Data.Vec using (Vec)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion
import Cubical.Analysis.Complex.FundamentalTheorem.Completion.SeparatedMatching as Separated
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base as Sequential
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties as Properties
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular as Comparison
import Cubical.Analysis.Completion.Completeness as Completeness

module Q = Separated M n
module S = Sequential Q.configurationSpace
module P = Properties Q.configurationSpace
private
  module C = Comparison Q.configurationSpace
  module Complete = Completeness Q.configurationSpace
  module Base = PremetricStr (snd M)

finiteMatchingCompletion : MatchingCompletion (fst M) Base._≈[_]_ n
MatchingCompletion.space finiteMatchingCompletion = P.ℭ̂ₛPremetricSpace
MatchingCompletion.insert finiteMatchingCompletion xs = S.ι (Q.insert xs)
MatchingCompletion.insertionIsometry finiteMatchingCompletion xs ys ε =
  propBiimpl→Equiv (S.isProp∼ _ ε _) PT.isPropPropTrunc
    (λ close → equivFun (Q.insertion-closeness xs ys ε)
      (C.ι-reflects∼ (Q.insert xs) (Q.insert ys) ε close))
    (λ close → S.ι-ι (Q.insert xs) (Q.insert ys) ε
      (invEq (Q.insertion-closeness xs ys ε) close))
MatchingCompletion.dense finiteMatchingCompletion x ε =
  PT.rec PT.isPropPropTrunc
    (λ { (q , close) → PT.map
      (λ { (xs , same) → xs , subst (λ a → S.ι a S.∼̂ₛ[ ε ] x) (sym same) close })
      (SQ.[]surjective q) })
    (P.∃approx x ε)
MatchingCompletion.complete finiteMatchingCompletion = Complete.isCompleteSequential
MatchingCompletion.sequentiallyComplete finiteMatchingCompletion x witness =
  S.lim x witness , P.lim-isLimitSeq x witness
