module Cubical.Relation.Premetric.Completion.Rationals.PointwiseContinuousExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Base
  as CompletionDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as CompletionPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Lift.PointwiseContinuousExtension
  as PointwiseExtensionDefinition

module R = CompletionDefinition ℚPremetricSpace
module RP = CompletionPropertiesDefinition ℚPremetricSpace
module E = PointwiseExtensionDefinition ℚPremetricSpace ℚPremetricSpace

private
  module PR = PremetricStr (RP.ℭPremetricSpace .snd)

open PositiveRationals
open PositiveHalvesℚ


-- A genuine, though elementary, rational-to-real example requiring no
-- previously lifted operation: the dense rational embedding.  Its germ at a
-- completed input x visibly tends to x itself.

rationalIdentity : ℚ → R.ℭ
rationalIdentity = R.ι


rationalIdentity-tends : ∀ x →
  E.TendsToAt rationalIdentity x x
rationalIdentity-tends x ε =
  ∣ (ε /2₊) , (λ q ιq∼x →
      PR.isMonotone≈< (R.ι q) x (ε /2₊) ε
        (/2₊<id ε) ιq∼x)
  ∣₁


rationalIdentity-everywhereConvergent :
  E.IsEverywhereConvergent rationalIdentity
rationalIdentity-everywhereConvergent x =
  ∣ x , rationalIdentity-tends x ∣₁


liftRationalIdentity : R.ℭ → R.ℭ
liftRationalIdentity =
  E.liftEverywhereConvergent rationalIdentity
    rationalIdentity-everywhereConvergent


liftRationalIdentity-isContinuous :
  isContinuous
    (RP.ℭPremetricSpace .snd) liftRationalIdentity
    (RP.ℭPremetricSpace .snd)
liftRationalIdentity-isContinuous =
  E.liftEverywhereConvergent-isContinuous rationalIdentity
    rationalIdentity-everywhereConvergent


liftRationalIdentity-ι : ∀ q →
  liftRationalIdentity (R.ι q) ≡ R.ι q
liftRationalIdentity-ι =
  E.liftEverywhereConvergent-ι rationalIdentity
    rationalIdentity-everywhereConvergent


liftRationalIdentity≡id : liftRationalIdentity ≡ idfun R.ℭ
liftRationalIdentity≡id = funExt λ x →
  E.tendsToAt-unique x (liftRationalIdentity x) x
    (E.liftEverywhereConvergent-tends rationalIdentity
      rationalIdentity-everywhereConvergent x)
    (rationalIdentity-tends x)
