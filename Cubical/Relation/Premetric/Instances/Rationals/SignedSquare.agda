module Cubical.Relation.Premetric.Instances.Rationals.SignedSquare where

-- The instance itself is defined with the ordinary rational premetric so
-- existing users of Instances.Rationals keep their API.  The substantial
-- comparison proofs are grouped below this namespace.

open import Cubical.Relation.Premetric.Instances.Rationals public
  using (signedSquareℚ; signedSquareℚ≡·abs;
         signedSquareℚ-strictMono; signedSquareℚ-injective;
         ℚSignedSquarePremetricSpace)

import Cubical.Relation.Premetric.Instances.Rationals.SignedSquare.Completion
  as CompletionDefinition
import Cubical.Relation.Premetric.Instances.Rationals.SignedSquare.Identity
  as IdentityDefinition

module Completion = CompletionDefinition
module Identity = IdentityDefinition
