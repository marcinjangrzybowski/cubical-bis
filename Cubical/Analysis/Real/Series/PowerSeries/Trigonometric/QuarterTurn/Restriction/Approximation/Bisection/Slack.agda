module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Slack where

-- Compatibility names; the order estimates are shared with other inverse constructions.
open import Cubical.Analysis.Real.Order.Strict.Slack public
  using ()
  renaming
    ( positiveSlack to sineQuarter-positiveSlack
    ; rightSlack to sineQuarter-rightSlack
    ; leftSlack to sineQuarter-leftSlack
    ; slackBand to sineQuarter-slackBand
    )
