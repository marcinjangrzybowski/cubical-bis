module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals where

-- Results that genuinely use rational absolute value, order, or the
-- cofinality of natural radii.  All completion and general lifting machinery
-- remains in the generic Sequential modules.

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.ClosedBalls
  as ClosedBallsDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous
  as CauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Examples
  as ExamplesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous
  as LocalLiftingDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Lift.MapsCauchySequences
  as MapsCauchySequencesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.NaturalClosedBalls
  as NaturalClosedBallsDefinition

module ClosedBalls = ClosedBallsDefinition
module CauchyContinuous = CauchyContinuousDefinition
module Examples = ExamplesDefinition
module LocalLifting = LocalLiftingDefinition
module MapsCauchySequences = MapsCauchySequencesDefinition
module NaturalClosedBalls = NaturalClosedBallsDefinition
