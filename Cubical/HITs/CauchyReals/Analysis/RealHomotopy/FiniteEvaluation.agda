module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteEvaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using (Dichotomyℝ')
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric using (ℝPremetricSpace)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Stitching
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

-- Compare two supplied finite pastes through an arbitrary evaluation
-- function. No global continuity of evaluation is assumed: jointly UC
-- branches on the right are explicit input to the theorem.
module FiniteEvaluation {ℓA ℓA' ℓX ℓX' ℓB ℓB' ℓY ℓY'}
  (A : PremetricSpace ℓA ℓA') (X : PremetricSpace ℓX ℓX')
  (B : PremetricSpace ℓB ℓB')
  (Y : PremetricSpace ℓY ℓY') (evaluate : fst A → fst Y → fst X) where

  module P = FinitePaste A B
  module Q = FinitePaste X (PremetricProduct B Y)

  Agrees : P.Branch → Q.Branch → Type (ℓ-max ℓB (ℓ-max ℓX ℓY))
  Agrees f g = (t : ℝ) (b : fst B) (y : fst Y) →
    evaluate (fst f (t , b)) y ≡ fst g (t , (b , y))

  Branchwise : (n : ℕ) → P.Chain n → Q.Chain n → Type (ℓ-max ℓB (ℓ-max ℓX ℓY))
  Branchwise zero c d = Agrees c d
  Branchwise (suc n) (c , f , cf) (d , g , dg) = Branchwise n c d × Agrees f g

  paste-agrees : (n : ℕ) (c : P.Chain n) (d : Q.Chain n) →
    Branchwise n c d → Agrees (P.paste n c) (Q.paste n d)
  paste-agrees zero c d same = same
  paste-agrees (suc n) (c , f , cf) (d , g , dg) (previous , same) t b y =
    PT.rec (PremetricStr.isSetM (snd X) _ _) (λ where
      (inl left) → cong (λ a → evaluate a y) (S.stitched-left t b left) ∙
        paste-agrees n c d previous t b y ∙ sym (T.stitched-left t (b , y) left)
      (inr right) → cong (λ a → evaluate a y) (S.stitched-right t b right) ∙
        same t b y ∙ sym (T.stitched-right t (b , y) right))
      (Dichotomyℝ' (rat (cut n)) t (rat (upper n)) (overlap-positive n))
    where
    module S = Stitch A B (cut n) (P.paste n c) f
      (λ t y lo hi → P.last-after n c t y lo ∙ cf t y lo hi)
    module T = Stitch X (PremetricProduct B Y) (cut n) (Q.paste n d) g
      (λ t y lo hi → Q.last-after n d t y lo ∙ dg t y lo hi)

  evaluatedPasteUC : (n : ℕ) (c : P.Chain n) (d : Q.Chain n) → Branchwise n c d →
    UC[ PremetricProduct ℝPremetricSpace (PremetricProduct B Y) , X ]
  fst (evaluatedPasteUC n c d same) (t , (b , y)) = evaluate (fst (P.paste n c) (t , b)) y
  snd (evaluatedPasteUC n c d same) = subst
    (λ f → isUniformlyContinuous
      (snd (PremetricProduct ℝPremetricSpace (PremetricProduct B Y))) f (snd X))
    (funExt (λ (t , (b , y)) → sym (paste-agrees n c d same t b y))) (snd (Q.paste n d))

  -- Jointness on each of the FINITELY many supplied branches suffices.
  -- Construct the second chain and every overlap equation internally.
  JointBranch : P.Branch → Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max (ℓ-max ℓY ℓY') ℓX'))
  JointBranch f = isUniformlyContinuous
    (snd (PremetricProduct ℝPremetricSpace (PremetricProduct B Y)))
    (λ (t , (b , y)) → evaluate (fst f (t , b)) y) (snd X)

  JointBranches : (n : ℕ) → P.Chain n →
    Type (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max (ℓ-max ℓY ℓY') ℓX'))
  JointBranches zero f = JointBranch f
  JointBranches (suc n) (c , f , cf) = JointBranches n c × JointBranch f

  private
    jointBranch : (f : P.Branch) → JointBranch f → Q.Branch
    fst (jointBranch f joint) (t , (b , y)) = evaluate (fst f (t , b)) y
    snd (jointBranch f joint) = joint

  evaluatedChain : (n : ℕ) (c : P.Chain n) → JointBranches n c → Q.Chain n
  last-agrees : (n : ℕ) (c : P.Chain n) (joint : JointBranches n c) →
    Agrees (P.last n c) (Q.last n (evaluatedChain n c joint))
  evaluatedChain zero f joint = jointBranch f joint
  evaluatedChain (suc n) (c , f , cf) (previous , joint) =
    evaluatedChain n c previous , jointBranch f joint ,
    λ t (b , y) lo hi → sym (last-agrees n c previous t b y) ∙
      cong (λ a → evaluate a y) (cf t b lo hi)
  last-agrees zero c joint t b y = refl
  last-agrees (suc n) (c , f , cf) (previous , joint) t b y = refl

  chain-agrees : (n : ℕ) (c : P.Chain n) (joint : JointBranches n c) →
    Branchwise n c (evaluatedChain n c joint)
  chain-agrees zero c joint t b y = refl
  chain-agrees (suc n) (c , f , cf) (previous , joint) =
    chain-agrees n c previous , λ t b y → refl

  jointPaste : (n : ℕ) (c : P.Chain n) → JointBranches n c → JointBranch (P.paste n c)
  jointPaste n c joint =
    snd (evaluatedPasteUC n c (evaluatedChain n c joint) (chain-agrees n c joint))
