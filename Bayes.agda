module Bayes where

open import Data.Rational using (ℚ; _*_; _+_)

-- A Bayesian setup: a prior over hypotheses and a likelihood function.
-- The likelihood is fixed to a particular evidence value:
--   prior      h = P(h)
--   likelihood h = P(evidence | h)
record BayesSetup (H : Set) : Set where
  field
    prior      : H → ℚ
    likelihood : H → ℚ

-- Joint probability: P(h, evidence) = P(evidence | h) × P(h)
joint : {H : Set} → BayesSetup H → H → ℚ
joint b h = BayesSetup.likelihood b h * BayesSetup.prior b h

-- Normalizing constant for a two-hypothesis problem:
-- P(evidence) = P(evidence | h₁) × P(h₁) + P(evidence | h₂) × P(h₂)
normalizer₂ : {H : Set} → H → H → BayesSetup H → ℚ
normalizer₂ h₁ h₂ b = joint b h₁ + joint b h₂

-- Bayes' theorem:
-- P(h | evidence) = joint b h / normalizer₂ h₁ h₂ b
--
-- Expressed without division as the proportionality:
--   P(h | evidence) × P(evidence) = P(evidence | h) × P(h)
-- i.e., posterior is proportional to likelihood × prior.
