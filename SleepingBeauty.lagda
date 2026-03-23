\title{The Sleeping Beauty Problem}

\begin{document}

\maketitle

\section{Introduction}

The Sleeping Beauty problem is a puzzle in probability theory and epistemology
first discussed by Arnold Zuboff and later popularized by Adam Elga in 2000.

The setup is as follows: Sleeping Beauty is put to sleep on Sunday. A fair coin
is flipped. If the coin lands \textbf{Heads}, Beauty is woken once on Monday,
then the experiment ends. If the coin lands \textbf{Tails}, Beauty is woken on
Monday, put back to sleep with her memory of the waking erased, then woken
again on Tuesday. 

Upon each awakening, Beauty is asked: \emph{What is your credence that the coin
landed Heads?}. She does not get told either the outcome of the coin flip 
or what day it is until she states her credence. 

There are two main positions:

\begin{itemize}
  \item \textbf{Halfers} argue the answer is $\frac{1}{2}$, since the coin is
        fair and no new information is gained upon waking.
  \item \textbf{Thirders} argue the answer is $\frac{1}{3}$, since upon waking
        there are three equally likely situations (Heads/Monday,
        Tails/Monday, Tails/Tuesday), only one of which corresponds to Heads.
\end{itemize}

\section{Formalisation}

\begin{code}
module SleepingBeauty where

open import Data.Rational
open import Data.Integer using (+_)
open import Bayes
open import Data.Product using (∃; _,_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

The halfer credence for Heads:

\begin{code}
data CoinFlip : Set where
  heads : CoinFlip
  tails : CoinFlip

data Day : Set where
  monday  : Day
  tuesday : Day

data Awakening : Set where
  -- An awakening is characterized by the coin result and the day
  awake : CoinFlip → Day → Awakening

-- Not all combinations are valid awakenings
data ValidAwakening : Awakening → Set where
  mon-heads : ValidAwakening (awake heads monday)
  mon-tails : ValidAwakening (awake tails monday)
  tue-tails : ValidAwakening (awake tails tuesday)
  -- Note: (awake heads tuesday) is NOT valid

isValidAwakening : Awakening → Bool
isValidAwakening (awake heads monday)  = true
isValidAwakening (awake tails monday)  = true
isValidAwakening (awake tails tuesday) = true
isValidAwakening (awake heads tuesday) = false

\end{code}

2. Formalize Indistinguishability (The Key Insight)
Following the paper's approach of separating possibility from certainty, the core of Sleeping Beauty is that she cannot distinguish which awakening she's in:


\begin{code}

-- What does "I am awake" tell Beauty?
data Evidence : Set where
  i-am-awake : Evidence

-- Beauty's epistemic state upon awakening
-- She knows she's awake, but not which awakening this is
record EpistemicState : Set where
  field
    -- The set of awakenings compatible with her observations
    possible-awakenings : Awakening → Bool
    -- At least one must be possible
    nonempty : ∃ λ a → T (possible-awakenings a)
    -- Prior over the coin flip: the coin is fair
    coin-prior : CoinFlip → ℚ
    -- Prior probability over days, given evidence (waking up is evidence it's more likely Monday)
    day-prior : Evidence → Day → ℚ

-- Thirder epistemic state: uniform prior over the three valid awakening-moments.
-- Two of the three are Monday, so P(Monday) = 2/3 and P(Tuesday) = 1/3.
BeautyKnowledgeThird : EpistemicState
BeautyKnowledgeThird = record
  { possible-awakenings = isValidAwakening
  ; nonempty             = (awake heads monday) , tt
  ; coin-prior           = λ _ → ½
  ; day-prior            = λ { i-am-awake monday  → (+ 2) / 3
                             ; i-am-awake tuesday → (+ 1) / 3 }
  }

-- Halfer (Lewis) epistemic state: day-prior derived from coin-weighted day probabilities.
-- Monday always occurs (weight 1); Tuesday only with Tails (weight 1/2).
-- Normalised: P(Monday) = 3/4, P(Tuesday) = 1/4.
BeautyKnowledgeHalf : EpistemicState
BeautyKnowledgeHalf = record
  { possible-awakenings = isValidAwakening
  ; nonempty             = (awake heads monday) , tt
  ; coin-prior           = λ _ → ½
  ; day-prior            = λ { i-am-awake monday  → (+ 3) / 4
                             ; i-am-awake tuesday → (+ 1) / 4 }
  }

\end{code}

3. Formalize the Two Interpretations of Probability

Both views agree on the Bayesian update rule: since Heads is impossible on
Tuesday, $P(\text{Heads}) = P(\text{Monday}) \times P(\text{Heads} \mid
\text{Monday})$.  They disagree on the two inputs to this formula.

\begin{code}

-- A belief view captures the conditional probability of Heads given it is Monday.
-- P(Heads) is derived as P(Monday) × P(Heads|Monday) using the day-prior from
-- the EpistemicState, since P(Heads|Tuesday) = 0 (Tuesday only occurs with Tails).
record BeliefView : Set where
  field
    p-heads-given-monday : ℚ

p-heads : EpistemicState → BeliefView → ℚ
p-heads es bv = EpistemicState.day-prior es i-am-awake monday
              * BeliefView.p-heads-given-monday bv

-- Thirder view:
--   P(Heads|Monday) = 1/2  (coin is symmetric; neither outcome biases Monday)
--   P(Heads) = 2/3 × 1/2 = 1/3
thirder-view : BeliefView
thirder-view = record
  { p-heads-given-monday = ½ }

-- Halfer view:
--   P(Heads|Monday) = 2/3  (Monday is more probable under Heads than Tails)
--   P(Heads) = 3/4 × 2/3 = 1/2
halfer-view : BeliefView
halfer-view = record
  { p-heads-given-monday = (+ 2) / 3 }

\end{code}

4. Formalize the "Self-Location" Uncertainty (Novel Contribution)
Following the hanging paper's insight about parametrizing beliefs by "today," you can parametrize by which awakening Beauty is in:

\begin{code}

-- Beliefs parametrized by the actual state of the world
-- (which Beauty doesn't know)
record BeliefSystem : Set₁ where
  field
    -- Given the true state, what does Beauty believe about the coin?
    credence-in-heads : (actual : Awakening) → ValidAwakening actual → ℚ
    
    -- Constraint: beliefs must be consistent across indistinguishable states
    -- If Beauty can't tell states apart, her credence must be the same
    consistency : (a₁ a₂ : Awakening) → (v₁ : ValidAwakening a₁) → (v₂ : ValidAwakening a₂)
                → credence-in-heads a₁ v₁ ≡ credence-in-heads a₂ v₂

\end{code}

5. The Key Theorem: Both Views Are Internally Consistent
Like the hanging paper showing classical propositions can satisfy paradox constraints, you can show both halfer and thirder views are internally consistent:

\begin{code}

-- Both views are consistent: credence is derived from the respective BeliefView
-- via the shared Bayesian update, then held constantly across all awakenings.
thirder-consistent : BeliefSystem
thirder-consistent = record
  { credence-in-heads = λ _ _ → p-heads BeautyKnowledgeThird thirder-view
  ; consistency       = λ _ _ _ _ → refl
  }

halfer-consistent : BeliefSystem
halfer-consistent = record
  { credence-in-heads = λ _ _ → p-heads BeautyKnowledgeHalf halfer-view
  ; consistency       = λ _ _ _ _ → refl
  }

\end{code}

6. Where the Disagreement Lives: Different Priors, Different Posteriors

By Bayes' rule (law of total probability form):
$P(\text{Heads} \mid \text{awake}) = \sum_{d : \text{Day}} P(d \mid \text{awake}) \times P(\text{Heads} \mid d)$
The two views share the same rule but differ in the prior $P(d \mid \text{awake})$,
supplied by \texttt{BeautyKnowledgeThird} and \texttt{BeautyKnowledgeHalf}.

\begin{code}

-- P(Heads | day) from the experiment rules and a BeliefView:
-- Heads is impossible on Tuesday; on Monday it equals p-heads-given-monday.
p-heads-given-day : BeliefView → Day → ℚ
p-heads-given-day bv monday  = BeliefView.p-heads-given-monday bv
p-heads-given-day _  tuesday = 0ℚ

-- Build a BayesSetup over Day for a given epistemic state and belief view:
--   prior      d = P(d | awake)     from the EpistemicState day-prior
--   likelihood d = P(Heads | d)     from the BeliefView
-- normalizer₂ monday tuesday then computes
--   Σ_{d} P(Heads | d) × P(d | awake)  =  P(Heads | awake)
sb-bayes-setup : EpistemicState → BeliefView → Evidence → BayesSetup Day
sb-bayes-setup es bv e = record
  { prior      = EpistemicState.day-prior es e
  ; likelihood = p-heads-given-day bv
  }

-- Applying Bayes with BeautyKnowledgeThird:
-- P(Monday | awake) = 2/3,  P(Heads | Monday) = 1/2
-- P(Heads | awake) = 2/3 × 1/2 + 1/3 × 0 = 1/3
credence-thirder : ℚ
credence-thirder = normalizer₂ monday tuesday
  (sb-bayes-setup BeautyKnowledgeThird thirder-view i-am-awake)

-- Applying Bayes with BeautyKnowledgeHalf:
-- P(Monday | awake) = 3/4,  P(Heads | Monday) = 2/3
-- P(Heads | awake) = 3/4 × 2/3 + 1/4 × 0 = 1/2
credence-halfer : ℚ
credence-halfer = normalizer₂ monday tuesday
  (sb-bayes-setup BeautyKnowledgeHalf halfer-view i-am-awake)

-- Proofs that the Bayesian credences equal the p-heads computed from each view
credence-thirder-correct : credence-thirder ≡ p-heads BeautyKnowledgeThird thirder-view
credence-thirder-correct = refl

credence-halfer-correct : credence-halfer ≡ p-heads BeautyKnowledgeHalf halfer-view
credence-halfer-correct = refl

\end{code}

7. Formalize the Betting Arguments
One way to make the problem concrete is through bets:

\begin{code}

record Bet : Set where
  field
    stake : ℚ
    pays-on : CoinFlip → ℚ

open Bet

-- Expected value depends on how you count!
-- Per-awakening betting (thirder-friendly)
ev-per-awakening : Bet → ℚ
ev-per-awakening b = ((+ 1) / 3 * pays-on b heads) + ((+ 2) / 3 * pays-on b tails)

-- Per-experiment betting (halfer-friendly)  
ev-per-experiment : Bet → ℚ
ev-per-experiment b = (½ * pays-on b heads) + (½ * pays-on b tails)
\end{code}

\section{The Parametric Approach}

In the unexpected hanging formalization, beliefs are parametrized by the actual
execution day: a reasoning function takes \emph{(actual hanging day, today,
query day)} and the constraint \texttt{hangingOnTodayIsReasoningAbout} picks out
which such functions are consistent with the rules of the situation.

We adopt the same structure here. A reasoning function takes the actual coin
result and Beauty's current awakening and returns her credence in heads. The
rules of the Sleeping Beauty situation --- which (coin, awakening) pairs can
actually occur, and that Beauty cannot distinguish between them --- then
characterise the admissible reasoning functions.

\subsection{The rules of the situation}

The valid (coin, awakening) pairs encode exactly what the experimenter knows
that Beauty does not: which awakening is actually occurring.

\begin{code}

data CoinAwakeningValid : CoinFlip → Awakening → Set where
  val-heads-mon : CoinAwakeningValid heads (awake heads monday)
  val-tails-mon : CoinAwakeningValid tails (awake tails monday)
  val-tails-tue : CoinAwakeningValid tails (awake tails tuesday)

\end{code}


\subsection{Source of the disagreement}

The formalization makes the source of the disagreement precise: it lies
entirely in Beauty's \emph{day-prior} --- her probability distribution over
days upon waking, encoded in the \texttt{day-prior} field of her
\texttt{EpistemicState}.  Both views apply the same Bayesian update rule
(\texttt{bayes-rule}), share the same fair coin prior, and agree that
$P(\text{Heads} \mid \text{Tuesday}) = 0$.  The only thing that differs
between \texttt{BeautyKnowledgeThird} and \texttt{BeautyKnowledgeHalf} is
$P(\text{Monday} \mid \text{awake})$:

\begin{center}
\begin{tabular}{lll}
  & $P(\text{Monday} \mid \text{awake})$ & $P(\text{Heads} \mid \text{awake})$ \\
  \hline
  \textbf{Thirder} & $\frac{2}{3}$ & $\frac{2}{3} \times \frac{1}{2} = \frac{1}{3}$ \\
  \textbf{Halfer}  & $\frac{3}{4}$ & $\frac{3}{4} \times \frac{2}{3} = \frac{1}{2}$ \\
\end{tabular}
\end{center}

The familiar thirder slogan --- ``the three awakening-moments are equally
likely, each with probability $\frac{1}{3}$'' --- is therefore not a
primitive assumption but a \emph{derived consequence} of the day-prior.
Given $P(\text{Monday} \mid \text{awake}) = \frac{2}{3}$ and a fair coin,
the two Monday scenarios split that mass equally
($P(\text{Heads/Mon}) = P(\text{Tails/Mon}) = \frac{1}{3}$), and the single
Tuesday scenario inherits the remaining $\frac{1}{3}$.  The real commitment
is to the day-prior, encoded in \texttt{BeautyKnowledgeThird}; the uniform
distribution over awakening-moments is just what that prior looks like once
coin symmetry on Monday is applied.

\end{document}
