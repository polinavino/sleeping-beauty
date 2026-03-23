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
landed Heads?}

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

-- Beauty's epistemic state upon awakening
-- She knows she's awake, but not which awakening this is
record EpistemicState : Set where
  field
    -- The set of awakenings compatible with her observations
    possible-awakenings : Awakening → Bool
    -- At least one must be possible
    nonempty : ∃ λ a → T (possible-awakenings a)

-- Upon awakening, all three valid awakenings are indistinguishable
BeautyKnowledge : EpistemicState
BeautyKnowledge = record
  { possible-awakenings = isValidAwakening
  ; nonempty = (awake heads monday) , tt
  }

\end{code}

3. Formalize the Two Interpretations of Probability
This is where it gets interesting. The halfer/thirder debate stems from different interpretations of what probability means here:

\begin{code}

-- Approach 1: Probability over COIN FLIPS (Halfer view)
-- There's one coin flip, two outcomes, fair coin
data CoinOutcome : Set where
  the-flip : CoinFlip → CoinOutcome

halfer-probability : CoinFlip → ℚ
halfer-probability heads = ½
halfer-probability tails = ½

-- Approach 2: Probability over AWAKENING-MOMENTS (Thirder view)
-- There are three possible awakening-moments, weighted equally
thirder-probability : ∀ (a : Awakening) → ValidAwakening a → ℚ
thirder-probability (awake heads monday) _ = (+ 1) / 3
thirder-probability (awake tails monday) _ = (+ 1) / 3
thirder-probability (awake tails tuesday) _ = (+ 1) / 3

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

-- Thirder view is consistent
thirder-consistent : BeliefSystem
thirder-consistent = record
  { credence-in-heads = λ _ _ → (+ 1) / 3
  ; consistency = λ _ _ _ _ → refl
  }

-- Halfer view requires a different formalization...
-- The halfer argues Beauty learns nothing upon awakening,
-- so her credence stays at the prior: ½
halfer-consistent : BeliefSystem
halfer-consistent = record
  { credence-in-heads = λ _ _ → ½
  ; consistency = λ _ _ _ _ → refl
  }

\end{code}

6. Where the Disagreement Lives: Formalizing the Update Rule
The real insight (paralleling the paper's "two-possible" vs "one-possible" distinction) is formalizing what counts as evidence:

\begin{code}
-- What does "I am awake" tell Beauty?
data Evidence : Set where
  i-am-awake : Evidence

-- Thirder interpretation: "I am awake" selects an awakening-moment
-- from the space of all possible awakening-moments
thirder-sample-space : Evidence → List Awakening
thirder-sample-space i-am-awake = 
  awake heads monday ∷ awake tails monday ∷ awake tails tuesday ∷ []

-- Halfer interpretation: "I am awake" was guaranteed to happen
-- regardless of the coin flip, so it's not evidence about the coin
halfer-evidence-value : Evidence → CoinFlip → ℚ
halfer-evidence-value i-am-awake heads = 1ℚ  -- P(awake | heads) = 1
halfer-evidence-value i-am-awake tails = 1ℚ  -- P(awake | tails) = 1
-- By Bayes: P(heads | awake) = P(awake|heads)P(heads) / P(awake) = ½

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

\subsection{Admissible reasoning functions}

\begin{code}

ReasoningFunc : Set
ReasoningFunc = CoinFlip → Awakening → ℚ

record ReasoningFuncOk (rf : ReasoningFunc) : Set where
  field
    indistinguishable : ∀ c₁ c₂ a₁ a₂
                        → CoinAwakeningValid c₁ a₁
                        → CoinAwakeningValid c₂ a₂
                        → rf c₁ a₁ ≡ rf c₂ a₂

\end{code}

\subsection{Both views are admissible}

The halfer and thirder reasoning functions both satisfy the constraint.  The
rules of the situation underdetermine the credence: any constant function on
valid pairs is admissible, so the disagreement between halfers and thirders
cannot be resolved by the situation description alone.

\begin{code}

halfer-rf : ReasoningFunc
halfer-rf _ _ = ½

halfer-rf-ok : ReasoningFuncOk halfer-rf
halfer-rf-ok = record
  { indistinguishable = λ _ _ _ _ _ _ → refl }

thirder-rf : ReasoningFunc
thirder-rf _ _ = (+ 1) / 3

thirder-rf-ok : ReasoningFuncOk thirder-rf
thirder-rf-ok = record
  { indistinguishable = λ _ _ _ _ _ _ → refl }

\end{code}

\subsection{The rules force a constant credence}

Any admissible reasoning function must assign the same credence at every valid
scenario.  The halfer--thirder debate is therefore a debate about which constant
to choose, not about internal consistency: both sides satisfy every constraint
imposed by the situation.

\begin{code}

rf-constant : ∀ (rf : ReasoningFunc) → ReasoningFuncOk rf
              → ∀ c₁ c₂ a₁ a₂
              → CoinAwakeningValid c₁ a₁
              → CoinAwakeningValid c₂ a₂
              → rf c₁ a₁ ≡ rf c₂ a₂
rf-constant rf ok = ReasoningFuncOk.indistinguishable ok

\end{code}

\subsection{Source of the disagreement}

The disagreement between halfers and thirders is not really about the coin ---
it is about what the sample space is. The halfer's core claim is that upon
waking, Beauty learns nothing she did not already know. She knew before the
experiment that she would wake up at least once no matter what the coin showed,
so \emph{``I am awake''} carries no evidential weight about the coin. Her prior
was $\frac{1}{2}$ (fair coin), and nothing has updated it. The natural sample
space is therefore the coin flip itself: one event, two outcomes, probability
$\frac{1}{2}$ each. The number of awakenings is irrelevant because Beauty cannot
count them --- her memory is erased between them, so the tails scenario does not
get to ``vote twice.''

The thirder rejects this framing. Beauty should reason about \emph{which
awakening-moment she is currently in}, not about the coin in isolation. The
sample space is the set of (coin, day) pairs --- three equally likely moments
--- and $P(\text{Heads}) = \frac{1}{3}$ because only one of those three moments
corresponds to Heads.

\begin{center}
\begin{tabular}{ll}
  \textbf{Halfer}  & sample space $= \{\text{Heads},\, \text{Tails}\}$ \\
  \textbf{Thirder} & sample space $= \{\text{Heads/Mon},\, \text{Tails/Mon},\, \text{Tails/Tue}\}$
\end{tabular}
\end{center}

A reasoning function maps the actual coin and current awakening to a credence.
It is admissible when it respects indistinguishability: because Beauty wakes
with no memory and the same subjective experience in every valid scenario, her
credence must be identical across all valid (coin, awakening) pairs.

\end{document}
