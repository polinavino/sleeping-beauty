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

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)

\end{code}

\subsection{Sample space}

The sample space $\Omega$ for the Sleeping Beauty problem is the set of all
\emph{(coin outcome, day)} pairs that can arise during the experiment.

\begin{code}

data CoinFlip : Set where
  heads : CoinFlip
  tails : CoinFlip

data Day : Set where
  monday  : Day
  tuesday : Day

Ω : Set
Ω = CoinFlip × Day

\end{code}

\subsection{Events as predicates}

Following \texttt{CategoricalCrypto.ProbabilisticLogic}, events are
predicates $\Omega \to \mathsf{Set}$.

\begin{code}

-- Set-theoretic operations on events
_∩_ _∪_ : (Ω → Set) → (Ω → Set) → Ω → Set
(X ∩ Y) ω = X ω × Y ω
(X ∪ Y) ω = X ω ⊎ Y ω

∅ U : Ω → Set
∅ _ = ⊥
U _ = ⊤

disjoint : (X Y : Ω → Set) → Set
disjoint X Y = ∀ {ω} → X ω → Y ω → ⊥

-- A binary partition of Ω
record Partition (X Y : Ω → Set) : Set where
  field
    disj   : disjoint X Y
    covers : ∀ ω → X ω ⊎ Y ω

-- The four basic SB events
IsTails IsHeads IsMonday IsTuesday : Ω → Set
IsTails   (c , _) = c ≡ tails
IsHeads   (c , _) = c ≡ heads
IsMonday  (_ , d) = d ≡ monday
IsTuesday (_ , d) = d ≡ tuesday

\end{code}

\subsection{Abstract probability frame}

We work parametrically over an \emph{abstract probability frame}, which
captures the axioms of the \texttt{Abstract} record from
\texttt{CategoricalCrypto.ProbabilisticLogic} that we actually need.
The two load-bearing axioms are the conditional-probability identity and
finite additivity for disjoint events.

\begin{code}

-- Abstract probability type — we leave it abstract so the module can be
-- instantiated with ℚ or any other probability semiring.
record ProbFrame : Set₁ where
  field
    Prob   : Set
    _⊕_    : Prob → Prob → Prob   -- addition of probabilities
    _⊗_    : Prob → Prob → Prob   -- multiplication of probabilities
    0p 1p ½p : Prob

    -- Distributions over Ω
    Distr  : Set
    _∙_    : Distr → (Ω → Set) → Prob

    -- Conditional distribution P ∣ X, viewed back on Ω
    _∣_    : Distr → (X : Ω → Set) → Distr

    -- Axioms (from Abstract in ProbabilisticLogic.agda)
    cond-prob      : ∀ {P : Distr} {X Y : Ω → Set}
                   → (P ∙ X) ⊗ ((P ∣ X) ∙ Y)  ≡  P ∙ (X ∩ Y)

    disjoint-add   : ∀ {P : Distr} {X Y : Ω → Set}
                   → disjoint X Y
                   → (P ∙ X) ⊕ (P ∙ Y)  ≡  P ∙ (X ∪ Y)

    -- Distributions respect extensional equality of events
    ∙-cong         : ∀ {P : Distr} {X Y : Ω → Set}
                   → (∀ ω → X ω → Y ω) → (∀ ω → Y ω → X ω)
                   → P ∙ X ≡ P ∙ Y

    -- Rational arithmetic laws (hold when Prob = ℚ)
    mul-1p     : ∀ (x : Prob) → x ⊗ 1p ≡ x
    ½-cancel   : ∀ {x y : Prob} → x ⊗ ½p ≡ y ⊗ ½p → x ≡ y
    ½-double   : ∀ (x : Prob) → ((x ⊗ ½p) ⊕ (x ⊗ ½p)) ≡ x
    ⊕-cancel-r : ∀ {x y z : Prob} → (x ⊕ z) ≡ (y ⊕ z) → x ≡ y

\end{code}

\subsection{Chapman–Kolmogorov / law of total probability}

For a binary partition $\{X, Y\}$ of $\Omega$ the \emph{law of total
probability} reads
\[
  P(Z) \;=\; P(X)\cdot P(Z\mid X) \;+\; P(Y)\cdot P(Z\mid Y).
\]
In the abstract frame this is a consequence of \texttt{cond-prob} and
\texttt{disjoint-add}; it instantiates the Chapman–Kolmogorov identity for
Kleisli composition in the probability monad (see nLab: \emph{monads of
probability, measures, and valuations}).

\begin{code}

module ChapmanKolmogorov (F : ProbFrame) where
  open ProbFrame F

  -- The Chapman–Kolmogorov law of total probability for a binary partition.
  --
  --   P ∙ Z  =  (P ∙ X) ⊗ ((P ∣ X) ∙ Z)  ⊕  (P ∙ Y) ⊗ ((P ∣ Y) ∙ Z)
  --
  ck : ∀ (P : Distr) {X Y : Ω → Set} (Z : Ω → Set)
     → Partition X Y
     → (((P ∙ X) ⊗ ((P ∣ X) ∙ Z)) ⊕ ((P ∙ Y) ⊗ ((P ∣ Y) ∙ Z))) ≡ (P ∙ Z)
  ck P {X} {Y} Z part =
    trans (cong₂ _⊕_ cond-prob cond-prob)
    (trans (disjoint-add dXZ-YZ)
           (∙-cong {P = P} {X = (X ∩ Z) ∪ (Y ∩ Z)} {Y = Z} bwd fwd))
    where
      dXZ-YZ : disjoint (X ∩ Z) (Y ∩ Z)
      dXZ-YZ (xω , _) (yω , _) = Partition.disj part xω yω
      bwd : ∀ ω → ((X ∩ Z) ∪ (Y ∩ Z)) ω → Z ω
      bwd ω (inj₁ (_ , zω)) = zω
      bwd ω (inj₂ (_ , zω)) = zω
      fwd : ∀ ω → Z ω → ((X ∩ Z) ∪ (Y ∩ Z)) ω
      fwd ω zω with Partition.covers part ω
      ... | inj₁ xω = inj₁ (xω , zω)
      ... | inj₂ yω = inj₂ (yω , zω)

\end{code}

\subsection{Application to Sleeping Beauty}

We now instantiate \texttt{ck} for the two Chapman–Kolmogorov identities
that govern the Sleeping Beauty problem.

\begin{code}

-- Halfer priors: the coin is fair (P(Heads) = 1/2 as a marginal),
-- plus the uncontroversial structural facts about the experiment.
record HalferPriors (F : ProbFrame) (wakingMeasure : ProbFrame.Distr F) : Set where
  open ProbFrame F
  field
    -- Fair coin: the marginal probability of heads is 1/2.
    --     P(Heads) = 1/2
    heads-prior               : wakingMeasure ∙ IsHeads ≡ ½p

    -- (2) SB is never woken on Tuesday when the coin landed Heads.
    --     P(Heads | Tuesday) = 0
    heads-given-tuesday : (wakingMeasure ∣ IsTuesday) ∙ IsHeads  ≡ 0p

    -- (3) If the coin landed Heads, SB is only woken on Monday.
    --     P(Monday | Heads) = 1
    monday-given-heads  : (wakingMeasure ∣ IsHeads)   ∙ IsMonday ≡ 1p

    -- (4) Self-locating uncertainty: if Tails, SB is equally likely to be
    --     woken on Monday or Tuesday.
    --     P(Monday | Tails) = 1/2
    monday-given-tails  : (wakingMeasure ∣ IsTails)   ∙ IsMonday ≡ ½p

-- Thirder priors: CoinFlip and Day are sampled independently —
-- Monday carries no information about the coin outcome.
record ThirderPriors (F : ProbFrame) (wakingMeasure : ProbFrame.Distr F) : Set where
  open ProbFrame F
  field
    -- (1) Independence: conditioning on Monday leaves the coin 50/50.
    --     P(Tails | Monday) = 1/2
    tails-given-monday  : (wakingMeasure ∣ IsMonday)  ∙ IsTails  ≡ ½p

    -- (2) SB is never woken on Tuesday when the coin landed Heads.
    --     P(Heads | Tuesday) = 0
    heads-given-tuesday : (wakingMeasure ∣ IsTuesday) ∙ IsHeads  ≡ 0p

    -- (3) If the coin landed Heads, SB is only woken on Monday.
    --     P(Monday | Heads) = 1
    monday-given-heads  : (wakingMeasure ∣ IsHeads)   ∙ IsMonday ≡ 1p

    -- (4) Self-locating uncertainty: if Tails, SB is equally likely to be
    --     woken on Monday or Tuesday.
    --     P(Monday | Tails) = 1/2
    monday-given-tails  : (wakingMeasure ∣ IsTails)   ∙ IsMonday ≡ ½p

module SBApplication
    (F             : ProbFrame)
    (wakingMeasure : ProbFrame.Distr F)
    (priors        : ThirderPriors F wakingMeasure) where
  open ProbFrame F
  open ChapmanKolmogorov F
  open ThirderPriors priors

  -- The partition of Ω by day
  dayPartition : Partition IsMonday IsTuesday
  dayPartition = record
    { disj   = λ { refl () }
    ; covers = λ { (c , monday)  → inj₁ refl
                 ; (c , tuesday) → inj₂ refl }
    }

  -- The partition of Ω by coin outcome
  coinPartition : Partition IsHeads IsTails
  coinPartition = record
    { disj   = λ { refl () }
    ; covers = λ { (heads , d) → inj₁ refl
                 ; (tails , d) → inj₂ refl }
    }

  -- P(Heads) = P(Monday) × P(Heads | Monday) + P(Tuesday) × P(Heads | Tuesday)
  formula-1 : (((wakingMeasure ∙ IsMonday) ⊗ ((wakingMeasure ∣ IsMonday) ∙ IsHeads))
             ⊕ ((wakingMeasure ∙ IsTuesday) ⊗ ((wakingMeasure ∣ IsTuesday) ∙ IsHeads)))
             ≡ (wakingMeasure ∙ IsHeads)
  formula-1 = ck wakingMeasure IsHeads dayPartition

  -- P(Monday) = P(Heads) × P(Monday | Heads) + P(Tails) × P(Monday | Tails)
  formula-2 : (((wakingMeasure ∙ IsHeads) ⊗ ((wakingMeasure ∣ IsHeads) ∙ IsMonday))
             ⊕ ((wakingMeasure ∙ IsTails) ⊗ ((wakingMeasure ∣ IsTails) ∙ IsMonday)))
             ≡ (wakingMeasure ∙ IsMonday)
  formula-2 = ck wakingMeasure IsMonday coinPartition

  -- The thirder conclusion: P(Tails) = 2 × P(Heads).
  --
  -- Proof sketch:
  --  (a) cond-prob applied twice + priors 1 and 4 gives
  --      P(Monday) × ½ = P(Monday ∩ Tails) = P(Tails) × ½,
  --      so P(Monday) = P(Tails).
  --  (b) formula-2 + priors 3 and 4 gives P(Heads) + P(Tails) × ½ = P(Monday).
  --  (c) Substituting (a) into (b): P(Heads) + P(Tails) × ½ = P(Tails),
  --      so P(Heads) = P(Tails) × ½, i.e. P(Tails) = P(Heads) + P(Heads).
  tails-twice-heads : (wakingMeasure ∙ IsTails) ≡ ((wakingMeasure ∙ IsHeads) ⊕ (wakingMeasure ∙ IsHeads))
  tails-twice-heads =
    let
      -- (a1) P(Monday) × ½ = P(Monday ∩ Tails)  [cond-prob + prior 1]
      monday-tails : (wakingMeasure ∙ IsMonday) ⊗ ½p ≡ wakingMeasure ∙ (IsMonday ∩ IsTails)
      monday-tails = trans (sym (cong ((wakingMeasure ∙ IsMonday) ⊗_) tails-given-monday))
                           cond-prob

      -- (a2) P(Tails) × ½ = P(Tails ∩ Monday)  [cond-prob + prior 4]
      tails-monday : (wakingMeasure ∙ IsTails) ⊗ ½p ≡ wakingMeasure ∙ (IsTails ∩ IsMonday)
      tails-monday = trans (sym (cong ((wakingMeasure ∙ IsTails) ⊗_) monday-given-tails))
                           cond-prob

      -- P(Monday ∩ Tails) = P(Tails ∩ Monday)  [∩ is symmetric]
      ∩-swap : wakingMeasure ∙ (IsMonday ∩ IsTails) ≡ wakingMeasure ∙ (IsTails ∩ IsMonday)
      ∩-swap = ∙-cong (λ ω (m , t) → t , m) (λ ω (t , m) → m , t)

      -- P(Monday) × ½ = P(Tails) × ½
      eq½ : (wakingMeasure ∙ IsMonday) ⊗ ½p ≡ (wakingMeasure ∙ IsTails) ⊗ ½p
      eq½ = trans monday-tails (trans ∩-swap (sym tails-monday))

      -- (a) P(Monday) = P(Tails)
      M≡T : wakingMeasure ∙ IsMonday ≡ wakingMeasure ∙ IsTails
      M≡T = ½-cancel eq½

      -- (b) Simplify formula-2 using priors 3 and 4:
      --     P(Heads) + P(Tails) × ½ = P(Monday)
      from-f2 : (wakingMeasure ∙ IsHeads) ⊕ ((wakingMeasure ∙ IsTails) ⊗ ½p) ≡ wakingMeasure ∙ IsMonday
      from-f2 = trans
        (sym (cong₂ _⊕_
          (trans (cong ((wakingMeasure ∙ IsHeads) ⊗_) monday-given-heads) (mul-1p _))
          (cong  ((wakingMeasure ∙ IsTails) ⊗_)       monday-given-tails)))
        formula-2

      -- (c) P(Heads) + P(Tails) × ½ = P(Tails)
      H⊕T½≡T : (wakingMeasure ∙ IsHeads) ⊕ ((wakingMeasure ∙ IsTails) ⊗ ½p) ≡ wakingMeasure ∙ IsTails
      H⊕T½≡T = trans from-f2 M≡T

      -- P(Heads) = P(Tails) × ½
      H≡T½ : wakingMeasure ∙ IsHeads ≡ (wakingMeasure ∙ IsTails) ⊗ ½p
      H≡T½ = ⊕-cancel-r (trans H⊕T½≡T (sym (½-double _)))

    in trans (sym (½-double (wakingMeasure ∙ IsTails)))
             (cong₂ _⊕_ (sym H≡T½) (sym H≡T½))

\end{code}

\subsection{What the two protocols are counting}

The halfer and thirder positions are not merely different answers to the same question: they
reflect different choices of \emph{what} the probability measure $\mu$ is defined over.
The halfer treats each \emph{experiment run} as a single unit of probability mass.
Because the coin is fair, exactly half of all runs land Heads, so the marginal weight of
Heads waking occasions is $\frac{1}{2}$.
Tails runs are weighted the same as Heads runs, but each Tails run produces \emph{two}
waking occasions; the measure is therefore concentrated on runs, not wakings.

The thirder, by contrast, assigns equal weight to each \emph{waking occasion}.
Under this accounting there are three equally-possible situations
(Heads/Monday, Tails/Monday, Tails/Tuesday), so each carries weight $\frac{1}{3}$.
Conditioning on Monday still leaves the coin 50/50 --- that is exactly the prior
\texttt{tails-given-monday} --- because Monday is equally likely under both outcomes.

Formally, the disagreement surfaces as a contradiction: no single distribution
$\mu$ can satisfy \texttt{HalferPriors} and \texttt{ThirderPriors} simultaneously.
The halfer's constraint \texttt{heads-prior} pins the marginal $\mu({\rm Heads}) = \tfrac{1}{2}$,
whereas \texttt{tails-twice-heads} derived from the thirder's constraint forces
$\mu({\rm Tails}) = 2\,\mu({\rm Heads})$; together with normalization these two claims
are inconsistent.
The two records therefore do not describe competing beliefs about the same probability
space --- they describe \emph{different probability spaces} built from the same sample
space $\Omega$, one weighted by runs and one weighted by wakings.

\end{document}
