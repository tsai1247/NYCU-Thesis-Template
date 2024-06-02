\begin{code}
------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.

{-# OPTIONS --without-K --safe #-}

module agdaTrans where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_; _on_)
import Data.Nat.Properties as ℕₚ
open import Level using () renaming (zero to ℓ₀)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)
\end{code}