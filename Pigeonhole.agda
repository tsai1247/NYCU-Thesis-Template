module Pigeonhole where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

caseAnalysis : ∀ n x → (f : ℕ → ℕ)
              → (∃[ m ] (m < n × f m ≡ x)) ⊎ (∄[ m ] (m < n × f m ≡ x))
caseAnalysis 0 x f = inj₂ (λ {(_ , () , _)})
caseAnalysis (suc n) x f with caseAnalysis n x f
caseAnalysis (suc n) x f  | inj₁ (m , m<n , fm≡x) = inj₁ (m , ≤-trans m<n (n≤1+n n) , fm≡x)
caseAnalysis (suc n) x f  | inj₂ ¬exists with f n ≟ x
... | yes fn≡x = inj₁ (n , ≤-refl , fn≡x)
... | no ¬fn≡x = inj₂ lem
  where
    lem : ∄[ m ] (m < suc n × f m ≡ x)
    lem (m , m<n+1 , fm≡x) with m≤n⇒m<n∨m≡n m<n+1
    ... | inj₁ (s≤s m<n) = ¬exists (m , m<n , fm≡x)
    ... | inj₂ refl = ¬fn≡x fm≡x

postulate
  pigeonhole : ∀ N → (f : ℕ → ℕ)
            → (∀ n → n ≤ N → f n < N)
            → ∃[ m ] ∃[ n ] (m < n × n ≤ N × f m ≡ f n)