\begin{code}
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Function.Bijection using ( _⤖_)
open import Data.Fin using ( Fin ; toℕ ; fromℕ<)
open import Relation.Nullary
import Level as L
open import Relation.Binary

record RevMachine {ℓ} : Set (L.suc ℓ) where
  field
    State : Set ℓ
    _↦_ : Rel State ℓ
    deterministic : ∀ {st st₁ st₂} → st ↦ st₁ → st ↦ st₂ → st₁ ≡ st₂
    deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → st₁ ≡ st₂
    has-next : ∀ (st : State) → Dec (∃[ st' ] (st ↦ st'))


module RevNoRepeat {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine M

  is-initial : State → Set _
  is-initial st = ∄[ st' ] (st' ↦ st)
  is-stuck : State → Set _
  is-stuck st = ∄[ st' ] (st' ↦ st)

  data _↦*_ : State → State → Set (L.suc ℓ) where
    ◾ : {st : State} → st ↦* st
    _∷_ : {st₁ st₂ st₃ : State} → st₁ ↦ st₂ → st₂ ↦* st₃ → st₁ ↦* st₃

  data _↦[_]_ : State → ℕ → State → Set (L.suc ℓ) where
    ◾ : ∀ {st} → st ↦[ 0 ] st
    _∷_ : ∀ {st₁ st₂ st₃ n} → st₁ ↦ st₂ → st₂ ↦[ n ] st₃ → st₁ ↦[ suc n ] st₃

  postulate
    Finite-State-Termination : ∀ {N st₀}
      → (∀ (st : State) → Dec (∃[ st' ] (st ↦ st')))
      → State ⤖ Fin N
      → is-initial st₀
      → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)

      
    Finite-State-Termination-With-Countdown : ∀ {N st₀}
      → State ⤖ Fin N
      → is-initial st₀
      → ∀ cd m stₘ → cd + m ≡ N → st₀ ↦[ m ] stₘ
      → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)

    NoRepeat : ∀ {st₀ stₙ stₘ n m}
          → is-initial st₀
          → n < m
          → st₀ ↦[ n ] stₙ
          → st₀ ↦[ m ] stₘ
          → stₙ ≢  stₘ

    Finite-State-Termination-At-N : ∀ {N st₀}
        → State ⤖ Fin N
        → is-initial st₀
        → ∃[ stₙ ] (st₀ ↦[ N ] stₙ) → ⊥


    pigeonhole : ∀ N → (f : ℕ → ℕ)
           → (∀ n → n ≤ N → f n < N)
           → ∃[ m ] ∃[ n ] (m < n × n ≤ N × f m ≡ f n)

    Finite-Reachable-State-Termination : ∀ {N st₀}
      → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
      → is-initial st₀
      → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)


    cd-1 : ∀ {cd} {m} {N}
      → suc (cd + m) ≡ N
      → cd + (m + 1) ≡ N
      
    -- target
    Finite-Reachable-State-Termination-CountDown : ∀ {N st₀}
      → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
      → (has-next : ∀ (st : State) → Dec (∃[ st' ] (st ↦ st')))
      → is-initial st₀
      → ∀ cd m  stₘ → cd + m ≡ N → st₀ ↦[ m ] stₘ
      → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)


\end{code}