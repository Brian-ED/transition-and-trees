module TransitionSystems where

open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃) renaming (_×_ to _and_)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

-- Section Start Page 30

record TransitionSystem : Set₁ where
    constructor ⌞_,_,_⌟
    field
        Γ : Set
        _⇒_ : Γ → Γ → Set
        T : Γ → Set

    -- INNER Section Begin Page 38. This label is place 2

    data _⇒⟨_⟩_ : Γ → ℕ → Γ → Set where
        step-zero : ∀ {γ} → γ ⇒⟨ 0 ⟩ γ
        _step-suc_ : ∀ {γ γ′ γ″ n}
                   → γ ⇒ γ′
                   → γ′ ⇒⟨ n ⟩ γ″
                   → γ ⇒⟨ suc n ⟩ γ″
    infixr 4 _step-suc_

    _⇒*_ : Γ → Γ → Set
    γ ⇒* γ′ = ∃ λ k → γ ⇒⟨ k ⟩ γ′

    -- INNER Section End Page 38

-- Section End Page 30
