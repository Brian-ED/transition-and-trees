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

--    _⇒⟨_⟩_ : Γ → ℕ → Γ → Set
--    γ ⇒⟨ ℕ.zero  ⟩ γ′ = γ ≡ γ′
--    γ ⇒⟨ ℕ.suc n ⟩ γ′ = ∃ λ γ′′ → γ ⇒ γ′′ and (γ′′ ⇒⟨ n ⟩  γ′)

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

data Γ₁ : Set where
    γ₁ : Γ₁
    γ₂ : Γ₁
    γ₃ : Γ₁
    γ₄ : Γ₁

_⇒₁_ : Γ₁ → Γ₁ → Set
γ₁ ⇒₁ γ₁ = ⊥
γ₁ ⇒₁ γ₂ = ⊤
γ₁ ⇒₁ γ₃ = ⊥
γ₁ ⇒₁ γ₄ = ⊤
γ₂ ⇒₁ γ₁ = ⊥
γ₂ ⇒₁ γ₂ = ⊥
γ₂ ⇒₁ γ₃ = ⊤
γ₂ ⇒₁ γ₄ = ⊥
γ₃ ⇒₁ y  = ⊥
γ₄ ⇒₁ y  = ⊥

T₁_ : Γ₁ → Set
T₁ γ₁ = ⊥
T₁ γ₂ = ⊥
T₁ γ₃ = ⊤
T₁ γ₄ = ⊤

testSystem : TransitionSystem
testSystem = ⌞ Γ₁ , _⇒₁_ , T₁_ ⌟

-- Section End Page 30
