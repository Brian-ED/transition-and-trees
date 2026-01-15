module transitionSystems where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)

-- Section Start Page 30

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

open TransitionSystem testSystem
x = _⇒⟨_⟩_

-- Section End Page 30
