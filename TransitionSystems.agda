module TransitionSystems where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃; _,_)

-- Section Start Page 30

record TransitionSystem : Set₁ where
    constructor ⌞_,_,_⌟
    field
        Γ : Set
        _⇒_ : Γ → Γ → Set
        T : Γ → Set

    -- INNER Section Begin Page 38. This label is place 2

    data _⇒⟨_⟩_ : Γ → ℕ → Γ → Set where
        x⇒x : ∀ {γ} → γ ⇒⟨ 0 ⟩ γ
        _⇒∘⇒_ : ∀ {γ γ´ k γ˝}
              → γ ⇒ γ˝
              → γ˝ ⇒⟨ k ⟩ γ´
              → γ ⇒⟨ suc k ⟩ γ´

    _⇒*_ : Γ → Γ → Set
    γ ⇒* γ′ = ∃ λ k → γ ⇒⟨ k ⟩ γ′

    x⇒*x : ∀ {x} → x ⇒* x
    x⇒*x = 0 , x⇒x

    _⇒∘_ : ∀ {x y z} → (z ⇒ x) → x ⇒* y → z ⇒* y
    a ⇒∘ (fst , snd) = suc fst , a ⇒∘⇒ snd

    _∘⇒∘_ : ∀ {x y z}
          → x ⇒* y
          → y ⇒* z
          → x ⇒* z
    (0 , x⇒x) ∘⇒∘ x₁ = x₁
    (suc fst , x ⇒∘⇒ snd) ∘⇒∘ x₁ = x ⇒∘ ((fst , snd) ∘⇒∘ x₁)

    infixr 5 _⇒∘⇒_
    infixr 5 _⇒∘_
    infixr 5 _⇒*_
    infixr 5 _∘⇒∘_


    -- INNER Section End Page 38

-- Section End Page 30
