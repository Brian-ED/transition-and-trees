module TransitionSystems where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃; _,_)

-- Section Start Page 30

open import Level using (Level) renaming (suc to lsuc)

record TransitionSystem {ℓ : Level} : Set (lsuc ℓ) where
    constructor ⌞_,_,_⌟
    field
        Γ : Set ℓ
        _⇒_ : Γ → Γ → Set ℓ
        T : Γ → Set ℓ

    -- INNER Section Begin Page 38. This label is place 2

    data _⇒⟨_⟩_ : Γ → ℕ → Γ → Set ℓ where
        x⇒x : ∀ {γ} → γ ⇒⟨ 0 ⟩ γ
        _⇒∘⇒_ : ∀ {γ γ´ k γ˝}
              → γ ⇒ γ˝
              → γ˝ ⇒⟨ k ⟩ γ´
              → γ ⇒⟨ suc k ⟩ γ´

    _⇒*_ : Γ → Γ → Set ℓ
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
