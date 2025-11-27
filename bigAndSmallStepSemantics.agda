module transition-and-trees.bigAndSmallStepSemantics where

open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import transition-and-trees.BigAndSmallStepSemantics using (BigStepSemantics; ⌈>)
open import transition-and-trees.transitionSystems using (Γ₁; T₁_; )

-- Section Start Page 31

_⇒₂_ : Γ₁ → Γ₁ → Set
x ⇒₂ Γ₁.γ₁ = ⊥
x ⇒₂ Γ₁.γ₂ = ⊥
x ⇒₂ Γ₁.γ₃ = ⊤
x ⇒₂ Γ₁.γ₄ = ⊥

semantic : TransitionSystem
semantic = ⌞ Γ₁ , _⇒₂_ , T₁_ ⌟

semantic-is-big-step : Set
semantic-is-big-step = (x y : Γ₁) → (x ⇒₂ y) → (T₁ y)
semantic-is-big-step-proof : semantic-is-big-step
semantic-is-big-step-proof x Γ₁.γ₁ = λ ()
semantic-is-big-step-proof x Γ₁.γ₂ = λ ()
semantic-is-big-step-proof x Γ₁.γ₃ = λ z → z
semantic-is-big-step-proof x Γ₁.γ₄ = λ ()

big-semantic : BigStepSemantics semantic
big-semantic = ⌈> semantic-is-big-step-proof

-- Section End Page 31
