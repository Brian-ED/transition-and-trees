module transition-and-trees.BigAndSmallStepSemantics where

open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)

-- Section Start Page 31

record BigStepSemantics (TS : TransitionSystem) : Set₁ where
    constructor ⌈>_
    open TransitionSystem TS
    field
        BigStepping : ∀ (x y : Γ) → (x ⇛ y) → (T y)

open import transition-and-trees.TransitionSystems using (Γ₁; _⇛₁_; T₁_; True; False)

_⇛₂_ : Γ₁ → Γ₁ → Set
x ⇛₂ Γ₁.γ₁ = False
x ⇛₂ Γ₁.γ₂ = False
x ⇛₂ Γ₁.γ₃ = True
x ⇛₂ Γ₁.γ₄ = False

semantic : TransitionSystem
semantic = ⌞ Γ₁ , _⇛₂_ , T₁_ ⌟

semantic-is-big-step : Set
semantic-is-big-step = ∀ (x y : Γ₁) → (x ⇛₂ y) → (T₁ y)
semantic-is-big-step-proof : semantic-is-big-step
semantic-is-big-step-proof x Γ₁.γ₁ = λ ()
semantic-is-big-step-proof x Γ₁.γ₂ = λ ()
semantic-is-big-step-proof x Γ₁.γ₃ = λ z → z
semantic-is-big-step-proof x Γ₁.γ₄ = λ ()

big-semantic : BigStepSemantics semantic
big-semantic = ⌈> semantic-is-big-step-proof

-- TODO: Complain to book maker that a SmallStepSemantic is a big step semantic too.
SmallStepSemantics = TransitionSystem

-- Section End Page 31
