module transition-and-trees.TransitionSystems where

-- Section Start Page 30

record TransitionSystem : Set₁ where
  constructor ⌞_,_,_⌟
  field
    Γ : Set
    _⇛_ : Γ → Γ → Set
    T : Γ → Set

data Γ₁ : Set where
    γ₁ : Γ₁
    γ₂ : Γ₁
    γ₃ : Γ₁
    γ₄ : Γ₁

data False : Set where
data True : Set where
    unit : True

_⇛₁_ : Γ₁ → Γ₁ → Set
γ₁ ⇛₁ γ₁ = False
γ₁ ⇛₁ γ₂ = True
γ₁ ⇛₁ γ₃ = False
γ₁ ⇛₁ γ₄ = True
γ₂ ⇛₁ γ₁ = False
γ₂ ⇛₁ γ₂ = False
γ₂ ⇛₁ γ₃ = True
γ₂ ⇛₁ γ₄ = False
γ₃ ⇛₁ y  = False
γ₄ ⇛₁ y  = False

T₁_ : Γ₁ → Set
T₁ γ₁ = False
T₁ γ₂ = False
T₁ γ₃ = True
T₁ γ₄ = True

x : TransitionSystem
x = ⌞ Γ₁ , _⇛₁_ , T₁_ ⌟

-- Section End Page 30
