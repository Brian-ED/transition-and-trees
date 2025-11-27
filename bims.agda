module transition-and-trees.bims where

-- Section Start Page 29
open import transition-and-trees.Bims using (Aexp₁; Bexp; Stm; N_; _+_; _*_)
open import Data.Integer using (+_)

exprPg29 : Aexp₁
exprPg29 = (N + 3 + N + 4) * (N + 14 + N + 9)
-- Section End Page 29

-- Section Start Page 32-33
-- 3.4.1 A big-step semantics of Aexp₁

open import transition-and-trees.Bims using (_⇒₁_)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _≟_ to _=ℤ_; _<_ to _<ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤) renaming (tt to ttt)
open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import transition-and-trees.BigAndSmallStepSemantics using (⌈>; BigStepSemantics)

-- The book doesn't define Transition on Nums. I assume there is no transition, so the extension is simply False
-- Turn subtype in argument to sumtype
⭆⇒ : (Aexp₁ → ℤ) → (ℤ ⊎ Aexp₁ → ℤ ⊎ Aexp₁ → Set)
⭆⇒ x (inj₁ x₁) (inj₁ z) = ⊥
⭆⇒ x (inj₂ y) (inj₁ z) = ⊤
⭆⇒ x y (inj₂ z) = ⊥

T₁ : (ℤ ⊎ Aexp₁ → Set)
T₁ (inj₁ x) = ⊤
T₁ (inj₂ x) = ⊥

Aexp₁Semantic : TransitionSystem
Aexp₁Semantic = ⌞ (ℤ ⊎ Aexp₁) , _⇒₁_ , T₁ ⌟

Aexp₁-is-big-step : Set
Aexp₁-is-big-step = (x y : (ℤ ⊎ Aexp₁)) → (x ⇒₁ y) → (T₁ y)
Aexp₁-is-big-step-proof : Aexp₁-is-big-step
Aexp₁-is-big-step-proof (inj₁ x) (inj₁ y) = λ z → ttt
Aexp₁-is-big-step-proof (inj₂ x) (inj₁ y) = λ z → ttt
Aexp₁-is-big-step-proof x (inj₂ y) ()

Aexp₁big-semantic : BigStepSemantics Aexp₁Semantic
Aexp₁big-semantic = ⌈> Aexp₁-is-big-step-proof

-- Section End Page 32-33


-- Section Start Page 36-37
-- A small-step semantics of Aexp₁

open import transition-and-trees.Bims using (Aexp₂; _⇒₂_; ++_)

T₂ : (Aexp₂ → Set)
T₂ (++ x) = ⊤
T₂ _ = ⊥

Aexp₂Semantic : TransitionSystem
Aexp₂Semantic = ⌞ Aexp₂ , _⇒₂_ , T₂ ⌟

-- Section End Page 36-37

-- Section Start Page 44-45


-- Section End Page 44-45
