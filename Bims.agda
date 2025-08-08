module transition-and-trees.Bims where
open import Data.Integer using (+_) renaming (ℤ to Num)
open import Data.Integer.Literals
open import Data.String using () renaming (String to Var)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (∃; ∃₂) renaming (_×_ to _and_)
open import transition-and-trees.TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
open import transition-and-trees.BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _≟_ to _=ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)


-- Section Start Page 29

data Aexp₁ : Set where
    N_ : Num → Aexp₁
    -- V_ : Var → Aexp₁ -- The book decides to not define variables yet
    _+_ : Aexp₁ → Aexp₁ → Aexp₁
    _*_ : Aexp₁ → Aexp₁ → Aexp₁
    _-_ : Aexp₁ → Aexp₁ → Aexp₁
    [_] : Aexp₁ → Aexp₁

data Bexp : Set where
    _==_ : Aexp₁ → Aexp₁ → Bexp
    _<_ : Aexp₁ → Aexp₁ → Bexp
    ¬_ : Bexp → Bexp
    _∧_ : Bexp → Bexp → Bexp
    ⟨_⟩ : Bexp → Bexp

data Stm : Set where
    skip : Stm
    _←_ : Var → Aexp₁ → Stm
    _Å_ : Stm → Stm → Stm
    if_then_else_ : Bexp → Stm → Stm → Stm
    _while_ : Stm → Bexp → Stm

infixr 5 N_
infixr 5 ++_

exprPg29 : Aexp₁
exprPg29 = (N + 3 + N + 4) * (N + 14 + N + 9)

-- TODO: complain to book owner: Bims in the book doesn't define n like I've done. I don't understand what the syntactic catagory of 3 is, Aexp₁ or Num or both?

-- Section End Page 29

-- Section Start Page 30

infixl 2 _Å_
infixr 3 _*_
infixr 4 _+_
infixr 4 _-_

_≠_ : Aexp₁ → Aexp₁ → Bexp
_≠_ a b = ¬ (a == b)

-- Section End Page 30

-- Section Start Page 32-33

-- 3.4.1 A big-step semantics of Aexp₁

-- The book doesn't define Transition on Nums. I assume there is no transition, so the extension is simply False
-- Turn subtype in argument to sumtype
⭆⇒ : (Aexp₁ → ℤ) → (ℤ ⊎ Aexp₁ → ℤ ⊎ Aexp₁ → Set)
⭆⇒ x (inj₁ x₁) (inj₁ z) = ⊥
⭆⇒ x (inj₂ y) (inj₁ z) = ⊤
⭆⇒ x y (inj₂ z) = ⊥

T₁ : (ℤ ⊎ Aexp₁ → Set)
T₁ (inj₁ x) = ⊤
T₁ (inj₂ x) = ⊥

_⇒₁_ : ℤ ⊎ Aexp₁ → ℤ ⊎ Aexp₁ → Set
inj₂ (α₁ + α₂) ⇒₁ inj₁ v = ∃₂ λ(v₁ v₂ : ℤ)→ inj₂ α₁ ⇒₁ inj₁ v₁ and inj₂ α₂ ⇒₁ inj₁ v₂ → v ≡ (v₁ +ℤ v₂) -- [PLUS_BSS]
inj₂ (α₁ * α₂) ⇒₁ inj₁ v = ∃₂ λ(v₁ v₂ : ℤ)→ inj₂ α₁ ⇒₁ inj₁ v₁ and inj₂ α₂ ⇒₁ inj₁ v₂ → v ≡ (v₁ *ℤ v₂) -- [MULT_BSS]
inj₂ (α₁ - α₂) ⇒₁ inj₁ v = ∃₂ λ(v₁ v₂ : ℤ)→ inj₂ α₁ ⇒₁ inj₁ v₁ and inj₂ α₂ ⇒₁ inj₁ v₂ → v ≡ (v₁ -ℤ v₂) -- [MINUS_BSS]
inj₂ [ x ] ⇒₁ inj₁ v = inj₂ x ⇒₁ inj₁ v  -- [PARENT_BSS]
inj₂ (N n) ⇒₁ inj₁ v = n ≡ v -- [NUM_BSS]
inj₁ x ⇒₁ y = ⊥ -- Not mentioned, therefore False
inj₂ x ⇒₁ inj₂ y = ⊥ -- Not mentioned, therefore False

Aexp₁Semantic : TransitionSystem
Aexp₁Semantic = ⌞ (ℤ ⊎ Aexp₁) , _⇒₁_ , T₁ ⌟

Aexp₁-is-big-step : Set
Aexp₁-is-big-step = (x y : (ℤ ⊎ Aexp₁)) → (x ⇒₁ y) → (T₁ y)
Aexp₁-is-big-step-proof : Aexp₁-is-big-step
Aexp₁-is-big-step-proof (inj₁ x) (inj₁ y) = λ z → tt
Aexp₁-is-big-step-proof (inj₁ x) (inj₂ y) = λ z → z
Aexp₁-is-big-step-proof (inj₂ x) (inj₁ y) = λ z → tt
Aexp₁-is-big-step-proof (inj₂ (N x)) (inj₂ y) ()
Aexp₁-is-big-step-proof (inj₂ (x + x₁)) (inj₂ y) ()
Aexp₁-is-big-step-proof (inj₂ (x * x₁)) (inj₂ y) ()
Aexp₁-is-big-step-proof (inj₂ (x - x₁)) (inj₂ y) ()
Aexp₁-is-big-step-proof (inj₂ [ x ]) (inj₂ y) ()

Aexp₁big-semantic : BigStepSemantics Aexp₁Semantic
Aexp₁big-semantic = ⌈> Aexp₁-is-big-step-proof


-- Section End Page 32-33

-- Section Start Page 36-37
-- A small-step semantics of Aexp₁

-- Need to redefine Aexp to support non-literals too...
-- "The presentation becomes a little easier if we can let values appear directly
-- in our intermediate results. We do this by extending the formation rules for
-- Aexp such that values become elements of Aexp"
data Aexp₂ : Set where
    N_ : Num → Aexp₂ -- Number literals
    ++_  : Num → Aexp₂ -- Parsed number
    -- V_ : Var → Aexp₂ -- The book decides to not define variables yet
    _+_ : Aexp₂ → Aexp₂ → Aexp₂
    _*_ : Aexp₂ → Aexp₂ → Aexp₂
    _-_ : Aexp₂ → Aexp₂ → Aexp₂
    [_] : Aexp₂ → Aexp₂

_or_ = _⊎_

infix 4 _⇒₂_

data _⇒₂_ : Aexp₂ → Aexp₂ → Set where

  -- PLUS
  PLUS-1ₛₛₛ : ∀ {α₁ α₁′ α₂}
            → α₁ ⇒₂ α₁′
            → (α₁ + α₂) ⇒₂ (α₁′ + α₂)

  PLUS-2ₛₛₛ : ∀ {α₁ α₂ α₂′}
            → α₂ ⇒₂ α₂′
            → (α₁ + α₂) ⇒₂ (α₁ + α₂′)

  PLUS-3ₛₛₛ : ∀ {x y}
            → (++ x + ++ y) ⇒₂ ++ x +ℤ y

  -- MULT
  MULT-1ₛₛₛ : ∀ {α₁ α₁′ α₂}
            → α₁ ⇒₂ α₁′
            → (α₁ * α₂) ⇒₂ (α₁′ * α₂)

  MULT-2ₛₛₛ : ∀ {α₁ α₂ α₂′}
            → α₂ ⇒₂ α₂′
            → (α₁ * α₂) ⇒₂ (α₁ * α₂′)

  MULT-3ₛₛₛ : ∀ {x y}
            → (++ x * ++ y) ⇒₂ ++ x *ℤ y

  -- SUB
  SUB-1ₛₛₛ : ∀ {α₁ α₁′ α₂}
           → α₁ ⇒₂ α₁′
           → (α₁ - α₂) ⇒₂ (α₁′ - α₂)

  SUB-2ₛₛₛ : ∀ {α₁ α₂ α₂′}
           → α₂ ⇒₂ α₂′
           → (α₁ - α₂) ⇒₂ (α₁ - α₂′)

  SUB-3ₛₛₛ : ∀ {x y}
           → (++ x - ++ y) ⇒₂ ++ x -ℤ y

  -- PARENTHESES
  PARENT-1ₛₛₛ : ∀ {x y}
              → x ⇒₂ y
              → [ x ] ⇒₂ [ y ]

  PARENT-2ₛₛₛ : ∀ {x y}
              → x ≡ y
              → [ ++ x ] ⇒₂ ++ y

  -- NUM
  NUMₛₛₛ : ∀ {x y}
         → x ≡ y
         → N x ⇒₂ ++ y


T₂ : (Aexp₂ → Set)
T₂ (++ x) = ⊤
T₂ _ = ⊥

Aexp₂Semantic : TransitionSystem
Aexp₂Semantic = ⌞ Aexp₂ , _⇒₂_ , T₂ ⌟

-- Section End Page 36-37

-- Section Start Page 38. This label is place 1
-- page 28 is also done in TransitionSystems.agda

open import Data.Nat using (ℕ) renaming ()

open TransitionSystem Aexp₂Semantic using () renaming (_⇛⟨_⟩_ to _⇒₂⟨_⟩_; step-zero to step-zero₂; step-suc to step-suc₂)

exampleAexp : (((N + 3) + (N + 12)) * (N + 4)*((N + 5)*(N + 8)))
      ⇒₂⟨ 3 ⟩ ((++ + 15)            * (N + 4)*((N + 5)*(N + 8)))
exampleAexp =
    step-suc₂ (MULT-1ₛₛₛ (PLUS-1ₛₛₛ (NUMₛₛₛ refl)))
        (step-suc₂ (MULT-1ₛₛₛ (PLUS-2ₛₛₛ (NUMₛₛₛ refl)))
            (step-suc₂ (MULT-1ₛₛₛ PLUS-3ₛₛₛ)
                step-zero₂))

-- Aexp₂Semantic .TransitionSystem._⇒⟨_⟩_

--open TransitionSystem using (_⇒*_)
--
--( ) ⇒*

-- Section End Page 38