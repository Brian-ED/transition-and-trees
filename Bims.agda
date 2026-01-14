module Bims where

-- Section Start Page 29

module Aexp₁-bigstep-semantic where
    open import Data.String using () renaming (String to Var)
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    data Aexp₁ : Set where
        N_ : Num → Aexp₁
        -- V_ : Var → Aexp₁ -- The book decides to not define variables yet
        _+_ : Aexp₁ → Aexp₁ → Aexp₁
        _*_ : Aexp₁ → Aexp₁ → Aexp₁
        _-_ : Aexp₁ → Aexp₁ → Aexp₁
        [_] : Aexp₁ → Aexp₁

    data Bexp : Set where
        tt : Bexp
        ff : Bexp
        _==_ : Aexp₁ → Aexp₁ → Bexp
        _<_ : Aexp₁ → Aexp₁ → Bexp
        ¬_ : Bexp → Bexp
        _∧_ : Bexp → Bexp → Bexp
        ⟨_⟩ : Bexp → Bexp

    data Stm : Set where
        skip : Stm
        _←_ : Var → Aexp₁ → Stm
        _Å_ : Stm → Stm → Stm
        ifStm_then_else : Bexp → Stm → Stm → Stm
        _while_ : Stm → Bexp → Stm

    infixr 5 N_
    infixl 2 _Å_
    infixr 3 _*_
    infixr 4 _+_
    infixr 4 _-_

    -- Section End Page 29

    -- Section Start Page 30

    -- Section End Page 30

    -- Section Start Page 32-33
    -- 3.4.1 A big-step semantics of Aexp₁

    data _⇒₁_ : Num ⊎ Aexp₁ → Num ⊎ Aexp₁ → Set where
        _PLUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₂ α₁ ⇒₁ inj₁ v₁
                   → inj₂ α₂ ⇒₁ inj₁ v₂
                   → inj₂ (α₁ + α₂) ⇒₁ inj₁ (v₁ +ℤ v₂)

        _MULT-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₂ α₁ ⇒₁ inj₁ v₁
                   → inj₂ α₂ ⇒₁ inj₁ v₂
                   → inj₂ (α₁ * α₂) ⇒₁ inj₁ (v₁ *ℤ v₂)

        _MINUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                    → inj₂ α₁ ⇒₁ inj₁ v₁
                    → inj₂ α₂ ⇒₁ inj₁ v₂
                    → inj₂ ( α₁ - α₂ ) ⇒₁ inj₁ (v₁ -ℤ v₂)

        PARENT-BSS_ : ∀ {α₁ v₁}
                    → inj₂ α₁ ⇒₁ inj₁ v₁
                    → inj₂ [ α₁ ] ⇒₁ inj₁ v₁

        NUM-BSS_ : ∀ {n}
                 → inj₂ (N n) ⇒₁ inj₁ n

    infixr 5 _PLUS-BSS_
    infixr 5 _MULT-BSS_
    infixr 5 _MINUS-BSS_
    infixr 5 PARENT-BSS_
    infixr 5 NUM-BSS_

-- Section End Page 32-33

-- Section Start Page 36-37
-- A small-step semantics of Aexp₁

module Aexp₁-smallstep-semantic where
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)

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

    data Bexp : Set where
        tt : Bexp
        ff : Bexp
        _==_ : Aexp₂ → Aexp₂ → Bexp
        _<_ : Aexp₂ → Aexp₂ → Bexp
        ¬_ : Bexp → Bexp
        _∧_ : Bexp → Bexp → Bexp
        ⟨_⟩ : Bexp → Bexp

    infixr 5 N_
    infixr 5 ++_
    infixr 3 _*_
    infixr 4 _+_
    infixr 4 _-_
    infix 4 _⇒₂_

    infixr 5 PLUS-1ₛₛₛ_
    infixr 5 PLUS-2ₛₛₛ_
    infixr 5 PLUS-3ₛₛₛ
    infixr 5 MULT-1ₛₛₛ_
    infixr 5 MULT-2ₛₛₛ_
    infixr 5 MULT-3ₛₛₛ
    infixr 5 SUB-1ₛₛₛ_
    infixr 5 SUB-2ₛₛₛ_
    infixr 5 SUB-3ₛₛₛ
    infixr 5 PARENT-1ₛₛₛ_
    infixr 5 NUMₛₛₛ_

    data _⇒₂_ : Aexp₂ → Aexp₂ → Set where

        -- PLUS
        PLUS-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒₂ α₁´
                   → (α₁ + α₂) ⇒₂ (α₁´ + α₂)

        PLUS-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒₂ α₂´
                   → (α₁ + α₂) ⇒₂ (α₁ + α₂´)

        PLUS-3ₛₛₛ : ∀ {x y}
                  → (++ x + ++ y) ⇒₂ ++ x +ℤ y

        -- MULT
        MULT-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒₂ α₁´
                   → (α₁ * α₂) ⇒₂ (α₁´ * α₂)

        MULT-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒₂ α₂´
                   → (α₁ * α₂) ⇒₂ (α₁ * α₂´)

        MULT-3ₛₛₛ : ∀ {x y}
                  → (++ x * ++ y) ⇒₂ ++ x *ℤ y

        -- SUB
        SUB-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                  → α₁ ⇒₂ α₁´
                  → (α₁ - α₂) ⇒₂ (α₁´ - α₂)

        SUB-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                  → α₂ ⇒₂ α₂´
                  → (α₁ - α₂) ⇒₂ (α₁ - α₂´)

        SUB-3ₛₛₛ : ∀ {x y}
                 → (++ x - ++ y) ⇒₂ ++ x -ℤ y

        -- PARENTHESES
        PARENT-1ₛₛₛ_ : ∀ {x y}
                     → x ⇒₂ y
                     → [ x ] ⇒₂ [ y ]

        PARENT-2ₛₛₛ_ : ∀ {x y}
                     → x ≡ y
                     → [ ++ x ] ⇒₂ ++ y

        -- NUM
        NUMₛₛₛ_ : ∀ {x y}
                → x ≡ y
                → N x ⇒₂ ++ y

-- Section End Page 36-37

-- Section Begin Page 40

module Bexp-bigstep-transition where
    open Aexp₁-bigstep-semantic using (Bexp; _⇒₁_; _==_; _<_; ¬_; ⟨_⟩; _∧_)

    open import Data.Integer using () renaming (_<_ to _<ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool; true; false)


    data _⇒b_ : (Bool ⊎ Bexp) → (Bool ⊎ Bexp) → Set where

        _EQUALS-1-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                       → inj₂ α₁ ⇒₁ inj₁ v₁
                       → inj₂ α₂ ⇒₁ inj₁ v₂
                       → v₁ ≡ v₂
                       → inj₂ (α₁ == α₂) ⇒b inj₁ true

        _EQUALS-2-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                       → inj₂ α₁ ⇒₁ inj₁ v₁
                       → inj₂ α₂ ⇒₁ inj₁ v₂
                       → not (v₁ ≡ v₂)
                       → inj₂ (α₁ == α₂) ⇒b inj₁ false

        _GREATERTHAN-1-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                            → inj₂ α₁ ⇒₁ inj₁ v₁
                            → inj₂ α₂ ⇒₁ inj₁ v₂
                            → v₁ <ℤ v₂
                            → inj₂ (α₁ < α₂) ⇒b inj₁ false

        _GREATERTHAN-2-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                            → inj₂ α₁ ⇒₁ inj₁ v₁
                            → inj₂ α₂ ⇒₁ inj₁ v₂
                            → not (v₁ <ℤ v₂)
                            → inj₂ (α₁ < α₂) ⇒b inj₁ false

        NOT-1-BSS_ : ∀ {b}
                   → inj₂ b ⇒b inj₁ false
                   → inj₂ (¬ b) ⇒b inj₁ true

        NOT-2-BSS_ : ∀ {b}
                   → inj₂ b ⇒b inj₁ true
                   → inj₂ (¬ b) ⇒b inj₁ false

        PARENTH-B-BSS : ∀ {b v}
                      → inj₂ b ⇒b v
                      → inj₂ ⟨ b ⟩ ⇒b v

        AND-1-BSS : ∀ {b₁ b₂}
                  → inj₂ b₁ ⇒b inj₁ true
                  → inj₂ b₂ ⇒b inj₁ true
                  → inj₂ (b₁ ∧ b₂) ⇒b inj₁ true

        AND-2-BSS : ∀ {b₁ b₂}
                  → (inj₂ b₁ ⇒b inj₁ false)
                  ⊎ (inj₂ b₂ ⇒b inj₁ false)
                  → inj₂ (b₁ ∧ b₂) ⇒b inj₁ false

-- Problem 3.16
module Bexp-smallstep-transition where
    open Aexp₁-smallstep-semantic

    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _-ℤ_; _<_ to _<ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool; true; false)
    open import Data.Nat using (_≡ᵇ_)


    _==ℤ_ : Num → Num → Bool
    Num.pos x ==ℤ Num.pos y = x ≡ᵇ y
    Num.pos x ==ℤ Num.negsuc y = false
    Num.negsuc x ==ℤ Num.pos y = false
    Num.negsuc x ==ℤ Num.negsuc y = x ≡ᵇ y

--        NOT-1-BSS_ : ∀ {b}
--                → inj₂ b ⇒b inj₁ false
--                → inj₂ (¬ b) ⇒b inj₁ true
--
--        NOT-2-BSS_ : ∀ {b}
--                   → inj₂ b ⇒b inj₁ true
--                   → inj₂ (¬ b) ⇒b inj₁ false
--
--        PARENTH-B-BSS : ∀ {b v}
--                      → inj₂ b ⇒b v
--                      → inj₂ ⟨ b ⟩ ⇒b v
--
--        AND-1-BSS : ∀ {b₁ b₂}
--                  → inj₂ b₁ ⇒b inj₁ true
--                  → inj₂ b₂ ⇒b inj₁ true
--                  → inj₂ (b₁ ∧ b₂) ⇒b inj₁ true
--
--        AND-2-BSS : ∀ {b₁ b₂}
--                  → (inj₂ b₁ ⇒b inj₁ false)
--                  ⊎ (inj₂ b₂ ⇒b inj₁ false)
--                  → inj₂ (b₁ ∧ b₂) ⇒b inj₁ false

    open import Data.Bool using (if_then_else_; Bool; true; false)

    data _⇒b_ : Bexp → Bexp → Set where

        EQUALS-1-BSS_ : ∀ {α₁ α₂ α₂´}
                      → α₂ ⇒₂ α₂´
                      → (α₁ == α₂) ⇒b (α₁ == α₂´)

        EQUALS-2-BSS_ : ∀ {α₁ α₁´ α₂}
                      → α₁ ⇒₂ α₁´
                      → (α₁ == α₂) ⇒b (α₁´ == α₂)

        EQUALS-3-BSS : ∀ {x y}
                     → ((++ x) == (++ y)) ⇒b (if (x ==ℤ y) then tt else ff)


        GREATERTHAN-1-BSS_ : ∀ {α₁ α₂ α₂´}
                           → α₂ ⇒₂ α₂´
                           → (α₁ == α₂) ⇒b (α₁ == α₂´)

        GREATERTHAN-2-BSS_ : ∀ {α₁ α₁´ α₂}
                           → α₁ ⇒₂ α₁´
                           → (α₁ == α₂) ⇒b (α₁´ == α₂)

        GREATERTHAN-3-BSS : ∀ {x y}
                          → ((++ x) == (++ y)) ⇒b (if (x ==ℤ y) then tt else ff)


--        _GREATERTHAN-1-BSS_ : ∀ {α₁ α₂ v₁ v₂}
--                            → α₁ ⇒₂ v₁
--                            → α₂ ⇒₂ v₂
--                            → v₁ <ℤ v₂
--                            → inj₂ (α₁ < α₂) ⇒b inj₁ false

--        _GREATERTHAN-2-BSS_ : ∀ {α₁ α₂ v₁ v₂}
--                            → inj₂ α₁ ⇒₂ inj₁ v₁
--                            → inj₂ α₂ ⇒₂ inj₁ v₂
--                            → not (v₁ <ℤ v₂)
--                            → inj₂ (α₁ < α₂) ⇒b inj₁ false


--        -- PLUS
--        PLUS-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
--                → α₁ ⇒₂ α₁´
--                → (α₁ + α₂) ⇒₂ (α₁´ + α₂)
--
--        PLUS-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
--                → α₂ ⇒₂ α₂´
--                → (α₁ + α₂) ⇒₂ (α₁ + α₂´)
--
--        PLUS-3ₛₛₛ : ∀ {x y}
--                → (++ x + ++ y) ⇒₂ ++ x +ℤ y
--
--        -- MULT
--        MULT-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
--                → α₁ ⇒₂ α₁´
--                → (α₁ * α₂) ⇒₂ (α₁´ * α₂)
--
--        MULT-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
--                → α₂ ⇒₂ α₂´
--                → (α₁ * α₂) ⇒₂ (α₁ * α₂´)
--
--        MULT-3ₛₛₛ : ∀ {x y}
--                → (++ x * ++ y) ⇒₂ ++ x *ℤ y
--
--        -- SUB
--        SUB-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
--                → α₁ ⇒₂ α₁´
--                → (α₁ - α₂) ⇒₂ (α₁´ - α₂)
--
--        SUB-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
--                → α₂ ⇒₂ α₂´
--                → (α₁ - α₂) ⇒₂ (α₁ - α₂´)
--
--        SUB-3ₛₛₛ : ∀ {x y}
--                → (++ x - ++ y) ⇒₂ ++ x -ℤ y
--
--        -- PARENTHESES
--        PARENT-1ₛₛₛ_ : ∀ {x y}
--                    → x ⇒₂ y
--                    → [ x ] ⇒₂ [ y ]
--
--        PARENT-2ₛₛₛ_ : ∀ {x y}
--                    → x ≡ y
--                    → [ ++ x ] ⇒₂ ++ y
--
--        -- NUM
--        NUMₛₛₛ_ : ∀ {x y}
--                → x ≡ y
--                → N x ⇒₂ ++ y


-- Section End Page 40

module Aexp₃-semantic where
    open import State using (State; _[_↦_]; lookup; emptyState)
    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_; _<_ to _<ℤ_)
    open import Data.String using () renaming (String to Var)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import BigAndSmallStepSemantics using (⌈>; BigStepSemantics)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤) renaming (tt to ttt)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Agda.Builtin.Maybe using (Maybe; just; nothing)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool; true; false)


    -- Section Start Page 44-45

    infixr 5 N_
    infixr 5 ++_
    infixr 3 _*_
    infixr 4 _+_
    infixr 4 _-_

    infixr 5 _PLUS-BSS_
    infixr 5 _MULT-BSS_
    infixr 5 _MINUS-BSS_
    infixr 5 PARENT-BSS_

    data Aexp₃ : Set where
        N_ : Num → Aexp₃ -- Number literals
        ++_  : Num → Aexp₃ -- Parsed number
        V_ : Var → Aexp₃
        _+_ : Aexp₃ → Aexp₃ → Aexp₃
        _*_ : Aexp₃ → Aexp₃ → Aexp₃
        _-_ : Aexp₃ → Aexp₃ → Aexp₃
        [_] : Aexp₃ → Aexp₃


    data _⊢_⇒₃_ : State → Num ⊎ Aexp₃ → Num ⊎ Aexp₃ → Set where
        _PLUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                   → s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                   → s ⊢ inj₂ (α₁ + α₂) ⇒₃ inj₁ (v₁ +ℤ v₂)

        _MULT-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                   → s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                   → s ⊢ inj₂ (α₁ * α₂) ⇒₃ inj₁ (v₁ *ℤ v₂)

        _MINUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                    → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                    → s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                    → s ⊢ inj₂ ( α₁ - α₂ ) ⇒₃ inj₁ (v₁ -ℤ v₂)

        PARENT-BSS_ : ∀ {s α₁ v₁}
                    → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                    → s ⊢ inj₂ [ α₁ ] ⇒₃ inj₁ v₁

        NUM-BSS : ∀ {s n}
                → s ⊢ inj₂ (N n) ⇒₃ inj₁ n

        VAR-BSS_ : ∀ {s x v}
                 → (lookup x s) ≡ just v
                 → s ⊢ inj₂ (V x) ⇒₃ inj₁ v

    -- The book states that the `⌞ (Num ⊎ Aexp₃) , (_⊢_⇒₃_ s) , T₃ ⌟` transition system is a big-step-semantic, though does not prove it.
    -- Here is a proof for any starting state s:

    T₃ : (Num ⊎ Aexp₃ → Set)
    T₃ (inj₁ x) = ⊤
    T₃ (inj₂ x) = ⊥

    Aexp₃Semantic : State → TransitionSystem
    Aexp₃Semantic s = ⌞ (Num ⊎ Aexp₃) , (_⊢_⇒₃_ s) , T₃ ⌟

    Aexp₃-is-big-step-proof : ∀ s x y → s ⊢ x ⇒₃ y → T₃ y
    Aexp₃-is-big-step-proof s (inj₁ x) (inj₁ x₁) = λ _ → ttt
    Aexp₃-is-big-step-proof s (inj₁ x) (inj₂ y) ()
    Aexp₃-is-big-step-proof s (inj₂ y₁) (inj₁ x) = λ _ → ttt
    Aexp₃-is-big-step-proof s (inj₂ y₁) (inj₂ y) ()
    Aexp₃big-semantic : ∀ s → BigStepSemantics (Aexp₃Semantic s)
    Aexp₃big-semantic s = ⌈> (Aexp₃-is-big-step-proof s)

    -- Section End Page 44-45

    -- Section Begin Page 46

    data Bexp₃ : Set where
        tt₃ : Bexp₃
        ff₃ : Bexp₃
        _==₃_ : Aexp₃ → Aexp₃ → Bexp₃
        _<₃_ : Aexp₃ → Aexp₃ → Bexp₃
        ¬₃_ : Bexp₃ → Bexp₃
        _∧₃_ : Bexp₃ → Bexp₃ → Bexp₃
        ⟨_⟩₃ : Bexp₃ → Bexp₃

    data _⊢_⇒₃b_ : State → Bool ⊎ Bexp₃ → Bool ⊎ Bexp₃ → Set where

        _EQUAL-1-BSS_ : ∀ {s α₁ α₂ v}
                      → s ⊢ inj₂ α₁ ⇒₃ inj₁ v
                      →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v
                      → s ⊢ (inj₂ (α₁ ==₃ α₂)) ⇒₃b inj₁ true

        EQUALS-2-BSS : ∀ {s α₁ α₂ v₁ v₂}
                     → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                     →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                     → not (v₁ ≡ v₂)
                     → s ⊢ inj₂ (α₁ ==₃ α₂) ⇒₃b inj₁ false

        _GREATERTHAN-1-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                            → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                            →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                            → v₁ <ℤ v₂
                            → s ⊢ inj₂ (α₁ <₃ α₂) ⇒₃b inj₁ false

        _GREATERTHAN-2-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                            → s ⊢ inj₂ α₁ ⇒₃ inj₁ v₁
                            →  s ⊢ inj₂ α₂ ⇒₃ inj₁ v₂
                            → not (v₁ <ℤ v₂)
                            → s ⊢ inj₂ (α₁ <₃ α₂) ⇒₃b inj₁ false

        NOT-1-BSS_ : ∀ {s b}
                   → s ⊢ inj₂ b ⇒₃b inj₁ false
                   → s ⊢ inj₂ (¬₃ b) ⇒₃b inj₁ true

        NOT-2-BSS_ : ∀ {s b}
                   → s ⊢ inj₂ b ⇒₃b inj₁ true
                   → s ⊢ inj₂ (¬₃ b) ⇒₃b inj₁ false

        PARENTH-B-BSS : ∀ {s b v}
                      → s ⊢ inj₂ b ⇒₃b v
                      → s ⊢ inj₂ ⟨ b ⟩₃ ⇒₃b v

        AND-1-BSS : ∀ {s b₁ b₂}
                  → s ⊢ inj₂ b₁ ⇒₃b inj₁ true
                  → s ⊢ inj₂ b₂ ⇒₃b inj₁ true
                  → s ⊢ inj₂ (b₁ ∧₃ b₂) ⇒₃b inj₁ true

        AND-2-BSS : ∀ {s b₁ b₂}
                  → (s ⊢ inj₂ b₁ ⇒₃b inj₁ false)
                  ⊎ (s ⊢ inj₂ b₂ ⇒₃b inj₁ false)
                  → s ⊢ inj₂ (b₁ ∧₃ b₂) ⇒₃b inj₁ false

    -- Section End Page 46

    -- Section Begin Page 47

    data Stm₃ : Set where
        skip₃ : Stm₃
        _←₃_ : Var → Aexp₃ → Stm₃
        _Å₃_ : Stm₃ → Stm₃ → Stm₃
        ifStm₃_then_else : Bexp₃ → Stm₃ → Stm₃ → Stm₃
        while_do₃_ : Bexp₃ → Stm₃ → Stm₃

    data ⟨_,_⟩⇒₃_ : Stm₃ → State → State → Set where
        ASS-BSS         : ∀ {x a s v}
                        → s ⊢ inj₂ a ⇒₃ inj₁ v
                        → ⟨ (x ←₃ a) , s ⟩⇒₃ (s [ x ↦ v ])

        SKIP-BSS        : ∀ {s}
                        → ⟨ skip₃ , s ⟩⇒₃ s

        COMP-BSS        : ∀ {S₁ S₂ s s´ s˝}
                        → ⟨ S₁ , s ⟩⇒₃ s˝
                        → ⟨ S₂ , s˝ ⟩⇒₃ s´
                        → ⟨ (S₁ Å₃ S₂) , s ⟩⇒₃ s´

        IF-TRUE-BSS     : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₁ , s ⟩⇒₃ s´
                        → s ⊢ inj₂ b ⇒₃b inj₁ true
                        → ⟨ (ifStm₃ b then S₁ else S₂) , s ⟩⇒₃ s´

        IF-FALSE-BSS    : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₂ , s ⟩⇒₃ s´
                        → s ⊢ inj₂ b ⇒₃b inj₁ false
                        → ⟨ (ifStm₃ b then S₁ else S₂) , s ⟩⇒₃ s´

        WHILE-TRUE-BSS  : ∀ {S s s´ s˝ b}
                        → s ⊢ inj₂ b ⇒₃b inj₁ true
                        → ⟨ S , s ⟩⇒₃ s˝
                        → ⟨ (while b do₃ S) , s˝ ⟩⇒₃ s´
                        → ⟨ (while b do₃ S) , s ⟩⇒₃ s´

        WHILE-FALSE-BSS : ∀ {S s s´ b}
                        → s ⊢ inj₂ b ⇒₃b inj₁ false
                        → s´ ≡ s
                        → ⟨ (while b do₃ S) , s ⟩⇒₃ s´

    -- Section End Page 47
