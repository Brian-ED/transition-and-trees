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

    data _⇒₁_ : Aexp₁ ⊎ Num → Aexp₁ ⊎ Num → Set where
        _PLUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₁ α₁ ⇒₁ inj₂ v₁
                   → inj₁ α₂ ⇒₁ inj₂ v₂
                   → inj₁ (α₁ + α₂) ⇒₁ inj₂ (v₁ +ℤ v₂)

        _MULT-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                   → inj₁ α₁ ⇒₁ inj₂ v₁
                   → inj₁ α₂ ⇒₁ inj₂ v₂
                   → inj₁ (α₁ * α₂) ⇒₁ inj₂ (v₁ *ℤ v₂)

        _MINUS-BSS_ : ∀ {α₁ α₂ v₁ v₂}
                    → inj₁ α₁ ⇒₁ inj₂ v₁
                    → inj₁ α₂ ⇒₁ inj₂ v₂
                    → inj₁ ( α₁ - α₂ ) ⇒₁ inj₂ (v₁ -ℤ v₂)

        PARENT-BSS_ : ∀ {α₁ v₁}
                    → inj₁ α₁ ⇒₁ inj₂ v₁
                    → inj₁ [ α₁ ] ⇒₁ inj₂ v₁

        NUM-BSS_ : ∀ {n}
                 → inj₁ (N n) ⇒₁ inj₂ n

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
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool)

    -- Need to redefine Aexp to support non-literals too...
    -- "The presentation becomes a little easier if we can let values appear directly
    -- in our intermediate results. We do this by extending the formation rules for
    -- Aexp such that values become elements of Aexp"
    data Aexp₁ss : Set where
        N_ : Num → Aexp₁ss -- Number literals
        -- V_ : Var → Aexp₁ss -- The book decides to not define variables yet
        _+_ : Aexp₁ss ⊎ Num → Aexp₁ss ⊎ Num → Aexp₁ss
        _*_ : Aexp₁ss ⊎ Num → Aexp₁ss ⊎ Num → Aexp₁ss
        _-_ : Aexp₁ss ⊎ Num → Aexp₁ss ⊎ Num → Aexp₁ss
        [_] : Aexp₁ss ⊎ Num → Aexp₁ss

    data Bexp : Set where
        _==_ : Aexp₁ss ⊎ Num → Aexp₁ss ⊎ Num → Bexp
        _<_ : Aexp₁ss ⊎ Num → Aexp₁ss ⊎ Num → Bexp
        ¬_ : Bexp ⊎ Bool → Bexp
        _∧_ : Bexp ⊎ Bool → Bexp ⊎ Bool → Bexp
        ⟨_⟩ : Bexp ⊎ Bool → Bexp

    infixr 5 N_
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

    data _⇒₂_ : Aexp₁ss ⊎ Num → Aexp₁ss ⊎ Num → Set where

        -- PLUS
        PLUS-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒₂ α₁´
                   → inj₁ (α₁ + α₂) ⇒₂ inj₁(α₁´ + α₂)

        PLUS-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒₂ α₂´
                   → inj₁ (α₁ + α₂) ⇒₂ inj₁ (α₁ + α₂´)

        PLUS-3ₛₛₛ : ∀ {α₁ α₂ n₁ n₂}
                  → α₁ ⇒₂ inj₂ n₁
                  → α₂ ⇒₂ inj₂ n₂
                  → inj₁ (α₁ + α₂) ⇒₂ inj₂ (n₁ +ℤ n₂)

        -- MULT
        MULT-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒₂ α₁´
                   → inj₁ (α₁ * α₂) ⇒₂ inj₁ (α₁´ * α₂)

        MULT-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒₂ α₂´
                   → inj₁ (α₁ * α₂) ⇒₂ inj₁ (α₁ * α₂´)

        MULT-3ₛₛₛ : ∀ {v v₁ v₂}
                  → v ≡ v₁ *ℤ v₂
                  → inj₁ (inj₂ v₁ * inj₂ v₂) ⇒₂ inj₂ v₂

        -- SUB
        SUB-1ₛₛₛ_ : ∀ {α₁ α₁´ α₂}
                  → α₁ ⇒₂ α₁´
                  → inj₁ (α₁ - α₂) ⇒₂ inj₁ (α₁´ - α₂)

        SUB-2ₛₛₛ_ : ∀ {α₁ α₂ α₂´}
                  → α₂ ⇒₂ α₂´
                  → inj₁ (α₁ - α₂) ⇒₂ inj₁ (α₁ - α₂´)

        SUB-3ₛₛₛ : ∀ {x y}
                 → inj₁ (inj₂ x - inj₂ y) ⇒₂ inj₂ (x -ℤ y)

        -- PARENTHESES
        PARENT-1ₛₛₛ_ : ∀ {α α´} -- The book uses α₁ and α₁´, I don't know why it adds the ₁
                     → α ⇒₂ α´
                     → inj₁ [ α ] ⇒₂ inj₁ [ α´ ]

        PARENT-2ₛₛₛ_ : ∀ {x y}
                     → x ≡ y
                     → inj₁ [ inj₂ x ] ⇒₂ inj₂ y

        -- NUM
        NUMₛₛₛ_ : ∀ {x y}
                → x ≡ y
                → inj₁ (N x) ⇒₂ inj₂ y

    open import TransitionSystems using (TransitionSystem; ⌞_,_,_⌟)
    open import Data.Product using (_×_)
    open import Data.Empty using (⊥)
    open import Data.Unit using (⊤)

    transitionSystem = ⌞ Γ , _⇒₂_ , T ⌟
        where
            Γ = Aexp₁ss ⊎ Num
            T : Γ → Set
            T (inj₁ x) = ⊥
            T (inj₂ y) = ⊤

    open TransitionSystem transitionSystem public

-- Section End Page 36-37

-- Section Begin Page 40

module Bexp-bigstep-transition where
    open Aexp₁-bigstep-semantic using (Bexp; _⇒₁_; _==_; _<_; ¬_; ⟨_⟩; _∧_)

    open import Data.Integer using () renaming (_<_ to _<ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)


    data _⇒b_ : Bexp ⊎ Bool → Bexp ⊎ Bool → Set where

        EQUALS-1-BSS : ∀ {α₁ α₂ v₁ v₂}
                     → inj₁ α₁ ⇒₁ inj₂ v₁
                     → inj₁ α₂ ⇒₁ inj₂ v₂
                     → v₁ ≡ v₂
                     → inj₁ (α₁ == α₂) ⇒b inj₂ tt

        EQUALS-2-BSS : ∀ {α₁ α₂ v₁ v₂}
                     → inj₁ α₁ ⇒₁ inj₂ v₁
                     → inj₁ α₂ ⇒₁ inj₂ v₂
                     → not (v₁ ≡ v₂)
                     → inj₁ (α₁ == α₂) ⇒b inj₂ ff

        GREATERTHAN-1-BSS : ∀ {α₁ α₂ v₁ v₂}
                          → inj₁ α₁ ⇒₁ inj₂ v₁
                          → inj₁ α₂ ⇒₁ inj₂ v₂
                          → v₁ <ℤ v₂
                          → inj₁ (α₁ < α₂) ⇒b inj₂ ff

        GREATERTHAN-2-BSS : ∀ {α₁ α₂ v₁ v₂}
                          → inj₁ α₁ ⇒₁ inj₂ v₁
                          → inj₁ α₂ ⇒₁ inj₂ v₂
                          → not (v₁ <ℤ v₂)
                          → inj₁ (α₁ < α₂) ⇒b inj₂ ff

        NOT-1-BSS_ : ∀ {b}
                   → inj₁ b ⇒b inj₂ ff
                   → inj₁ (¬ b) ⇒b inj₂ tt

        NOT-2-BSS_ : ∀ {b}
                   → inj₁ b ⇒b inj₂ tt
                   → inj₁ (¬ b) ⇒b inj₂ ff

        PARENTH-B-BSS : ∀ {b v}
                      → inj₁ b ⇒b v
                      → inj₁ ⟨ b ⟩ ⇒b v

        AND-1-BSS : ∀ {b₁ b₂}
                  → inj₁ b₁ ⇒b inj₂ tt
                  → inj₁ b₂ ⇒b inj₂ tt
                  → inj₁ (b₁ ∧ b₂) ⇒b inj₂ tt

        AND-2-BSS : ∀ {b₁ b₂}
                  → (inj₁ b₁ ⇒b inj₂ ff)
                  ⊎ (inj₁ b₂ ⇒b inj₂ ff)
                  → inj₁ (b₁ ∧ b₂) ⇒b inj₂ ff

-- Problem 3.16
module Bexp-smallstep-transition where
    open Aexp₁-smallstep-semantic

    open import Data.Integer using () renaming (ℤ to Num; _+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _-ℤ_; _<_ to _<ℤ_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open import Relation.Nullary.Negation using () renaming (¬_ to not_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open import Data.Bool using (Bool) renaming (true to tt; false to ff; _∧_ to _∧b_)
    open import Data.Nat using (_≡ᵇ_)

    _==ℤ_ : Num → Num → Bool
    Num.pos x ==ℤ Num.pos y = x ≡ᵇ y
    Num.pos x ==ℤ Num.negsuc y = ff
    Num.negsuc x ==ℤ Num.pos y = ff
    Num.negsuc x ==ℤ Num.negsuc y = x ≡ᵇ y

    open import Data.Bool using (if_then_else_; Bool) renaming (true to tt; false to ff)

    data _⇒b_ : Bexp ⊎ Bool → Bexp ⊎ Bool → Set where

        EQUALS-1-BSS_ : ∀ {α₁ α₁´ α₂}
                      → α₁ ⇒₂ α₁´
                      → inj₁ (α₁ == α₂) ⇒b inj₁ (α₁´ == α₂)

        EQUALS-2-BSS_ : ∀ {α₁ α₂ α₂´}
                      → α₂ ⇒₂ α₂´
                      → inj₁ (α₁ == α₂) ⇒b inj₁ (α₁ == α₂´)

        EQUALS-3-BSS : ∀ {x y}
                     → x ≡ y
                     → inj₁ ((inj₂ x) == (inj₂ y)) ⇒b inj₂ tt

        EQUALS-4-BSS : ∀ {x y}
                     → not x ≡ y
                     → inj₁ ((inj₂ x) == (inj₂ y)) ⇒b inj₂ ff

        GREATERTHAN-1-BSS_ : ∀ {α₁ α₁´ α₂}
                           → α₁ ⇒₂ α₁´
                           → inj₁(α₁ < α₂) ⇒b inj₁(α₁´ < α₂)

        GREATERTHAN-2-BSS_ : ∀ {α₁ α₂ α₂´}
                           → α₂ ⇒₂ α₂´
                           → inj₁(α₁ < α₂) ⇒b inj₁(α₁ < α₂´)

        GREATERTHAN-3-BSS : ∀ {x y}
                          → x <ℤ y
                          → inj₁((inj₂ x) < (inj₂ y)) ⇒b inj₂ tt

        GREATERTHAN-4-BSS : ∀ {x y}
                          → not x <ℤ y
                          → inj₁((inj₂ x) < (inj₂ y)) ⇒b inj₂ ff

        NOT-1-BSS_ : ∀ {α α´}
                   → α ⇒b α´
                   → inj₁ (¬ α) ⇒b inj₁ (¬ α´)

        NOT-2-BSS : ∀ {b}
                  → b ⇒b inj₂ ff
                  → inj₁ (¬ b) ⇒b inj₂ tt

        NOT-3-BSS : ∀ {b}
                  → b ⇒b inj₂ tt
                  → inj₁ (¬ b) ⇒b inj₂ ff

        PARENTH-B-BSS : ∀ {α α´}
                      → α ⇒b α´
                      → inj₁ ⟨ α ⟩ ⇒b inj₁ ⟨ α´ ⟩

        AND-1-BSS_ : ∀ {α₁ α₁´ α₂}
                   → α₁ ⇒b α₁´
                   → inj₁ (α₁ ∧ α₂) ⇒b inj₁ (α₁´ ∧ α₂)

        AND-2-BSS_ : ∀ {α₁ α₂ α₂´}
                   → α₂ ⇒b α₂´
                   → inj₁ (α₁ ∧ α₂) ⇒b inj₁ (α₁ ∧ α₂´)

        AND-3-BSS : ∀ {α₁ α₂}
                  → α₁ ⇒b inj₂ tt
                  → α₂ ⇒b inj₂ tt
                  → inj₁ (α₁ ∧ α₂) ⇒b inj₂ tt

        AND-4-BSS : ∀ {α₁ α₂}
                  → α₁ ≡ ff
                  → inj₁ (inj₂ α₁ ∧ α₂) ⇒b inj₂ ff

        AND-5-BSS : ∀ {α₁ α₂}
                  → α₂ ≡ ff
                  → inj₁ (α₁ ∧ inj₂ α₂) ⇒b inj₂ ff


-- Section End Page 40

module Aexp₂-semantic where
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
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)


    -- Section Start Page 44-45

    infixr 5 N_
    infixr 3 _*_
    infixr 4 _+_
    infixr 4 _-_

    infixr 5 _PLUS-BSS_
    infixr 5 _MULT-BSS_
    infixr 5 _MINUS-BSS_
    infixr 5 PARENT-BSS_

    data Aexp₂ : Set where
        N_ : Num → Aexp₂ -- Number literals
        V_ : Var → Aexp₂
        _+_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Aexp₂
        _*_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Aexp₂
        _-_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Aexp₂
        [_] : Aexp₂ ⊎ Num → Aexp₂


    data _⊢_⇒ₐ_ : State → Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Set where
        _PLUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ α₁ ⇒ₐ inj₂ v₁
                   → s ⊢ α₂ ⇒ₐ inj₂ v₂
                   → s ⊢ inj₁ (α₁ + α₂) ⇒ₐ inj₂ (v₁ +ℤ v₂)

        _MINUS-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                    → s ⊢ α₁ ⇒ₐ inj₂ v₁
                    → s ⊢ α₂ ⇒ₐ inj₂ v₂
                    → s ⊢ inj₁ ( α₁ - α₂ ) ⇒ₐ inj₂ (v₁ -ℤ v₂)

        _MULT-BSS_ : ∀ {s α₁ α₂ v₁ v₂}
                   → s ⊢ α₁ ⇒ₐ inj₂ v₁
                   → s ⊢ α₂ ⇒ₐ inj₂ v₂
                   → s ⊢ inj₁ (α₁ * α₂) ⇒ₐ inj₂ (v₁ *ℤ v₂)

        PARENT-BSS_ : ∀ {s α₁ v₁}
                    → s ⊢ α₁ ⇒ₐ inj₂ v₁
                    → s ⊢ inj₁ [ α₁ ] ⇒ₐ inj₂ v₁

        NUM-BSS : ∀ {s n}
                → s ⊢ inj₁ (N n) ⇒ₐ inj₂ n

        VAR-BSS_ : ∀ {s x v}
                 → (lookup x s) ≡ just v
                 → s ⊢ inj₁ (V x) ⇒ₐ inj₂ v

    -- The book states that the `⌞ (Aexp₂ ⊎ Num) , (_⊢_⇒ₐ_ s) , T₃ ⌟` transition system is a big-step-semantic, though does not prove it.
    -- Here is a proof for any starting state s:

    T₃ : Aexp₂ ⊎ Num → Set
    T₃ (inj₂ x) = ⊤
    T₃ (inj₁ x) = ⊥

    Aexp₂Semantic : State → TransitionSystem
    Aexp₂Semantic s = ⌞ (Aexp₂ ⊎ Num) , (_⊢_⇒ₐ_ s) , T₃ ⌟

    Aexp₂-is-big-step-proof : ∀ s x y → s ⊢ x ⇒ₐ y → T₃ y
    Aexp₂-is-big-step-proof s (inj₂ x) (inj₂ x₁) = λ _ → ttt
    Aexp₂-is-big-step-proof s (inj₂ x) (inj₁ y) ()
    Aexp₂-is-big-step-proof s (inj₁ y₁) (inj₂ x) = λ _ → ttt
    Aexp₂-is-big-step-proof s (inj₁ y₁) (inj₁ y) ()
    Aexp₂big-semantic : ∀ s → BigStepSemantics (Aexp₂Semantic s)
    Aexp₂big-semantic s = ⌈> (Aexp₂-is-big-step-proof s)

    -- Section End Page 44-45

    -- Section Begin Page 46

    data Bexp₂ : Set where
        _==₃_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Bexp₂
        _<₃_ : Aexp₂ ⊎ Num → Aexp₂ ⊎ Num → Bexp₂
        ¬₃_ : Bexp₂ ⊎ Bool → Bexp₂
        _∧₃_ : Bexp₂ ⊎ Bool → Bexp₂ ⊎ Bool → Bexp₂
        ⟨_⟩₃ : Bexp₂ ⊎ Bool → Bexp₂

    data _⊢_⇒₂b_ : State → Bexp₂ ⊎ Bool → Bexp₂ ⊎ Bool → Set where

        _EQUAL-1-BSS_ : ∀ {s α₁ α₂ v}
                      → s ⊢ α₁ ⇒ₐ inj₂ v
                      → s ⊢ α₂ ⇒ₐ inj₂ v
                      → s ⊢ (inj₁ (α₁ ==₃ α₂)) ⇒₂b inj₂ tt

        EQUALS-2-BSS : ∀ {s α₁ α₂ v₁ v₂}
                     → s ⊢ α₁ ⇒ₐ inj₂ v₁
                     → s ⊢ α₂ ⇒ₐ inj₂ v₂
                     → not (v₁ ≡ v₂)
                     → s ⊢ inj₁ (α₁ ==₃ α₂) ⇒₂b inj₂ ff

        GREATERTHAN-1-BSS : ∀ {s α₁ α₂ v₁ v₂}
                          → s ⊢ α₁ ⇒ₐ inj₂ v₁
                          → s ⊢ α₂ ⇒ₐ inj₂ v₂
                          → v₁ <ℤ v₂
                          → s ⊢ inj₁ (α₁ <₃ α₂) ⇒₂b inj₂ tt

        GREATERTHAN-2-BSS : ∀ {s α₁ α₂ v₁ v₂}
                          → s ⊢ α₁ ⇒ₐ inj₂ v₁
                          → s ⊢ α₂ ⇒ₐ inj₂ v₂
                          → not (v₁ <ℤ v₂)
                          → s ⊢ inj₁ (α₁ <₃ α₂) ⇒₂b inj₂ ff

        NOT-1-BSS_ : ∀ {s b}
                   → s ⊢ b ⇒₂b inj₂ ff
                   → s ⊢ inj₁ (¬₃ b) ⇒₂b inj₂ tt

        NOT-2-BSS_ : ∀ {s b}
                   → s ⊢ b ⇒₂b inj₂ tt
                   → s ⊢ inj₁ (¬₃ b) ⇒₂b inj₂ ff

        PARENTH-B-BSS : ∀ {s b v}
                      → s ⊢ b ⇒₂b v
                      → s ⊢ inj₁ ⟨ b ⟩₃ ⇒₂b v

        AND-1-BSS : ∀ {s b₁ b₂}
                  → s ⊢ b₁ ⇒₂b inj₂ tt
                  → s ⊢ b₂ ⇒₂b inj₂ tt
                  → s ⊢ inj₁ (b₁ ∧₃ b₂) ⇒₂b inj₂ tt

        AND-2-BSS : ∀ {s b₁ b₂}
                  → (s ⊢ b₁ ⇒₂b inj₂ ff)
                  ⊎ (s ⊢ b₂ ⇒₂b inj₂ ff)
                  → s ⊢ inj₁ (b₁ ∧₃ b₂) ⇒₂b inj₂ ff

    -- Section End Page 46


module Stm₂-semantic where
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
    open import Data.Bool using (Bool) renaming (true to tt; false to ff)
    open Aexp₂-semantic using (Aexp₂; Bexp₂; _⊢_⇒ₐ_; _⊢_⇒₂b_)

    -- Section Begin Page 47

    data Stm₂ : Set where
        skip₃ : Stm₂
        _←₃_ : Var → Aexp₂ ⊎ Num → Stm₂
        _Å₃_ : Stm₂ → Stm₂ → Stm₂
        ifStm₂_then_else_ : Bexp₂ ⊎ Bool → Stm₂ → Stm₂ → Stm₂
        while_do₃_ : Bexp₂ ⊎ Bool → Stm₂ → Stm₂

    data ⟨_,_⟩⇒₂_ : Stm₂ → State → State → Set where
        ASS-BSS         : ∀ {x a s v}
                        → s ⊢ a ⇒ₐ inj₂ v
                        → ⟨ (x ←₃ a) , s ⟩⇒₂ (s [ x ↦ v ])

        SKIP-BSS        : ∀ {s}
                        → ⟨ skip₃ , s ⟩⇒₂ s

        COMP-BSS        : ∀ {S₁ S₂ s s´ s˝}
                        → ⟨ S₁ , s ⟩⇒₂ s˝
                        → ⟨ S₂ , s˝ ⟩⇒₂ s´
                        → ⟨ (S₁ Å₃ S₂) , s ⟩⇒₂ s´

        IF-TRUE-BSS     : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₁ , s ⟩⇒₂ s´
                        → s ⊢ b ⇒₂b inj₂ tt
                        → ⟨ (ifStm₂ b then S₁ else S₂) , s ⟩⇒₂ s´

        IF-FALSE-BSS    : ∀ {S₁ S₂ s s´ b}
                        → ⟨ S₂ , s ⟩⇒₂ s´
                        → s ⊢ b ⇒₂b inj₂ ff
                        → ⟨ (ifStm₂ b then S₁ else S₂) , s ⟩⇒₂ s´

        WHILE-TRUE-BSS  : ∀ {S s s´ s˝ b}
                        → s ⊢ b ⇒₂b inj₂ tt
                        → ⟨ S , s ⟩⇒₂ s˝
                        → ⟨ (while b do₃ S) , s˝ ⟩⇒₂ s´
                        → ⟨ (while b do₃ S) , s ⟩⇒₂ s´

        WHILE-FALSE-BSS : ∀ {S s b}
                        → s ⊢ b ⇒₂b inj₂ ff
                        → ⟨ (while b do₃ S) , s ⟩⇒₂ s

    -- Section End Page 47

    -- Section Begin Page 53
    open import Data.Product using (_×_; _,_)
    data ⟨_⟩⇒₂⟨_⟩ : (Stm₂ × State) ⊎ State → (Stm₂ × State) ⊎ State → Set where
        ASSₛₛₛ : ∀ {x a v s}
               → s ⊢ a ⇒ₐ inj₂ v
               → ⟨ inj₁ (x ←₃ a , s) ⟩⇒₂⟨ inj₂ (s [ x ↦ v ]) ⟩

        SKIPₛₛₛ : ∀ {s}
                → ⟨ inj₁ (skip₃ , s) ⟩⇒₂⟨ inj₂ s ⟩

        COMP-1ₛₛₛ : ∀ {s s´ S₁ S₁´ S₂}
                  → ⟨ inj₁ (S₁ , s) ⟩⇒₂⟨ inj₁ (S₁´ , s´) ⟩
                  → ⟨ inj₁ (S₁ Å₃ S₂ , s) ⟩⇒₂⟨ inj₁ (S₁´ Å₃ S₂ , s´) ⟩

        COMP-2ₛₛₛ : ∀ {s s´ S₁ S₂}
                  → ⟨ inj₁ (S₁ , s) ⟩⇒₂⟨ inj₂ s´ ⟩
                  → ⟨ inj₁ (S₁ Å₃ S₂ , s) ⟩⇒₂⟨ inj₁ (S₂ , s´) ⟩

        IF-TRUEₛₛₛ : ∀ {s b S₁ S₂}
                   → s ⊢ b ⇒₂b inj₂ tt -- TODO right sides of some of these arrows assume the result is terminal value at inj2 instead of inj₁, which seems wrong
                   → ⟨ inj₁ (ifStm₂ b then S₁ else S₂ , s) ⟩⇒₂⟨ inj₁ (S₁ , s) ⟩

        IF-FALSEₛₛₛ : ∀ {s b S₁ S₂}
                    → s ⊢ b ⇒₂b inj₂ ff -- TODO right sides of some of these arrows assume the result is terminal value at inj2 instead of inj₁, which seems wrong
                    → ⟨ inj₁ (ifStm₂ b then S₁ else S₂ , s) ⟩⇒₂⟨ inj₁ (S₂ , s) ⟩

        WHILEₛₛₛ : ∀ {s b S}
                 → ⟨ inj₁ (while b do₃ S , s) ⟩⇒₂⟨ inj₁ (ifStm₂ b then S Å₃ (while b do₃ S) else skip₃ , s) ⟩

    ⟨_⟩⇒₂⟨_⟩-transition = ⌞ Γ , ⟨_⟩⇒₂⟨_⟩ , T ⌟
        where
            Γ = (Stm₂ × State) ⊎ State
            T : Γ → Set
            T (inj₁ x) = ⊥
            T (inj₂ y) = ⊤

    -- Imported via: open TransitionSystem ⟨_⟩⇒₂⟨_⟩-transition public

    -- Section End Page 53
