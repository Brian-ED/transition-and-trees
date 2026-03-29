open import Relation.Binary.Core using (Rel)
open import Level using (Level)
open import Relation.Binary.Definitions using (Decidable)
open import Data.Bool using (if_then_else_; Bool)

module State
    (𝕍 : Set)
    (ID : Set)
    (_<_ : Rel ID Level.0ℓ)
    (_<?_ : Decidable _<_)
    (_==_ : ID → ID → Bool)
    where

open import Data.Product using (Σ; _×_; _,_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes)
open import Data.List using (List; []; _∷_)


data Sorted : List (ID × 𝕍) → Set where
    sortedNil  : Sorted []
    sortedOne  : ∀ {x} → Sorted (x ∷ [])
    sortedCons : ∀ {s1 n1 s2 n2 xs}
               → s1 < s2
               → Sorted ((s2 , n2) ∷ xs)
               → Sorted ((s1 , n1) ∷ (s2 , n2) ∷ xs)

State = Σ (List (ID × 𝕍)) Sorted

--infixr 12 _[_↦_]

_[_↦_] : State
       → ID
       → 𝕍
       → State
([] , _) [ s ↦ n ] = (s , n) ∷ [] , sortedOne
((s₁ , _ ) ∷ [] , _) [ s ↦ _ ] with s <? s₁ | s₁ <? s
((s₁ , n₁) ∷ [] , _) [ s ↦ n ]    | yes a   | _     = (s , n) ∷ (s₁ , n₁) ∷ [] , sortedCons a sortedOne
((s₁ , n₁) ∷ [] , _) [ s ↦ n ]    | _       | yes a = (s₁ , n₁) ∷ (s , n) ∷ [] , sortedCons a sortedOne
((s₁ , _ ) ∷ [] , _) [ _ ↦ n ]    | _       | _     = (s₁ , n) ∷ [] , sortedOne

-- I need to prove that the first element of a sorted list is the lowest, and that s is heigher or equal to that element, and also that s and s1 aren't equal.
-- The first of these is hard.
-- Second of these is easy: via the already supposed (s₁ ≤ s) (`s <? s₁`'s `because ofⁿ` branch).
-- Third needs another case created.
-- →→ first element of f has to be larger than s₁
-- Using this I can prove the current goal `Sorted ((s₁ , n₁) ∷ f)`

-- s1 < is₁ ≤ s

(            (s₁ , _ ) ∷ xs , sortedCons _ b) [ s ↦ n ] with (xs , b) [ s ↦ n ]   | s <? s₁
(            xs             , pp            ) [ s ↦ n ]    | _                    | yes a = (s  , n ) ∷ xs , sortedCons a pp
(            (s₁ , n₁) ∷ _  , _             ) [ s ↦ n ]    | [] , g               | _     = (s₁ , n) ∷ [] , sortedOne
((s₁ , n₁) ∷ (s₂ , n₂) ∷ _ , _              ) [ s ↦ n ]    | (is₁ , in₁) ∷ f , pp | _ with s₁ <? is₁
((s₁ , n₁) ∷ (s₂ , n₂) ∷ _ , _              ) [ s ↦ n ]    | (is₁ , in₁) ∷ f , pp | _    | yes aa = (s₁ , n₁) ∷ (is₁ , in₁) ∷ f , sortedCons aa pp
_                                             [ _ ↦ _ ]    | f                    | _    | _      = f -- The keys of first elem match with the new one, so just throw the old key away

emptyState : State
emptyState = [] , sortedNil

lookup : State → ID → Maybe 𝕍
lookup ([] , sortedNil) x = nothing
lookup ((v , i) ∷ rest , sortedOne      ) x = if x == v then just i else nothing
lookup ((v , i) ∷ rest , sortedCons x₁ p) x = if x == v then just i else lookup (rest , p) x
