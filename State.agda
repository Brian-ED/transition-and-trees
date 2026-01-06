module State where
open import Data.Product using (Σ; _×_; _,_)
open import Data.Integer using (+_; ℤ)
open import Data.String using (String; _≟_; _<_)
open import Data.String.Properties using (_<?_)
open import Agda.Builtin.String using () renaming (primStringEquality to _==Str_)
open import Data.Bool using (Bool; true; false; if_then_else_) renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; _because_; Reflects; ofʸ; ofⁿ)
open import Data.List using (List; []; _∷_)

data Sorted : List (String × ℤ) → Set where
  sortedNil  : Sorted []
  sortedOne  : ∀ {x} → Sorted (x ∷ [])
  sortedCons : ∀ {s1 n1 s2 n2 xs}
             → s1 < s2
             → Sorted ((s2 , n2) ∷ xs)
             → Sorted ((s1 , n1) ∷ (s2 , n2) ∷ xs)

State = Σ (List (String × ℤ)) Sorted

--infixr 12 _[_↦_]

_[_↦_] : State
       → String
       → ℤ
       → State
([] , sortedNil) [ s ↦ n ] = (s , n) ∷ [] , sortedOne
((s₁ , n₁) ∷ [] , sortedOne) [ s ↦ n ] with s <? s₁         | s₁ <? s
((s₁ , n₁) ∷ [] , sortedOne) [ s ↦ n ]    | _ because ofʸ a | _ = (s , n) ∷ (s₁ , n₁) ∷ [] , sortedCons a sortedOne
((s₁ , n₁) ∷ [] , sortedOne) [ s ↦ n ]    | _ because ofⁿ _ | _ because ofⁿ _ = ((s₁ , n) ∷ []) , sortedOne
((s₁ , n₁) ∷ [] , sortedOne) [ s ↦ n ]    | _ because ofⁿ _ | _ because ofʸ a = ((s₁ , n₁) ∷ (s , n) ∷ []) , sortedCons a sortedOne

-- I need to prove that the first element of a sorted list is the lowest, and that s is heigher or equal to that element, and also that s and s1 aren't equal.
-- The first of these is hard.
-- Second of these is easy: via the already supposed (s₁ ≤ s) (`s <? s₁`'s `because ofⁿ` branch).
-- Third needs another case created.
-- →→ first element of f has to be larger than s₁
-- Using this I can prove the current goal `Sorted ((s₁ , n₁) ∷ f)`

-- s1 < is₁ ≤ s

(            (s₁ , _ ) ∷ xs , sortedCons _ b) [ s ↦ n ] with (xs , b) [ s ↦ n ]   | s <? s₁
(            (s₁ , n₁) ∷ _  , _             ) [ s ↦ n ]    | [] , g               | _ because ofⁿ _ = (s₁ , n) ∷ [] , sortedOne
(            xs             , pp            ) [ s ↦ n ]    | _                    | _ because ofʸ a = (s  , n ) ∷ xs , sortedCons a pp
((s₁ , n₁) ∷ (s₂ , n₂) ∷ xs , sortedCons p b) [ s ↦ n ]    | (is₁ , in₁) ∷ f , pp | _ because ofⁿ _ with s₁ <? is₁
_                                             [ _ ↦ _ ]    |               f      | _ because ofⁿ _    | _ because ofⁿ _ = f -- The keys of first elem match with the new one, so just throw the old key away
((s₁ , n₁) ∷ (s₂ , n₂) ∷ xs , sortedCons p b) [ s ↦ n ]    | (is₁ , in₁) ∷ f , pp | _ because ofⁿ _    | _ because ofʸ aa = (s₁ , n₁) ∷ (is₁ , in₁) ∷ f , sortedCons aa pp

emptyState : State
emptyState = [] , sortedNil

open import Relation.Binary.PropositionalEquality         public using (_≡_; refl; cong)

p1 : emptyState [ "hi" ↦ + 3 ] ≡ (( "hi" , + 3) ∷ [] , sortedOne)
p1 = refl

open import Data.List.Relation.Binary.Lex.Core using (this)
open import Data.Nat.Base using (_≤_; z≤n) renaming (s≤s to s≤s_)
open import Data.Nat using (ℕ; zero; suc; _+_)

--repeat : {m n g : ℕ} → (r : ℕ) → m ≤ n → zero ≤ g
--repeat zero x = z≤n
--repeat (suc r) x = (repeat r) (s≤s x)

F_ : ∀ {m n} → (m≤n : m ≤ n) → 8 + m ≤ 8 + n
F x = s≤s s≤s s≤s s≤s s≤s s≤s s≤s s≤s x

p2:1 : "hi" < "yo"
p2:1 = this (F F F F F F F F F F F F F s≤s z≤n)

p2 : ((emptyState [ "hi" ↦ + 3 ]) [ "yo" ↦ + 4 ]) ≡ (( "hi" , + 3) ∷ ( "yo" , + 4) ∷ [] , (sortedCons p2:1 sortedOne))
p2 = refl

p3 : emptyState [ "hi" ↦ + 3 ] [ "yo" ↦ + 4 ] ≡ emptyState [ "yo" ↦ + 4 ] [ "hi" ↦ + 3 ]
p3 = refl

lookup : String → State → Maybe ℤ
lookup x ([] , sortedNil) = nothing
lookup x ((v , i) ∷ rest , sortedOne      ) = if x ==Str v then just i else nothing
lookup x ((v , i) ∷ rest , sortedCons x₁ p) = if x ==Str v then just i else lookup x (rest , p)

a : State
a = (( "a" , + 0) ∷ ( "b" , + 0) ∷ [] , (sortedCons (this (s≤s F F F F F F F F F F F F s≤s z≤n)) sortedOne))

p4 : a [ "a" ↦ + 0 ] ≡ a
p4 = refl
