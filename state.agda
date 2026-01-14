module state where

open import State

open import Data.List.Relation.Binary.Lex.Core using (this)
open import Data.Nat.Base using (_≤_; z≤n) renaming (s≤s to s≤s_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Integer using (+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _≟_; _<_)
open import Data.String.Properties using (_<?_)


p1 : emptyState [ "hi" ↦ + 3 ] ≡ (( "hi" , + 3) ∷ [] , sortedOne)
p1 = refl

F_ : ∀ {m n} → (m≤n : m ≤ n) → 8 + m ≤ 8 + n
F x = s≤s s≤s s≤s s≤s s≤s s≤s s≤s s≤s x

p2:1 : "hi" < "yo"
p2:1 = this (F F F F F F F F F F F F F s≤s z≤n)

p2 : ((emptyState [ "hi" ↦ + 3 ]) [ "yo" ↦ + 4 ]) ≡ (( "hi" , + 3) ∷ ( "yo" , + 4) ∷ [] , (sortedCons p2:1 sortedOne))
p2 = refl

p3 : emptyState [ "hi" ↦ + 3 ] [ "yo" ↦ + 4 ] ≡ emptyState [ "yo" ↦ + 4 ] [ "hi" ↦ + 3 ]
p3 = refl


a : State
a = (( "a" , + 0) ∷ ( "b" , + 0) ∷ [] , (sortedCons (this (s≤s F F F F F F F F F F F F s≤s z≤n)) sortedOne))

p4 : a [ "a" ↦ + 0 ] ≡ a
p4 = refl
