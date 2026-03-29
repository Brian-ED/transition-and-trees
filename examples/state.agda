module examples.state where

open import Data.Integer using (ℤ; +_)
open import Data.String using (String; _<_; _<?_; _==_)
open import State ℤ String _<_ _<?_ _==_

open import Data.List.Relation.Binary.Lex using (this)
open import Data.Nat.Base using (_≤_; z≤n) renaming (s≤s to s≤s_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using ([]; _∷_)
open import Data.String using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

p1 : emptyState [ "hi" ↦ + 3 ] ≡ (( "hi" , + 3) ∷ [] , sortedOne)
p1 = refl

NSize : {m : ℕ} (n : ℕ) → n ≤ n + m
NSize 0 = z≤n
NSize (ℕ.suc n) = s≤s (NSize n)

p2 : (emptyState [ "hi" ↦ + 3 ] [ "yo" ↦ + 4 ]) ≡ (( "hi" , + 3) ∷ ( "yo" , + 4) ∷ [] , sortedCons (this (NSize 105)) sortedOne)
p2 = refl

p3 : emptyState [ "hi" ↦ + 3 ] [ "yo" ↦ + 4 ] ≡ emptyState [ "yo" ↦ + 4 ] [ "hi" ↦ + 3 ]
p3 = refl

a : State
a = ( "a" , + 0) ∷ ( "b" , + 0) ∷ [] , sortedCons (this (NSize 98)) sortedOne

p4 : a [ "a" ↦ + 0 ] ≡ a
p4 = refl
