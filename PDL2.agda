module PDL2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
  
open import Data.String
open import Data.Sum
open import Data.List hiding (_++_; drop)
open import Data.Bool.Base using (Bool; false; true; _∧_; if_then_else_)
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- for simplicity, we only define binary relation 
data Relation : Set where
  Unary  : String → Relation
  Binary : String → String → Relation

data Property : Set where
  Prop : String → Property
  
data Premise : Set where
  S : String → Premise
  P : Property → Relation → Premise  

data PremiseSet : Set where
  □   : PremiseSet
  _,_ : Premise → PremiseSet → PremiseSet


data RuleId : Set where
  Id     : String → RuleId

data Rule : Set where
  _⊢_∷_ : PremiseSet → RuleId → Premise → Rule


ruleParent : Rule
ruleParent = ((S "y") , ((S "x") , □)) ⊢ (Id "ruleParent") ∷ (P (Prop "parent") (Binary "x" "y"))



-- data Exp : Set
