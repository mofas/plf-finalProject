module PDL2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
  
open import Data.String
open import Data.Sum
open import Data.List hiding (_++_; drop)
open import Data.Bool.Base using (Bool; false; true; _∧_; if_then_else_)
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- for simplicity, we only define unary and binary relations 
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

data RuleCtx : Set where
  □ : RuleCtx
  _,_ : Rule → RuleCtx → RuleCtx


ruleParent : Rule
ruleParent = ((S "y") , ((S "x") , □)) ⊢ (Id "ruleParent") ∷ (P (Prop "parent") (Binary "x" "y"))

ruleMale : Rule
ruleMale = ((S "x") , □) ⊢ (Id "ruleMale") ∷ (P (Prop "male") (Unary "x"))


ruleFather : Rule
ruleFather = ((P (Prop "male") (Unary "x")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleFather") ∷ (P (Prop "father") (Binary "x" "y"))

ruleGrandparent : Rule
ruleGrandparent = ((P (Prop "parent") (Binary "y" "z")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleGrandparent") ∷ (P (Prop "grandparent") (Binary "x" "z"))


-- Example: ruleCtx
ctx1 : RuleCtx 
ctx1 = (ruleGrandparent , (ruleFather , (ruleMale , (ruleParent , □))))


data ParamSet : Set where
  □   : ParamSet
  _,_ : String → ParamSet → ParamSet
  
data Fact : Set where  
  App      : ParamSet → RuleId → Fact

data FactSet : Set where
  □   : FactSet
  _,_ : Fact → FactSet → FactSet

data Assumption : Set where
   Asump   : Premise → Assumption 

data Exp : Set where
  Check    : FactSet → Assumption → Exp

data VarMapping : Set where
  □   : VarMapping
  _>_,_ : String → String → VarMapping → VarMapping



-- (
--   [
--     ["Vader" "Luke"] -> parent("Vader", "Luke")
--     ["Vader"] -> male("Vader")
--   ]
--   ?-
--   father("Vader", "Luke")
-- )

-- fact 1
VaderIsLukeParent : Fact
VaderIsLukeParent = (App (("Luke" , ("Vader" , □))) (Id "ruleParent"))

-- fact 2
VaderIsMale : Fact
VaderIsMale = (App (("Vader" , □)) (Id "ruleMale"))

-- assumption
VaderIsLukeFather : Assumption
VaderIsLukeFather = (Asump (P (Prop "father") (Binary "Vader" "Luke")))


-- This expression is used to check the facts we have can infer our assumption 
checkVaderIsLukeFather : Exp
checkVaderIsLukeFather = (Check (VaderIsLukeParent , (VaderIsMale , □)) VaderIsLukeFather)

-- (
--   [
--     ["John", "Mose"] -> parent("John", "Mose")
--     ["Mose", "Inca"] -> parent("Mose", "Inca")
--   ]
--   ?-
--   grandparent("Ada", "Inca")
-- )


JohnIsMoseParent : Fact
JohnIsMoseParent = (App (("Mose" , ("John" , □))) (Id "ruleParent"))

MoseIsIncaParent : Fact
MoseIsIncaParent = (App (("John" , ("Inca" , □))) (Id "ruleParent"))

JohnIsAdaGrandparent : Assumption
JohnIsAdaGrandparent = (Asump (P (Prop "grandparent") (Binary "John" "Ada")))

JohnIsIncaGrandparent : Assumption
JohnIsIncaGrandparent = (Asump (P (Prop "grandparent") (Binary "John" "Inca")))

-- This one is false 
checkWithoutFact : Exp
checkWithoutFact = (Check □ JohnIsAdaGrandparent)

-- This one is false 
checkJohnIsAdaGrandparent : Exp
checkJohnIsAdaGrandparent = (Check (MoseIsIncaParent , (JohnIsMoseParent , □)) JohnIsAdaGrandparent)

-- This one is true
checkJohnIsIncaGrandparent : Exp
checkJohnIsIncaGrandparent = (Check (MoseIsIncaParent , (JohnIsMoseParent , □)) JohnIsIncaGrandparent)



data NotFind : Set where
  none : NotFind


lookup : RuleCtx → Premise → (Rule ⊎ NotFind)
lookup □ premise = inj₂ none
lookup ((require ⊢ id ∷ S x) , ctx) (S y) = if x == y then inj₁ (require ⊢ id ∷ S x) else (lookup ctx (S y))
lookup ((require ⊢ id ∷ P (Prop pr1) x) , ctx) (P (Prop pr2) y) =  if pr1 == pr2 then inj₁ (require ⊢ id ∷ P (Prop pr1) x) else (lookup ctx (P (Prop pr2) y)) 
lookup (_ , ctx) target = lookup ctx target

lookupEx1 : (Rule ⊎ NotFind)
lookupEx1 = lookup ctx1 (P (Prop "female") (Unary "y"))

lookupEx2 : (Rule ⊎ NotFind)
lookupEx2 = lookup ctx1 (P (Prop "father") (Binary "Vader" "Luke"))

lookupEx3 : (Rule ⊎ NotFind)
lookupEx3 = lookup ctx1 (P (Prop "grandparent") (Binary "John" "Inca"))

-- Quick check the relation fit with rule required
-- _≡Re_ : Relation → Relation → Bool
-- Unary x ≡Re Unary x₁ = true
-- Unary x ≡Re Binary x₁ x₂ = false
-- Binary x x₁ ≡Re Unary x₂ = false
-- Binary x x₁ ≡Re Binary x₂ x₃ = true 

-- data Relation : Set where
--   Unary  : String → Relation
--   Binary : String → String → Relation



-- we replace the relation in
-- Example: 
-- for rule : ((P (Prop "male") (Unary "x")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleFather") ∷ (P (Prop "father") (Binary "x" "y"))
-- assumption premise      : (Asump (P (Prop "father") (Binary "Vader" "Luke"))) 
-- PremiseSet              : ((P (Prop "male") (Unary "x")) , ((P (Prop "parent") (Binary "x" "y")) , □))
-- Relation in rule        : (P (Prop "father") (Binary "x" "y"))
-- Relation in assumption  : (P (Prop "father") (Binary "Vader" "Luke"))
-- We should get ((P (Prop "male") (Unary "Vader")) , ((P (Prop "parent") (Binary "Vader" "Luke")) , □)) in the end

 
GetVarMapping : Relation → Relation → VarMapping 
GetVarMapping (Unary x) (Unary y) =  x > y , □
GetVarMapping (Unary _) (Binary _ _) = □
GetVarMapping (Binary _ _) (Unary _) = □
GetVarMapping (Binary x₁ x₂) (Binary y₁ y₂) = ( x₂ > y₂ , (x₁ > y₁ , □))


-- Eg: Map x > Vadar , y > Luke
varMapping1 : VarMapping
varMapping1 = GetVarMapping (Binary "x" "y") (Binary "Vader" "Luke")

SubstituteVar : Premise → VarMapping → (Premise ⊎ NotFind)
SubstituteVar = {!!}

SubstitutePremiseSet : PremiseSet → VarMapping → (PremiseSet ⊎ NotFind)
SubstitutePremiseSet □ _ = inj₁ □
SubstitutePremiseSet (premise , set) map with (SubstituteVar premise map) | (SubstitutePremiseSet set map)
... | inj₁ premise' | inj₁ set' = inj₁ (premise' , set')
... | inj₂ x        | _         = inj₂ x
... | _             | inj₂ x    = inj₂ x



-- we simplify problem again, if we find our conclusion is a simple conclusion, and can be derived by a rule, then return true directly.
Derive : (Rule ⊎ NotFind) → Premise → Bool
Derive (inj₂ none) premise = false
Derive (inj₁ (premises ⊢ _ ∷ (S x))) (S y) = true

Derive (inj₁ (premises ⊢ _ ∷ (P pr1 re1))) (P pr2 re2) = let varMap = (GetVarMapping re1 re2) in {!!}
Derive _ _ = false


EvalExp : Exp → RuleCtx → Bool
EvalExp (Check factSet (Asump premise)) ctx = 
  let rule = (lookup ctx premise) in
    Derive rule premise
 
