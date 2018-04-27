module PDL where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
  
open import Data.String
open import Data.Sum
open import Data.List hiding (_++_; drop)

open import Data.Bool.Base using (Bool; false; true; _∧_; if_then_else_)

open import Relation.Nullary
open import Relation.Nullary.Decidable

data Exp : Set

data PremiseSet : Set where
  □   : PremiseSet
  _,_ : String → PremiseSet → PremiseSet

data RuleVar : Set where
  Var     : String → RuleVar

data Rule : Set where
  _⊢_∷_ : PremiseSet → String → String → Rule

-- Expr
data PremiseExp : Set where
  □   : PremiseExp
  _,_ : (String ⊎ Exp) → PremiseExp → PremiseExp

data Exp where
  App      : PremiseExp → RuleVar → Exp

data RuleCtx : Set where
  □ : RuleCtx
  _,_ : Rule → RuleCtx → RuleCtx


-- Example: set
  setAB : PremiseSet
setAB = ( "b" , ("a" , □))

setBC : PremiseSet
setBC = ( "c" , ("b" , □))

setAC : PremiseSet
setAC = ( "c" , ("a" , □))

setABC : PremiseSet
setABC = ("c" , ( "b" , ("a" , □)))


-- Example: rules
-- A : a b ∷ i
ruleA : Rule
ruleA = setAB ⊢ "A" ∷ "i"

-- B : a c ∷ j 
ruleB : Rule
ruleB = setAC ⊢ "B" ∷ "j"

-- C : b c ∷ k
ruleC : Rule
ruleC = setBC ⊢ "C" ∷ "k"

-- D : i j k ∷ x 
ruleD : Rule
ruleD = ( "k" , ( "j" , ("i" , □))) ⊢ "D" ∷ "x"



-- Example: exp
-- ([a, b] A)
exp1 : Exp
exp1 = (App (inj₁ "b" , ( inj₁ "a" , □)) (Var "A"))

-- ([a, c] B)
exp2 : Exp
exp2 = (App (inj₁ "c" , ( inj₁ "a" , □)) (Var "B"))

-- ([b, c] C)
exp3 : Exp
exp3 = (App (inj₁ "c" , ( inj₁ "b" , □)) (Var "C"))

-- ( [([a, b] A), ([a, c] B), ([b, c] C)] D)
exp4 : Exp
exp4 = (App (inj₂ exp3 , (inj₂ exp2 , ( inj₂ exp1 , □))) (Var "D"))


-- ( [([a, b] A), ([a, c] B), ([b, c] C)] D)
exp4' : Exp
exp4' = (App (inj₂ exp2 , ( inj₂ exp1 , □)) (Var "D"))


-- Example: ruleCtx
ctx1 : RuleCtx 
ctx1 = (ruleD , (ruleC , (ruleB , (ruleA , □))))


-- Type


data Typ : Set where
  Valid    : Typ

LengthPremisesExp : PremiseExp → ℕ
LengthPremisesExp □ = zero
LengthPremisesExp (x , exp) = suc (LengthPremisesExp exp)

LengthPremisesSet : PremiseSet → ℕ
LengthPremisesSet □ = zero
LengthPremisesSet (x , exp) = suc (LengthPremisesSet exp)


data _Set⊢_Set::_ : RuleCtx → PremiseExp → Typ → Set

data _App⊢_App::_ : RuleCtx → Exp → Typ → Set where  
  AppT : ∀ {require premises x c ctx} →
    ctx Set⊢ premises Set:: Valid →
    (require ⊢ x ∷ c) ∈ ctx → 
    (LengthPremisesSet require) ≤ (LengthPremisesExp premises) → 
    ctx App⊢ (App premises (Var x)) App:: Valid
  
data _Set⊢_Set::_ where
  EmptyT  : ∀ {ctx} → ctx Set⊢ □ Set:: Valid
  
  ExtendStrT : ∀ {set ctx} {s : String} → ctx Set⊢ set Set:: Valid →
    ctx Set⊢ (inj₁ s , set) Set:: Valid
    
  ExtendExpT : ∀ {e set ctx} → ctx App⊢ e App:: Valid → ctx Set⊢ set Set:: Valid →
    ctx Set⊢ (inj₂ e , set) Set:: Valid 


expSetABT : ctx1 Set⊢ (inj₁ "b" , ( inj₁ "a" , □)) Set:: Valid
expSetABT =  ExtendStrT (ExtendStrT EmptyT)

LengthAB≤ : (LengthPremisesSet ( "b" , ("a" , □))) ≤ (LengthPremisesExp (inj₁ "b" , ( inj₁ "a" , □)))
LengthAB≤ = s≤s (s≤s z≤n)

expABT : ctx1 App⊢ (App (inj₁ "b" , ( inj₁ "a" , □)) (Var "A")) App:: Valid
expABT = (AppT expSetABT ruleA∈ctx1 LengthAB≤)

expACT : ctx1 App⊢ (App (inj₁ "c" , ( inj₁ "a" , □)) (Var "B")) App:: Valid
expACT = (AppT (ExtendStrT (ExtendStrT EmptyT)) ruleB∈ctx1 (s≤s (s≤s z≤n)))

expBCT : ctx1 App⊢ (App (inj₁ "c" , ( inj₁ "b" , □)) (Var "C")) App:: Valid
expBCT = (AppT (ExtendStrT (ExtendStrT EmptyT)) ruleC∈ctx1 (s≤s (s≤s z≤n)))

exp4T : ctx1 App⊢ (App (inj₂ exp3 , (inj₂ exp2 , ( inj₂ exp1 , □))) (Var "D")) App:: Valid
exp4T = (AppT (ExtendExpT expBCT (ExtendExpT expACT (ExtendExpT expABT EmptyT))) ruleD∈ctx1 (s≤s (s≤s (s≤s z≤n))))







-- Operational Semantic

-- Big step

data Exception : Set where
  fail : RuleVar → Exception

-- Lookup the rule from ruleCtx
lookup : RuleCtx → String → Rule
lookup □ key = (□ ⊢ key ∷ "no rule find") 
lookup ((set ⊢ x ∷ conclusion) , ctx) key =  if x == key then (set ⊢ x ∷ conclusion) else (lookup ctx key)

-- Check a premise is in the premise set
isExisted : String → PremiseSet → Bool
isExisted x □ = false
isExisted x (y , ys) =  if x == y then true else isExisted x ys  

-- Check one premise set is the subset of another premise set
isSubset : PremiseSet → PremiseSet → Bool 
isSubset □ _ = true
isSubset (x , xs) ys =  isExisted x ys ∧ isSubset xs ys


EvalExp : Exp → RuleCtx → (String ⊎ Exception)

-- Eval PremiseExp 
EvalPremises : PremiseExp → RuleCtx → (PremiseSet ⊎ Exception) 
EvalPremises □ ctx = inj₁ □
EvalPremises (inj₁ str , exp) ctx with EvalPremises exp ctx
... | inj₁ set = inj₁ (str , set)
... | inj₂ exc = inj₂ exc 
EvalPremises (inj₂ e , exp) ctx with (EvalExp e ctx) | EvalPremises exp ctx
... | inj₁ str | inj₁ set = inj₁ (str , set) 
... | inj₁ str | inj₂ exc = inj₂ exc 
... | inj₂ exc | _ = inj₂ exc 

-- Check rule application is legal
CheckRule : Rule → (PremiseSet ⊎ Exception) → (String ⊎ Exception)
CheckRule (requireSet ⊢ ruleVar ∷ conclusion) (inj₁ currentSet) =
  if (isSubset requireSet currentSet)
  then (inj₁ conclusion)
  else (inj₂ (fail (Var ruleVar))) 
CheckRule rule (inj₂ exc) = inj₂ exc

-- Eval rule
EvalExp (App premises (Var x)) ctx = 
 let rule = (lookup ctx x) in
   let evalSet = (EvalPremises premises ctx) in
    (CheckRule rule evalSet)

-- Example : 
-- evalexp4 : (String ⊎ Exception)
-- evalexp4 = EvalExp exp4 ctx1

-- evalexp4' : (String ⊎ Exception)
-- evalexp4' = EvalExp exp4' ctx1



-- Small step

-- For simplicity, we assume PremiseSet is always sorted.
-- In lookup, we also don't need {α : False (s ≟ s')}
-- In addition, we don't need to isExisted type here.

-- lookup
data _∈_ : Rule → RuleCtx → Set where
  here : ∀ {ρ s p c} → (p ⊢ s ∷ c) ∈ ((p ⊢ s ∷ c) , ρ)
  skip : ∀ {ρ s s' p p' c c'} → (p ⊢ s ∷ c) ∈ ρ → (p ⊢ s ∷ c) ∈ ((p' ⊢ s' ∷ c') , ρ)


-- isExisted
-- infix 10 _∈_
-- data _∈set_ (x : String) : PremiseSet -> Set where
--   hd : ∀ {xs} -> x ∈set (x , xs)
--   tl : ∀ {y xs} -> x ∈set xs -> x ∈set (y , xs)

-- isSubset
infix 20 _⊆_
data _⊆_ : PremiseSet -> PremiseSet -> Set where
  stop : □ ⊆ □
  drop : ∀ {xs y ys} -> xs ⊆ ys -> xs ⊆ (y , ys)
  keep : ∀ {x xs ys} -> xs ⊆ ys -> (x , xs) ⊆ (x , ys)


data Frame : Set where
  EvalK        : RuleVar → Frame
  PremiseStrK  : String → Frame
  PremiseExpK  : Exp → Frame
  PremiseExpS  : PremiseSet → Frame
  
  CheckRuleK   : PremiseSet → PremiseSet → String → Frame
  -- ApplyRuleK   : PremiseSet → Frame
  
  

Cont : Set
Cont = List Frame


data State : Set where
  EnterEvalRule     : Exp → RuleCtx → Cont → State
  EnterEvalPremise  : PremiseExp → RuleCtx → Cont → State
  ReturnEvalPremise : Cont → RuleCtx → State
  ReturnPremiseSet  : PremiseSet → RuleCtx → Cont → State
  EnterCheckRule    : RuleCtx → Cont → State 
  ReturnEvalRule    : String → RuleCtx → Cont → State

 
data _↦_ : State → State → Set where
  AppE   : ∀ {premises x ρ κ} →
    (EnterEvalRule (App premises (Var x)) ρ κ) ↦
    (EnterEvalPremise premises ρ ((EvalK (Var x)) ∷ κ))
    
  EvalPreStr : ∀ {s rest ρ κ} →
    (EnterEvalPremise (inj₁ s , rest) ρ κ) ↦
    (EnterEvalPremise rest ρ ((PremiseStrK s) ∷ κ))

  EvalPreExp : ∀ {exp rest ρ κ} →
    (EnterEvalPremise (inj₂ exp , rest) ρ κ) ↦
    (EnterEvalPremise rest ρ ((PremiseExpK exp) ∷ κ))
    
  EvalPreK : ∀ {ρ κ} →
    (EnterEvalPremise □ ρ κ) ↦ (ReturnEvalPremise κ ρ)
  EvalPreS : ∀ {ρ κ} →
    (ReturnEvalPremise κ ρ) ↦ (ReturnPremiseSet □ ρ κ) 
  EvalPreStrK : ∀ {set s ρ κ} →
    (ReturnPremiseSet set ρ ((PremiseStrK s) ∷ κ)) ↦ 
    (ReturnPremiseSet (s , set) ρ κ)
    
  EvalPreExpK : ∀ {set exp ρ κ} →
    (ReturnPremiseSet set ρ ((PremiseExpK exp) ∷ κ)) ↦ 
    (EnterEvalRule exp ρ ((PremiseExpS set) ∷ κ))    
  EvalPreExpS : ∀ {set conclusion ρ κ} →
    (ReturnEvalRule conclusion ρ ((PremiseExpS set) ∷ κ)) ↦
    (ReturnPremiseSet (conclusion , set) ρ κ)

  AppK : ∀ {current require x conclusion ρ κ} →
    ((require ⊢ x ∷ conclusion) ∈ ρ)  →
    (ReturnPremiseSet current ρ ((EvalK (Var x)) ∷ κ)) ↦ 
    (EnterCheckRule ρ ((CheckRuleK current require conclusion) ∷ κ))

  AppS : ∀ {current require conclusion ρ κ} →
    require ⊆ current →
    (EnterCheckRule ρ ((CheckRuleK current require conclusion) ∷ κ)) ↦ 
    (ReturnEvalRule conclusion ρ κ)




infixr 10 _•_

data _↦*_ : State → State → Set where
  ∎   : ∀ {s} → s ↦* s
  _•_ : ∀ {s₁ s₂ s₃} → s₁ ↦ s₂ → s₂ ↦* s₃ → s₁ ↦* s₃


Eval : Exp → RuleCtx → String → Set
Eval e ρ c = ((EnterEvalRule e) ρ []) ↦* (ReturnEvalRule c ρ [])


-- Example : lookup
ruleA∈ctx1 : ruleA ∈ ctx1
ruleA∈ctx1 = skip (skip (skip here))

ruleB∈ctx1 : ruleB ∈ ctx1
ruleB∈ctx1 = skip (skip here)

ruleC∈ctx1 : ruleC ∈ ctx1
ruleC∈ctx1 = skip here

ruleD∈ctx1 : ruleD ∈ ctx1
ruleD∈ctx1 = here


-- Example : subset
setAB⊆setAB : setAB ⊆ setAB
setAB⊆setAB = keep (keep stop)

setAB⊆setABC : setAB ⊆ setABC
setAB⊆setABC = drop (keep (keep stop))


-- Example : Eval
evalE1 : Eval exp1 ctx1 "i"
evalE1 = AppE • EvalPreStr • EvalPreStr • EvalPreK • EvalPreS • EvalPreStrK • EvalPreStrK • (AppK ruleA∈ctx1) • (AppS setAB⊆setAB) • ∎ 



-- Full example for chain
-- E : m ∷ n 
ruleE : Rule
ruleE = ("m" , □) ⊢ "E" ∷ "n"

ruleF : Rule
ruleF = ("n" , □) ⊢ "F" ∷ "o"

ctx2 : RuleCtx
ctx2 = (ruleF , (ruleE , □))

exp5 : Exp
exp5 = (App (inj₂ (App ((inj₁ "m") , □) (Var "E")) , □) (Var "F"))

ruleE∈ctx2 : ruleE ∈ ctx2
ruleE∈ctx2 = skip here

ruleF∈ctx2 : ruleF ∈ ctx2
ruleF∈ctx2 = here

setM⊆setM : ("m" , □) ⊆ ("m" , □)
setM⊆setM = keep stop

setN⊆setN : ("n" , □) ⊆ ("n" , □)
setN⊆setN = keep stop

 
evalE2 : Eval exp5 ctx2 "o"
evalE2 = AppE • EvalPreExp • EvalPreK • EvalPreS • EvalPreExpK • AppE • EvalPreStr • EvalPreK • EvalPreS • EvalPreStrK • (AppK ruleE∈ctx2) • (AppS setM⊆setM) • EvalPreExpS • (AppK ruleF∈ctx2) • (AppS setN⊆setN) • ∎ 


