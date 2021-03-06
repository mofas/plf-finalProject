# Rule Derivation Language

You can find my slide here.

https://docs.google.com/presentation/d/1tt-JI24wW9j9pE_WUAUVhfyT2Pxlel-8WlimB4pv7l0/edit#slide=id.p

## Syntax

For simplicity, I don't define the rules in my language, all rules are predefiend and put in the context in advanced.

```agda
data Rule : Set where
  _⊢_∷_ : PremiseSet → String → String → Rule

-- D : [i j k -> x]
ruleD : Rule
ruleD = ( "k" , ( "j" , ("i" , □))) ⊢ "D" ∷ "x"
```

Expression is composed by two data type, `PremiseExp` and `Exp`.

```agda
data Exp : Set

data PremiseExp : Set where
  □   : PremiseExp
  _,_ : (String ⊎ Exp) → PremiseExp → PremiseExp

data Exp where
  App      : PremiseExp → RuleVar → Exp

exp1 : Exp
exp1 = (App
        (inj₁ "c" ,
        (inj₂ (App
                (inj₁ "b" ,
                (inj₁ "a" ,
                □))
              (Var "A")) ,
          □))
        (Var "D"))
```

## Type System

For all valid expressions, it has only one conclusion to return in the end. Therefore, it has only one type. However, we can also take the type system as a static check, to rule out some "invalid" expressions.

In my type system, I have only one type that call "valid" in type system. An expression need to satisify certain conditions to meet the "valid" type. For example, the number of the premises in "App" expression should be larger than that required by the rule.

## Operational Semantic

I do the big step and small step operational semantic for this language.

In big step, I implement an exception. If there is invalid rule application, then exception will arise.

In small step evaluation, I only implemented valid path, because implemented exception is quite tedious. Just like we do in the class, we need to bubble up the exception to the surface by adding new state transition for all existing cases.

Both implementation is the same, and you can the example of reduction in the slides I provide at beginning.

The whole implementation is at [PDL.agda](./PDL.agda)

## Extend language with properities

Now, I finish a language but it is not so interesting. Therefore, I try to add more thing into this language.

There are many other languages have similar derivation system like I did here, and they are more sophisticated and powerful. Prolog is a good example, it is a logic language which have a rule and unification system to solve logic complex relation.

For example, Prolog has the following syntax.

```
mortal(X) :- human(X)
```

It means "For a given X, X is mortal if X is human." In our language, we don't have universial variables to achieve this. It may be interesting if we could extend our language like this.

```
Rule mortal : ([x] -> ("mortal" x))
Rule human : ([x] -> ("human" x))
Rule humanIsMortal:  ([("human" x)] -> ("mortal" x))
```

In rule human: if you give me a premise x, then I will return a conclusion x is human.
In rule a: if you give me a premise x is human, then I will return a conclusion x is mortal.

That is to say, now conclusions or premises can have properties attached to them.

Let us see another complex example.

```
Rule parent : ([x y] -> ("parent" x y))
Rule male : ([z] -> ("male" z))
Rule father:  ([("parent" x y) ("male" x)] -> ("father" x y))
```

Now you can see the property "parent" could have two premises inside. It says :

In rule parent: if you give me premises x and y, then I will return a conclusion x is the parent of y.
In rule male: if you give me a premise z, then I will return a conclusion z is male.
In rule B: if your give me premise that "x is the parent of y" and "x is a male", then I will return a conclusion that "x is the father of y."

Now we can create an expression

```
parent("Vader", "Luke")
male("Vader")
father(x, "Luke")
```

It should return (`x = "Vader"`) in the ends.

However, execute such expressions will need unification, and that is hard to implement.
Therefore, we constraint our expression a little bit to let only return boolean in the end.

```
(
  [
    ["Vader" "Luke"] -> parent("Vader", "Luke")
    ["Vader"] -> male("Vader")
  ]
  -?
  father("Vader", "Luke")
)
```

The following is another example

```
Rule parent : ([x y] -> ("parent" x y))
Rule grandparent :  ([("parent" x y) ("parent" y z)] -> ("grandparent" x z))

(
  [
    ["John", "Mose"] -> parent("John", "Mose")
    ["Mose", "Inca"] -> parent("Mose", "Inca")
  ]
  ?-
  grandparent("Ada", "Inca")
)
```

It should return false.

For implementing such features, we will need more syntaxs.

### New Syntax

```
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
```

Now we will need relation and property in premise. With such syntax, we can represent `([x y] -> ("parent" x y)` by saying this premise's property is `parent` and that a binary relation between `x` and `y`.

In addition, in order to write fact and assumption. We will need the following syntax

```
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
```

### Check Mechanism

For this implementation, We can only do the shallow check. That is, we will find the rule that can generate the assumption, and instantiate the required premise by assumptions. Finally, we check if all instantiated premises are qualified by facts provided.

### Limitation

We don't do the recursively check and unification check here because they will cause non-terminating problem in Agda.

The whole implementation is at [PDL2.agda](./PDL2.agda)
