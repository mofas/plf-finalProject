#### Chung Yen Li

My idea of the final project is coming from an internship coding challenge.

It says something like following.

> You probably know that a general inference engine may carry out sort of reasoning by combining the knowledge encapsulated in a rule like `[[a b] -> c]`. It means given premise `a` and `b`, we can get conclusion `c`
>
> Given a set of two rules:
>
> `[[a b] -> c]`
>
> `[[c d e] -> f]`
>
> If we are given the premises `a` and `b`, we can derive `c` as the only resulting conclusion of the rule system. If we are given `a`, `b`, `d`, and `e`, we can use the fact that we can derive `c` to also derive `f`.

After finishing those challenges, I was thinking if we were given a set of rules, input premises, and an output conclusion, and we can verify if those input premises can produce the conclusion by checking all rules recursively until we get the conclusion or we cannot get anyone progress by applying rules.

I am curious if we can statically check if those inputs and rules are sufficient to produce the output conclusions before we running it, just like type system of language that can capture certain bugs before even running programs.

For example, if no rule can produce the conclusions, then we know there is no hope to produce conclusions; if initial premises are too few to apply any rule to get a new premie, then we can not get the conclusions either.

Maybe we can give premises and conclusions "type", and rules are functions that can map one type to another type, then we can do the type check.

To sum up, in my final project proposal, I will build a language to describe derivation, and a static semantic to quickly check if a derivation is legal or not.
