# Documentation #

py-prop-logic is an implementation of the back-tracking algorithm for propositional logic described in Russel and Norvig's "Artificial Intelligence a Modern Approach".
It implements negation as failure through the special keyword "Not(...)".

NOTE: There is very little error handling, so use it with care.

## Installation ##

There is nothing to install. Download the source file from the repository and put it in your project.
You can then import the classes from the "prop\_logic" module.


## Usage ##
This project implements a knowledge base in the class FolKB. This class has three methods:
- Tell
- Ask
- Retract
This project also implements help classes and a back tracking mechanism.

Special operator names:

"Not" - Implements negation as failure

"Eq" - Implements binary equality

### Some hints ###
General usage is shown in the source file through several examples.

In general, you first need to tell the knowledge base some rules and some facts.
Rules are indicated by an implication arrow, like
```
"Parent(x,y) -> Offspring(y,x)"
"Parent(x,y) & Female(x) -> Mother(x,y)"
"Parent(y,x) & Parent(z,y) -> Grandparent(z,x)"
"Not(Male(x)) -> Female(x)"
```

Facts do not have implication arrows, like
```
"Parent(Pam,Bob)"
"Male(Tom)"
```

There are three types of objects in this implementation (as of yet).
- Variables start with a lower case letter. In the examples above, "x","y" and "z" are used.
- Constants start with an upper case letter. In the examples above, "Pam", "Bob" and "Tom" are used.
- Predicates start with an upper case letter and have arguments. In the examples above, "Parent(x,y)", "Female(x)" and "Not(Male(x))" are used.

"Not" is a special keyword which indicates that the argument predicate should Not be fulfilled in the KB for the matching to succeed.

After you have told the knowledge base some facts, you can start asking questions. There are two general types of questions. Those that can be answered with "True/False" and those that can have several answers.
To ask a question of the first kind, you use the FolKB.ask method with an expression like
"Female(Jim)" -> The method returns a False in the example
"Male(Jim)" -> The method returns a True in the example
To ask a question of the second kind, you use expressions of the form:
"Male(x)" -> The method returns an iterator with the results
"Parent(x,y)"

A short code snippet to clarify usage of ask
```
for res_dict in myKB.ask("Parent(x,y)"):
    print "x=%s, y=%s" % (res_dict["x"],res_dict["y"])
```
You can interlieve telling, retracting and asking within your python program to use the propositional logic engine.

See the source file for more examples.