# tagless-staged

Notes from "Combinators for Impure yet Hygienic Code Generation" by Kameyama et al., adapted to a contemporary version of 'base' and 'template-haskell'.

This is a "tagless final" approach to implementing an embedded DSL (i.e. using typeclassed for encoding a higher-order abstract syntax). This approach has the benefit of being modular (since different interpretations might require different subsets of the API), and quite well suited to code generation.

Here we use :

* the Compose functor combinator, called 'J' in the paper 
* typed TH here to greatly simplify the code generation interpreter

paper : https://okmij.org/ftp/tagless-final/TaglessStaged/beyond.pdf

code : https://okmij.org/ftp/tagless-final/TaglessStaged/TSCore.hs


Also includes part the "reflection-reification" typeclass to enable simplification of terms by pattern matching, suitable for tagless DSLs : 

https://okmij.org/ftp/tagless-final/course/optimizations.html#circuit-tut

