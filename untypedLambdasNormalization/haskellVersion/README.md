# UNP

An algorithm that constracts traversals for and arbitrary term from untyped lambda calculus

## System Requirements
* ghc
* 'make' utility
* LaTex

## Run instruction
* Normalization only
- Run 'make normalize' in terminal
- Open file 'examplesNormalForms.pdf'
* Write traversal in pdf
- Run 'make generate_traversals' in terminal
- Open file 'examples.pdf'

### Comments
* Make file uses xelatex by default. If you prefer another one then open makefile and replace all occurence of xelatex by whatever you'd prefer

### How to run on new example

The syntax of input term is as follows L = var | \ var . L | L @ L

* Open file Examples.hs
* Add your example (<example_name> = <term_as_string>)
* Add <example_name> to list 'examples'
* Run make in terminal
* Your example has to appear in examples.pdf file