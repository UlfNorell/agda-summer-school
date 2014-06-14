
# Programming with Dependent Types

## Getting Started

### Prerequisites
- Haskell Platform
- Emacs
- git

### Installing Agda
- cabal install Agda
- agda-mode setup

### Getting the libraries
- git clone https://github.com/UlfNorell/agda-prelude
- git clone https://github.com/UlfNorell/agda-summer-school

### Set up Emacs paths
- M-x customize-group agda2
- Add path to agda-prelude/src to Include Dirs

### Check that it works
- Open agda-summer-school exercises/Main.agda in Emacs
- Hit C-c C-l to type check
- Hit C-c C-x C-x to compile
- You should now have an executable Main in exercises/
- Run ./Main example.lam. This should tell you that you haven't implemented TypeCheck.typeCheck.

## Exercises

### Warm-up exercises

- exercises/Lists.agda

### Lambda terms

- exercises/Term.agda
- exercises/TypeCheck.agda

### SECD machine

- exercises/SECD/StackSafe.agda
- exercises/SECD/WellTyped.agda
- exercises/SECD/Compiled.agda
