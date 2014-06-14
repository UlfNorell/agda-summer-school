
== Getting Started ==

Prerequisites: Haskell Platform, Emacs, git.

cabal install Agda
agda-mode setup

git clone https://github.com/UlfNorell/agda-prelude
git clone https://github.com/UlfNorell/agda-summer-school
cd agda-summer-school
git checkout EJCP

In emacs:
  M-x customize-group agda2
  Add path to agda-prelude/src to Include Directories

Open an Agda file and check that you have the Agda menu.
Hit C-c C-l to load the file.

== Exercises ==

Open exercises/Lists.agda and do the exercises inside.

...
