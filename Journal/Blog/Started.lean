/-
Copyright (c) 2025-2024 Peter Pfaffelhuber.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Pfaffelhuber
-/

import VersoBlog
open Verso Genre Blog

#doc (Page) "Infrastructure using mathlib" =>

When getting started with mathlib, one main issue is the new infrastructure, e.g. using `git`, using pull requests, setting up `vscode` etc.

# Using github and vscode
Mathlib PRs are now done using a forked repository. When you have this, regularly run the following, in order to keep mathlib up-to-date:
```
git checkout master
git fetch upstream
git merge upstream/master
git push origin master
```
