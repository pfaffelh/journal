/-
Copyright (c) 2025 Peter Pfaffelhuber.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Pfaffelhuber
-/

import VersoBlog
open Verso Genre Blog

#doc (Page) "Infrastructure using mathlib" =>

When getting started with mathlib, one main issue is the new infrastructure, e.g. using `git`, using pull requests, setting up `vscode` etc.

# Setting up upstream
git remote add upstream https://github.com/leanprover-community/mathlib4.git

Install the github issues and prs extension in vscode




# Using github and vscode
Mathlib PRs are now done using a forked repository. When you have this, regularly run the following, in order to keep mathlib up-to-date:


## Using git on the command line, reduce merge conflicts

In general, there is `origin`, which is my fork, and `upstream`, which is `mathlib` from `leanprover-community`.

Make sure master is the same on the fork and upstream:
```
git checkout master
git fetch upstream
git rebase upstream/master
```

Now the work on the feature-branch:
```
git checkout my-new-feature-branch
git rebase master (Resolve conflicts, see below)
git push --force-with-lease origin my-new-feature-branch
```
After resolving conflicts for a commit, use git add ., and git rebase --continue

Caution: If your branch is shared, this is dangerous.
