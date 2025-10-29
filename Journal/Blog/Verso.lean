import VersoManual
import Manual.Meta
open Verso Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Verso" =>

Here is some form of cheatsheet for verso.


# Markdown Syntax

Verso supports basic Markdown syntax:
* `*italic*` for _italic_
* `**bold**` for *bold*
* `(Mathlib docs)[https://leanprover-community.github.io/mathlib4_docs/index.html]` for [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/index.html)
* Headers follow the usual `#`, `##`, `###` syntax.
* Unordered lists are started with `* ` or `- ` as usual. Items on the same list must have the same indenttion. Ordered lists are started with `1. `, `2. ` etc.
* Description lists re as follows (note the indentation and breaklines):
  ```
  : Apple

    A fruit.

  : Banana

    Another fruit.
  ```
  : Apple

    A fruit.

  : Banana

    Another fruit.
* Quotations work as follows:
  ```
  > This is a quotation. Its end is determined by indentation.
  ```
  > This is a quotation. Its end is determined by indentation.


However, there is an imtant consideration. While standard Markdown will try its best to interprete erroneous code somehow, Verso usually gves n error message.

# Directives

For organiztion of text, as with `div`-tags in html, there are directives. They strt with `:::` (or more) colons. The keyword after `:::` must be defined somewhere, however.

```
:::«example» "one"
This is the first example.
:::
```

:::«example» "one"
This is the first example.
:::

# Docstrings and other lean code

One of the biggest advantages of Verso is that it can include docstrings from Lean code. This is done as follows:

```
{docstring Lean.Parser.Tactic.apply}
```
{docstring Lean.Parser.Tactic.apply}

Lean inline code as `2+2` is written like this:
```
`2+2`
```
Lean code block are similar, but start with three backticks and the `lean` keyword.

```lean (name := twoplustwo)
example : 2 + 2 = 4 :=
  by rfl
```

```lean (name := output)
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ 2
```

Illustrative examples are in expander boxes, as below:

::::keepEnv
:::example "Even Numbers"
Here is a simple calculation.

```lean
example: 2 + 2 = 4 := by rfl
```
:::
::::

# Commands

Commnds are single lines with `{...}`

`{include 0 MyChapter}`

# Images
This comman d`![Alt text](static/logo.png)` gives an image in the text.

![Alt text](static/logo.png)

# Mathematical formulae

```
Let us start simple, and write $`x_1, x_2,... \in ℝ`
for a real-valued sequence. In addition,
$$` \sum_{i=0}^n x_i`
is the sum of the first elements.
```

Let us start simple, and write $`x_1, x_2,... \in ℝ`
for a real-valued sequence. In addition,
$$` \sum_{i=0}^n x_i`
is the sum of the first elements.

How can I write a definition, lemma etc?

What is an easy way to make a link to a type?

# Error messages

Error messages might not always be helpful. For example, Mathlib notation might override notation introduced in Verso (e.g.\ for html).
