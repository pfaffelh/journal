/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import Journal

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    let postList :=
      match (← param? "posts") with
      | none => Html.empty
      | some html => {{ <h2> "Posts" </h2> }} ++ html
    let catList :=
      match (← param? (α := Post.Categories) "categories") with
      | none => Html.empty
      | some ⟨cats⟩ => {{
          <div class="category-directory">
            <h2> "Categories" </h2>
            <ul>
            {{ cats.map fun (target, cat) =>
              {{<li><a href={{target}}>{{Post.Category.name cat}}</a></li>}}
            }}
            </ul>
          </div>
        }}
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="light dark"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{{ (← param (α := String) "title") }} " — Verso "</title>
          <link rel="stylesheet" href="/static/style.css"/>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            <a class="logo" href="/"><h1>"Some experiences with mathlib"</h1></a>
            {{ ← topNav }}
            </div>
          </header>
          <main>
            <div class="wrap">
              {{ (← param "content") }}
              {{ postList }}
              {{ catList }}
            </div>
          </main>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩


def journal : Site := site Journal.Blog.Front /
  static "static" ← "Journal/Blog/static"
  "post001" Journal.Blog.Started
  "postBasics" Journal.Blog.Basics
  "post002" Journal.Blog.DoProbability


def linkTargets : Code.LinkTargets TraverseContext where
  const n _ := #[{shortDescription := "doc", description := s!"Documentation for {n}", href := s!"http://site.example/constlink/{n}"}]
  definition d _ := #[{shortDescription := "def", description := "Definition", href := s!"http://site.example/deflink/{d}"}]

def main := blogMain theme journal (linkTargets := linkTargets)
