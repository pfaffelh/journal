/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Journal
import VersoBlog

open Verso Genre Blog Site Syntax

def journal : Site := site Journal.Blog.Front /
  static "static" ← "Journal/Blog/static"
  "post001" Journal.Blog.Started
  "postBasics" Journal.Blog.Basics
  "post002" Journal.Blog.DoProbability
  "post003" Journal.Blog.Filters


def main := blogMain theme journal (linkTargets := linkTargets)
