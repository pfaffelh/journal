import Journal
import VersoManual
import Manual.Meta

open Verso.Genre Manual

open Verso.Output.Html in
def searchModule := {{
    <script type="module" src="/static/search/search-init.js"></script>
  }}

def KaTeXLicense : LicenseInfo where
  identifier := "MIT"
  dependency := "KaTeX"
  howUsed := "KaTeX is used to render mathematical notation."
  link := "https://katex.org/"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (c) 2013-2020 Khan Academy and other contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"#

def addKaTeX (config : Config) : Config :=
  {config with
    extraCss := "/static/katex/katex.min.css" :: config.extraCss,
    extraJs :=
      {filename := "/static/katex/katex.min.js"} ::
      {filename :="/static/math.js"} :: config.extraJs,
    licenseInfo := KaTeXLicense :: config.licenseInfo
  }

def main :=
  manualMain (%doc Journal) (config := config)
where
  config := Config.addSearch <| Config.addKaTeX {
    extraFiles := [("static", "static")],
    extraCss := [
      "/static/colors.css",
      "/static/theme.css",
      "/static/print.css",
      "/static/fonts/source-serif/source-serif-text.css",
      "/static/fonts/source-code-pro/source-code-pro.css",
      "/static/fonts/source-sans/source-sans-3.css"
    ],
    extraJs := [
      -- Print stylesheet improvements
      {filename := "/static/search/fuzzysort.js"},
      {filename := "/static/print.js"},
    ],
    extraHead := #[searchModule],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    emitHtmlMulti := true, -- for proofreading
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/pfaffelh/journl",
    issueLink := some "https://github.com/pfaffelh/journal/issues"
    -- Licenses for the search box
    licenseInfo := []
  }
