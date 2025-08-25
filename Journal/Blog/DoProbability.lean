import VersoBlog
open Verso Genre Blog

#doc (Page) "Do notation for PMFs" =>

PMFs are a lawful monad. Therefore we can use do-notation here.


Every `do` is a `bind`, and `pure` is a Dirac measure.

The image measure of `ℙ` under some map `f` is `f <$> ℙ := PMF.map f ℙ`.
