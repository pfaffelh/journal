import VersoManual
open Verso Genre Manual

#doc (Manual) "Basics" =>

If `a b : Prop`, and `h : a → b`, then `¬b → ¬ a`. Apparently, this is already implemented in `#check mt`.

example (P Q : Prop) : (¬A → B) ↔ (¬B → A) := by exact not_imp_comm


Hat man
h : P
⊢ : Q
 dann liefert

contrapose! h

h : ¬Q
⊢ : ¬P
