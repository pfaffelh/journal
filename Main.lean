import Journal

/-- Entry point for the `journal` executable.

This project previously used `VersoManual` here to emit an HTML manual from the
`Journal` namespace. Verso was dropped as a dependency (see the "delete verso"
commit), so this is now a minimal placeholder that just links against the
`Journal` library and keeps the `journal` executable target building. -/
def main : IO Unit :=
  IO.println "journal: Lean library built (Verso-based HTML manual generation has been removed)."
