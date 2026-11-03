import Lean
namespace TryCommand
open Lean Lean.Elab Command Term

elab "trial" _name:declId ? sig:(declSig) ":=" val:term: command =>
  liftTermElabM
    try
      let ⟨binders, typeStx⟩ := Elab.expandDeclSig sig
      Term.elabBinders binders.getArgs fun _xs => do
        let tp ← elabType typeStx
        discard $ elabTermEnsuringType val tp
        synthesizeSyntheticMVarsNoPostponing
    catch | e => throwError e.toMessageData

end TryCommand
