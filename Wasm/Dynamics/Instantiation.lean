import Wasm.Vec
import Wasm.Syntax
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance
import Wasm.Dynamics.Allocation

namespace Wasm.Dynamics.Instantiation

open Wasm.Dynamics
open Wasm.Dynamics.Allocation

def instantiate (s : Instance.Store)
                (mod : Syntax.Module)
                (imports : List Value.Extern)
                : Option (Instance.Store × Instance.Module) := do
  -- Allocate module
  let (s', m) ← allocModule s mod
  .some (s', m)

end Wasm.Dynamics.Instantiation
