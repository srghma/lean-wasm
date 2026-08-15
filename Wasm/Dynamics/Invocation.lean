import Wasm.Vec
import Wasm.Syntax
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance
import Wasm.Dynamics.Stack
import Wasm.Dynamics.Context

namespace Wasm.Dynamics.Invocation

open Wasm.Dynamics
open Numbers

def invoke (s : Instance.Store)
           (funcaddr : Address.Function)
           (args : List Value)
           : Option Context.Config := do
  if h : funcaddr.val < s.funcs.length then
    let f := s.funcs.get ⟨funcaddr.val, h⟩
    match f with
    | Instance.Function.internal code =>
      if h_args : args.length < Vec.max_length then
        let frame : Stack.Frame := ⟨⟨args, h_args⟩, code.module⟩
        let instrs : List Instr.Dynamic := code.code.body.fst.map Instr.Dynamic.real
        let thread : Context.Thread := (frame, instrs)
        .some (s, thread)
      else
        .none
    | Instance.Function.host _ =>
      .none
  else
    .none

end Wasm.Dynamics.Invocation
