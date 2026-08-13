import Wasm.Vec
import Wasm.Syntax
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value

namespace Wasm.Dynamics.Instance

structure Export where
  name  : Syntax.Value.Name
  value : Value.Extern

structure Module where
  types       : Vec Syntax.Typ.Func
  funcaddrs   : Vec Address.Function
  tableaddrs  : Vec Address.Table
  memaddrs    : Vec Address.Memory
  globaladdrs : Vec Address.Global
  elemaddrs   : Vec Address.Element
  dataaddrs   : Vec Address.Data
  exports     : Vec Instance.Export

structure Function.Internal where
  type : Syntax.Typ.Func
  module : Instance.Module
  code : Syntax.Module.Function

structure Function.Host where
  type : Syntax.Typ.Func
  hostcode : Unit         -- todo add

inductive Function
| internal : Function.Internal → Function
| host     : Function.Host → Function

structure Table where
  type : Syntax.Typ.Table
  elem : Vec Value.Reference

def Table.grow (tab : Table) (n : Nat) (v : Value.Reference) : Option Table :=
  let new_len := tab.elem.length + n
  if h : new_len < Vec.max_length then
    let max_ok : Bool :=
      match tab.type.fst.max with
      | Option.none => true
      | Option.some max_val => new_len ≤ max_val.val
    if max_ok then
      have h_len : (tab.elem.list ++ List.replicate n v).length = new_len := by
        simp [new_len]
      .some ⟨tab.type, ⟨tab.elem.list ++ List.replicate n v, by rw [h_len]; exact h⟩⟩
    else
      .none
  else
    .none

structure Memory where
  type : Syntax.Typ.Mem
  data : Vec Syntax.Value.Byte
  pagesize : data.length % 65536 = 0
  -- todo more invariants

-- in internal representations, the least significant byte is at the end
def Memory.read (mem : Memory)
                (pos len : Nat)
                : List Syntax.Value.Byte :=
  mem.data.list.drop pos |>.take len |>.reverse

def Memory.write (mem : Memory)
                 (bytes : List Syntax.Value.Byte)
                 (pos : Nat)
                 : Memory :=
  match bytes with
  | [] => mem
  | b :: bs =>
    if h : pos < mem.data.length then
      let mem' : Memory := ⟨mem.type, mem.data.set ⟨pos, h⟩ b, by
        have h_len : (mem.data.set ⟨pos, h⟩ b).length = mem.data.length := by
          unfold Vec.length Vec.set Vec.list
          simp only [List.length_set]
        have h_pagesize := mem.pagesize
        rw [h_len]
        exact h_pagesize
      ⟩
      Memory.write mem' bs (pos + 1)
    else
      mem


structure Global where
  type  : Syntax.Typ.Global
  value : Value

structure Element where
  type : Syntax.Typ.Ref
  elem : Vec Value.Reference

structure Data where
  data : Vec Syntax.Value.Byte


structure Store where
  funcs   : Vec Function
  tables  : Vec Table
  mems    : Vec Memory
  globals : Vec Global
  elems   : Vec Element
  datas   : Vec Data
