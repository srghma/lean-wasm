import Wasm.Vec
import Wasm.Syntax
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance

namespace Wasm.Dynamics.Allocation

open Wasm.Dynamics
open Numbers

-- Helper to allocate functions
def allocFunc (s : Instance.Store) (f : Instance.Function) : Option (Instance.Store × Address.Function) :=
  let new_len := s.funcs.length + 1
  if h : new_len < Vec.max_length then
    let funcs' := Vec.append s.funcs (Vec.single f) (by
      exact h
    )
    let addr : Address.Function := Unsigned.ofNat s.funcs.length
    .some ({s with funcs := funcs'}, addr)
  else
    .none

-- Helper to allocate tables
def allocTable (s : Instance.Store) (tab : Instance.Table) : Option (Instance.Store × Address.Table) :=
  let new_len := s.tables.length + 1
  if h : new_len < Vec.max_length then
    let tables' := Vec.append s.tables (Vec.single tab) (by
      exact h
    )
    let addr : Address.Table := Unsigned.ofNat s.tables.length
    .some ({s with tables := tables'}, addr)
  else
    .none

-- Helper to allocate memories
def allocMem (s : Instance.Store) (mem : Instance.Memory) : Option (Instance.Store × Address.Memory) :=
  let new_len := s.mems.length + 1
  if h : new_len < Vec.max_length then
    let mems' := Vec.append s.mems (Vec.single mem) (by
      exact h
    )
    let addr : Address.Memory := Unsigned.ofNat s.mems.length
    .some ({s with mems := mems'}, addr)
  else
    .none

-- Helper to allocate globals
def allocGlobal (s : Instance.Store) (g : Instance.Global) : Option (Instance.Store × Address.Global) :=
  let new_len := s.globals.length + 1
  if h : new_len < Vec.max_length then
    let globals' := Vec.append s.globals (Vec.single g) (by
      exact h
    )
    let addr : Address.Global := Unsigned.ofNat s.globals.length
    .some ({s with globals := globals'}, addr)
  else
    .none

-- We can sequentially allocate everything for a module!
def allocModuleFuncs (s : Instance.Store)
                     (m : Instance.Module)
                     (funcs : List Syntax.Module.Function)
                     : Option (Instance.Store × Instance.Module) :=
  match funcs with
  | [] => .some (s, m)
  | f :: fs =>
    -- Look up the type from m.types
    let f_type :=
      if h : f.type.val < m.types.length then
        m.types.get ⟨f.type.val, h⟩
      else
        ⟨Vec.nil, Vec.nil⟩
    let inst_f := Instance.Function.internal ⟨f_type, m, f⟩
    match allocFunc s inst_f with
    | Option.none => Option.none
    | Option.some (s', addr) =>
      let new_len := m.funcaddrs.length + 1
      if h : new_len < Vec.max_length then
        let funcaddrs' := Vec.append m.funcaddrs (Vec.single addr) (by
          exact h
        )
        allocModuleFuncs s' {m with funcaddrs := funcaddrs'} fs
      else
        Option.none

def allocModuleTables (s : Instance.Store)
                      (m : Instance.Module)
                      (tables : List Syntax.Module.Table)
                      : Option (Instance.Store × Instance.Module) :=
  match tables with
  | [] => .some (s, m)
  | t :: ts =>
    let inst_tab : Instance.Table := ⟨t.type, Vec.nil⟩
    match allocTable s inst_tab with
    | Option.none => Option.none
    | Option.some (s', addr) =>
      let new_len := m.tableaddrs.length + 1
      if h : new_len < Vec.max_length then
        let tableaddrs' := Vec.append m.tableaddrs (Vec.single addr) (by
          exact h
        )
        allocModuleTables s' {m with tableaddrs := tableaddrs'} ts
      else
        Option.none

def allocModuleMems (s : Instance.Store)
                    (m : Instance.Module)
                    (mems : List Syntax.Module.Memory)
                    : Option (Instance.Store × Instance.Module) :=
  match mems with
  | [] => .some (s, m)
  | mem :: ms =>
    let inst_mem : Instance.Memory := ⟨mem.type, Vec.nil, by decide⟩
    match allocMem s inst_mem with
    | Option.none => Option.none
    | Option.some (s', addr) =>
      let new_len := m.memaddrs.length + 1
      if h : new_len < Vec.max_length then
        let memaddrs' := Vec.append m.memaddrs (Vec.single addr) (by
          exact h
        )
        allocModuleMems s' {m with memaddrs := memaddrs'} ms
      else
        Option.none

def defaultVal : Value :=
  let v : Unsigned 32 := ⟨0, by decide⟩
  let i : {i : Instr.Dynamic // i = .real (.numeric ((.integer (Syntax.Instr.Numeric.Integer.const v)) : Wasm.Syntax.Instr.Numeric .double))} := ⟨.real (.numeric ((.integer (Syntax.Instr.Numeric.Integer.const v)) : Wasm.Syntax.Instr.Numeric .double)), rfl⟩
  Value.num (Value.Numeric.int_const .double i)

def allocModuleGlobals (s : Instance.Store)
                       (m : Instance.Module)
                       (globals : List Syntax.Module.Global)
                       : Option (Instance.Store × Instance.Module) :=
  match globals with
  | [] => .some (s, m)
  | g :: gs =>
    -- Initialize to some default value or dynamic Value
    let inst_g : Instance.Global := ⟨g.type, defaultVal⟩
    match allocGlobal s inst_g with
    | Option.none => Option.none
    | Option.some (s', addr) =>
      let new_len := m.globaladdrs.length + 1
      if h : new_len < Vec.max_length then
        let globaladdrs' := Vec.append m.globaladdrs (Vec.single addr) (by
          exact h
        )
        allocModuleGlobals s' {m with globaladdrs := globaladdrs'} gs
      else
        Option.none

def allocModule (s : Instance.Store) (mod : Syntax.Module) : Option (Instance.Store × Instance.Module) := do
  let empty_module : Instance.Module := {
    types       := mod.types,
    funcaddrs   := Vec.nil,
    tableaddrs  := Vec.nil,
    memaddrs    := Vec.nil,
    globaladdrs := Vec.nil,
    elemaddrs   := Vec.nil,
    dataaddrs   := Vec.nil,
    exports     := Vec.nil
  }
  let (s₁, m₁) ← allocModuleFuncs s empty_module mod.funcs.list
  let (s₂, m₂) ← allocModuleTables s₁ m₁ mod.tables.list
  let (s₃, m₃) ← allocModuleMems s₂ m₂ mod.mems.list
  let (s₄, m₄) ← allocModuleGlobals s₃ m₃ mod.globals.list
  .some (s₄, m₄)

end Wasm.Dynamics.Allocation
