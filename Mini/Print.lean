import Mini.Lang

/-! # Printing a program as C

Every value is a `uint64_t`. Memory is read and written through two helpers that copy eight bytes, which a
compiler turns into one instruction and which, unlike a cast pointer, C lets alias anything. A function is
`static` under its own name with `mini_` in front; one that C is to see gets a second, thin function under
its real name that converts the types at the edge and nothing else. -/

namespace Mini

def Op.c : Op → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .shl => "<<" | .shr => ">>" | .and => "&" | .or => "|" | .xor => "^"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="

def Op.compares : Op → Bool
  | .eq | .ne | .lt | .le => true
  | _ => false

def Expr.c : Expr → String
  | .lit value => s!"{value.toNat}ull"
  | .var name => name
  | .global name => name
  | .item array i => s!"{array}[{i.c}]"
  | .load address => s!"mini_load({address.c})"
  | .part bytes address => s!"mini_load{8 * bytes}({address.c})"
  | .op o a b => if o.compares then s!"(uint64_t)({a.c} {o.c} {b.c})" else s!"({a.c} {o.c} {b.c})"

def pad (depth : Nat) : String := "".pushn ' ' (4 * depth)

mutual
  def Stmt.c (others : List (String × Seen)) (depth : Nat) : Stmt → String
    | .set name value => s!"{pad depth}{name} = {value.c};\n"
    | .setGlobal name value => s!"{pad depth}{name} = {value.c};\n"
    | .setItem array i value => s!"{pad depth}{array}[{i.c}] = {value.c};\n"
    | .store address value => s!"{pad depth}mini_store({address.c}, {value.c});\n"
    | .storePart bytes address value => s!"{pad depth}mini_store{8 * bytes}({address.c}, {value.c});\n"
    | .branch condition yes [] => s!"{pad depth}if ({condition.c}) \{\n{block others (depth + 1) yes}{pad depth}}\n"
    | .branch condition yes no =>
      s!"{pad depth}if ({condition.c}) \{\n{block others (depth + 1) yes}{pad depth}} else \{\n{block others (depth + 1) no}{pad depth}}\n"
    | .loop condition body => s!"{pad depth}while ({condition.c}) \{\n{block others (depth + 1) body}{pad depth}}\n"
    | .call result function arguments =>
      let call := s!"mini_{function}({", ".intercalate (arguments.map Expr.c)})"
      match result with
      | some name => s!"{pad depth}{name} = {call};\n"
      | none => s!"{pad depth}{call};\n"
    | .callOther result function arguments =>
      let types := match others.find? (·.1 == function) with
        | some (_, seen) => seen.parameters
        | none => []
      let passed := ", ".intercalate ((arguments.zip types).map fun (argument, type) => s!"({type}){argument.c}")
      match result with
      | some name => s!"{pad depth}{name} = (uint64_t){function}({passed});\n"
      | none => s!"{pad depth}{function}({passed});\n"
    | .outside result c =>
      match result with
      | some name => s!"{pad depth}{name} = (uint64_t)({c});\n"
      | none => s!"{pad depth}{c};\n"
    | .hide name => s!"{pad depth}__asm__ volatile(\"\" : \"+r\"({name}));\n"
    | .keep address => s!"{pad depth}__asm__ volatile(\"\" : : \"r\"({address.c}) : \"memory\");\n"
    | .stop why => s!"{pad depth}rt_stop({repr why});\n"
    | .give value => s!"{pad depth}return {value.c};\n"
  def block (others : List (String × Seen)) (depth : Nat) : List Stmt → String
    | [] => ""
    | s :: rest => s.c others depth ++ block others depth rest
end

mutual
  /-- The locals a statement assigns, in the order they first appear. -/
  def Stmt.assigned : Stmt → List String
    | .set name _ => [name]
    | .branch _ yes no => assignedIn yes ++ assignedIn no
    | .loop _ body => assignedIn body
    | .call (some name) _ _ => [name]
    | .callOther (some name) _ _ => [name]
    | .outside (some name) _ => [name]
    | _ => []
  def assignedIn : List Stmt → List String
    | [] => []
    | s :: rest => s.assigned ++ assignedIn rest
end

def Function.signature (f : Function) : String :=
  let parameters := if f.parameters.isEmpty then "void" else ", ".intercalate (f.parameters.map (s!"uint64_t {·}"))
  s!"static uint64_t mini_{f.name}({parameters})"

def comment (text : String) : String := if text.isEmpty then "" else s!"/* {text} */\n"

def Function.c (others : List (String × Seen)) (f : Function) : String :=
  let locals := (assignedIn f.body).eraseDups.filter (!f.parameters.contains ·)
  let declared := String.join (locals.map (s!"    uint64_t {·} = 0;\n"))
  -- A function whose last statement gives its result needs nothing after it; any other gives zero.
  let last := match f.body.getLast? with
    | some (.give _) => ""
    | _ => "    return 0;\n"
  let inside := s!"{comment f.about}{f.signature} \{\n{declared}{block others 1 f.body}{last}}\n"
  match f.seen with
  | none => inside
  | some seen =>
    let named := f.parameters.zip seen.parameters
    let parameters := if named.isEmpty then "void" else ", ".intercalate (named.map fun (name, type) => s!"{type} {name}")
    let passed := ", ".intercalate (f.parameters.map (s!"(uint64_t){·}"))
    let call := s!"mini_{f.name}({passed})"
    let body := if seen.result == "void" then s!"    {call};\n" else s!"    return ({seen.result}){call};\n"
    s!"{inside}\n{seen.result} {f.name}({parameters}) \{\n{body}}\n"

def Program.c (p : Program) (source : String) : String :=
  let globals := String.join (p.globals.map (s!"static uint64_t {·};\n"))
  let arrays := String.join (p.arrays.map fun (name, size) => s!"static uint64_t {name}[{size}];\n")
  let declarations := String.join (p.functions.map (s!"{·.signature};\n"))
  let functions := "\n".intercalate (p.functions.map (Function.c p.others))
  let parts := String.join ([8, 16, 32].map fun bits =>
    s!"__attribute__((unused)) static inline uint64_t mini_load{bits}(uint64_t address) \{\n    uint{bits}_t part;\n    __builtin_memcpy(&part, (void const *)address, sizeof part);\n    return part;\n}\n\n__attribute__((unused)) static inline void mini_store{bits}(uint64_t address, uint64_t word) \{\n    uint{bits}_t part = (uint{bits}_t)word;\n    __builtin_memcpy((void *)address, &part, sizeof part);\n}\n\n")
  s!"/*\n{p.about}\n\nThis file is printed from {source} by `mini-print` when the runtime is built. Change that, not this.\n*/\n{p.preamble}\n__attribute__((unused)) static inline uint64_t mini_load(uint64_t address) \{\n    uint64_t word;\n    __builtin_memcpy(&word, (void const *)address, sizeof word);\n    return word;\n}\n\n__attribute__((unused)) static inline void mini_store(uint64_t address, uint64_t word) \{\n    __builtin_memcpy((void *)address, &word, sizeof word);\n}\n\n{parts}{globals}{arrays}\n{declarations}\n{functions}"

end Mini
