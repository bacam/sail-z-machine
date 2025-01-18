register configuration version : range(1,8) = 3

type operand = bits(16)

union exception = {
  Unimplemented : string, // Missing from this model
  StackUnderflow : unit,
  NoSuchLocal : int,
  NestedAbbreviation : unit,
  MalformedInstruction : string,
  LoadAddressOverflow : bits(20),
  InvalidDictionaryEntryLength : int,
  InvalidVariableOperand : operand,
  Unreachable : unit,
}

val unimplemented : forall ('a : Type). string -> 'a
function unimplemented(msg) = throw Unimplemented(msg)

val unreachable : forall ('a : Type). string -> 'a
function unreachable(msg) = throw unreachable(msg)

val warn : string -> unit

val "read_command_plain" : int -> string
