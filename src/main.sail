function warn(msg : string) -> unit = prerr_bits("Warning: " @ msg, PC)

function main() -> unit = {
  init();
  /*
  foreach (i from 0 to 221) {
    print_int("Object ", i);
    let base_addr = object_properties(add_bits_int(0x0000, i));
    let (_, s) = read_z_coded_string(base_addr + 0x00001);
    print_zscii_string(s);
    print_endline("")
  };
  */
  var instr_pc = PC;
  try {
    while not_bool(quit) do {
      instr_pc = PC;
      //prerr_bits("PC: ", PC);
      let instr = fetch_and_decode();
      execute(instr)
    }
  } catch {
    Unimplemented(s) => prerr_bits("Unimplemented: " @ s @ " at ", instr_pc),
    StackUnderflow() => prerr_bits("Stack unflow at ", instr_pc),
    NoSuchLocal(i) => prerr_bits("No such local " @ dec_str(i) @ " at ", instr_pc),
    NestedAbbreviation() => prerr_bits("Nested abbreviation at PC ", instr_pc),
    MalformedInstruction(s) => prerr_bits("Malformed instruction: " @ s @ " at ", instr_pc),
    LoadAddressOverflow(addr) => prerr_bits(concat_str_bits("Load address overflow: ", addr) @ " at ", instr_pc),
    InvalidDictionaryEntryLength(len) => prerr_bits("Invalid dictionary entry length: " @ dec_str(len) @ " at ", instr_pc),
    InvalidVariableOperand(oper) => prerr_bits(concat_str_bits("Invalid variable operand: ", oper) @ " at ", instr_pc),
    BadAttribute(ob, at) => prerr_bits("Bad attribute, object " @ dec_str(unsigned(ob)) @ ", attribute " @ dec_str(unsigned(at)) @ " at ", instr_pc),
    PropertyNotFound(ob, at) => prerr_bits("Bad property, object " @ dec_str(unsigned(ob)) @ ", attribute " @ dec_str(unsigned(at)) @ " at ", instr_pc),
    WrongPropertySize(ob, at) => prerr_bits("Bad property size, object " @ dec_str(unsigned(ob)) @ ", attribute " @ dec_str(unsigned(at)) @ " at ", instr_pc),
  }
}
